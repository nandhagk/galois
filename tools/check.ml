open Core

module Audit = struct
  type t =
    | Hygiene
    | Layout
    | Claims
  [@@deriving enumerate, sexp_of, string ~capitalize:"kebab-case"]
end

module Jobs = struct
  type t =
    | One
    | Two
  [@@deriving sexp_of]

  let default = Two
  let variable = "GALOIS_CHECK_JOBS"

  let parse = function
    | None -> Ok default
    | Some "1" -> Ok One
    | Some "2" -> Ok Two
    | Some value ->
      Or_error.error_s
        [%message "invalid claims worker setting" (variable : string) (value : string)]
  ;;
end

module Cancellation = struct
  module Stage = struct
    type t =
      | Workspace
      | Descriptor
      | Process
      | Script
      | Transcript
    [@@deriving sexp_of]
  end

  (* Signal handlers and workers share this flag while a claims audit is active. *)
  let requested = Atomic.make false

  let fail ~stage = function
    | Ok _ as result -> result
    | Error error ->
      Atomic.set requested true;
      Or_error.tag_s
        (Error error)
        ~tag:[%message "fatal claims orchestration failure" (stage : Stage.t)]
  ;;
end

module Diagnostic = struct
  type t =
    { file : Filename.t
    ; line : int
    ; claim : string option
    ; problem : string
    }
  [@@deriving sexp_of]

  let error ~file ~line ?claim problem =
    Or_error.error_s [%sexp ({ file; line; claim; problem } : t)]
  ;;
end

module Lex = struct
  module Token = struct
    type t =
      { text : string
      ; line : int
      }
    [@@deriving sexp_of]
  end

  module Sentence = struct
    type t =
      { tokens : Token.t list
      ; line : int
      }
    [@@deriving sexp_of]
  end

  let is_identifier c =
    Char.is_alphanum c || Char.equal c '_' || Char.equal c '\'' || Char.to_int c >= 128
  ;;

  let text ({ text; _ } : Token.t) = text

  (* Accumulators keep lexing linear; comments and strings never contribute identifier tokens. *)
  let scan ~file source =
    let length = String.length source in
    let at i c = i < length && Char.equal source.[i] c in
    let pair i a b = at i a && at (i + 1) b in
    let rec identifier_end i =
      if i < length && is_identifier source.[i] then identifier_end (i + 1) else i
    in
    let rec comment i line depth =
      if i >= length
      then Diagnostic.error ~file ~line "unterminated Rocq comment"
      else if pair i '(' '*'
      then comment (i + 2) line (depth + 1)
      else if pair i '*' ')'
      then if depth = 1 then Ok (i + 2, line) else comment (i + 2) line (depth - 1)
      else if at i '"'
      then (
        let%bind.Or_error next, next_line = quoted (i + 1) line in
        comment next next_line depth)
      else comment (i + 1) (line + if at i '\n' then 1 else 0) depth
    and quoted i line =
      if i >= length
      then Diagnostic.error ~file ~line "unterminated Rocq string"
      else if pair i '"' '"'
      then quoted (i + 2) line
      else if at i '"'
      then Ok (i + 1, line)
      else quoted (i + 1) (line + if at i '\n' then 1 else 0)
    in
    let rec loop i line tokens sentences =
      if i >= length
      then
        if List.is_empty tokens
        then Ok (List.rev sentences)
        else Diagnostic.error ~file ~line "incomplete Rocq sentence (missing final period)"
      else if pair i '(' '*'
      then (
        let%bind.Or_error i, line = comment (i + 2) line 1 in
        loop i line tokens sentences)
      else if at i '"'
      then (
        let%bind.Or_error next, next_line = quoted (i + 1) line in
        loop next next_line (({ text = "<string>"; line } : Token.t) :: tokens) sentences)
      else if Char.is_whitespace source.[i]
      then loop (i + 1) (line + if at i '\n' then 1 else 0) tokens sentences
      else if
        at i '.' && (i + 1 = length || Char.is_whitespace source.[i + 1] || pair (i + 1) '(' '*')
      then (
        let tokens = List.rev tokens in
        let sentence_line =
          match tokens with
          | [] -> line
          | first :: _ -> first.line
        in
        loop (i + 1) line [] (({ tokens; line = sentence_line } : Sentence.t) :: sentences))
      else (
        let next = if is_identifier source.[i] then identifier_end (i + 1) else i + 1 in
        let token = ({ text = String.sub source ~pos:i ~len:(next - i); line } : Token.t) in
        loop next line (token :: tokens) sentences)
    in
    loop 0 1 [] []
  ;;

  let rec head = function
    | "#" :: "[" :: rest -> attributes rest
    | ("Local" | "Global" | "Polymorphic" | "Monomorphic" | "Program" | "Time" | "Fail" | "Succeed")
      :: rest -> head rest
    | "Timeout" :: _seconds :: rest -> head rest
    | "Redirect" :: "<string>" :: rest -> head rest
    | tokens -> tokens

  and attributes = function
    | [] -> []
    | "]" :: rest -> head rest
    | _ :: rest -> attributes rest
  ;;

  let words ({ tokens; _ } : Sentence.t) = List.map tokens ~f:text
end

module Source = struct
  module Generation = struct
    type t =
      | New
      | Legacy
    [@@deriving enumerate, equal]
  end

  module Root = struct
    type t =
      | Theories
      | Examples
      | Tests
      | Legacy_theories [@rename "legacy/theories"]
      | Legacy_examples [@rename "legacy/examples"]
      | Legacy_tests [@rename "legacy/tests"]
    [@@deriving enumerate, equal, string ~capitalize:"kebab-case", sexp_of]

    let generation : t -> Generation.t = function
      | Theories | Examples | Tests -> New
      | Legacy_theories | Legacy_examples | Legacy_tests -> Legacy
    ;;
  end

  type t =
    { file : Filename.t
    ; root : Root.t
    ; relative : Filename.t
    ; package : string
    ; source : string
    ; sentences : Lex.Sentence.t list
    }
  [@@deriving sexp_of]

  let extension = ".v"
  let float_package = "Float"
  let rewrite_package = "Rewrite"
  let examples_package = "Examples"

  let legacy_packages =
    String.Set.of_list
      [ "Collections"
      ; "Order"
      ; "Graph"
      ; "Fixpoint"
      ; "Rules"
      ; rewrite_package
      ; "Bits"
      ; "Domains"
      ; "Views"
      ; "Analyses"
      ; float_package
      ]
  ;;

  let packages =
    String.Set.of_list
      [ "Cost"
      ; "Base"
      ; "Lattice"
      ; "Bits"
      ; "Graph"
      ; "Fixpoint"
      ; "Domains"
      ; "Program"
      ; "Datalog"
      ; "Egraph"
      ; "Framework"
      ; "Next"
      ; "Analyses"
      ; float_package
      ]
  ;;

  let test_packages = Set.add packages examples_package

  let analysis_families =
    String.Set.of_list [ "Dataflow"; "Values"; "Ssa"; "Equality"; "Loops"; "Calls"; "Memory" ]
  ;;

  let legacy_example_directories = String.Set.of_list [ "While"; "Ssa" ]

  let example_directories =
    Set.union
      legacy_example_directories
      (String.Set.of_list [ "Tutorial"; "SsaValues"; "SsaMemory"; "SsaLoops"; "SsaFloat" ])
  ;;

  let new_package = function
    | [ "Analyses"; family; _ ] when Set.mem analysis_families family -> "Analyses"
    | [ "Domains"; "Memory"; _ ] -> "Domains"
    | [ "Next"; _extension; _ ] -> "Next"
    | ("Analyses" | "Next") :: _ -> ""
    | [ package; _ ] -> package
    | _ -> ""
  ;;

  let test_package = function
    | [ "Examples"; directory; _ ] when Set.mem example_directories directory -> examples_package
    | "Examples" :: _ -> ""
    | [ package; _ ] -> package
    | parts -> new_package parts
  ;;

  let package ~root relative =
    match root, String.split relative ~on:'/' with
    | Root.Examples, [ directory; _ ] when Set.mem example_directories directory -> examples_package
    | Root.Legacy_examples, directory :: _ :: _ when Set.mem legacy_example_directories directory ->
      examples_package
    | Root.Theories, parts -> new_package parts
    | Root.Tests, "legacy" :: parts -> test_package parts
    | Root.Tests, parts -> test_package parts
    | (Root.Legacy_theories | Root.Legacy_tests), package :: _ :: _ -> package
    | (Root.Examples | Root.Legacy_examples | Root.Legacy_theories | Root.Legacy_tests), _ -> ""
  ;;

  let load ~root ~file ~relative ~package =
    let%bind.Or_error source = Or_error.try_with (fun () -> In_channel.read_all file) in
    let%map.Or_error sentences = Lex.scan ~file source in
    ({ file; root; relative; package; source; sentences } : t)
  ;;

  let rec files directory =
    let%bind.Or_error entries = Or_error.try_with (fun () -> Sys_unix.ls_dir directory) in
    List.map entries ~f:(fun entry ->
      let file = Filename.concat directory entry in
      let%bind.Or_error ({ st_kind; _ } : Core_unix.stats) =
        Or_error.try_with (fun () -> Core_unix.lstat file)
      in
      match st_kind with
      | S_DIR -> files file
      | S_REG -> Ok (if String.is_suffix file ~suffix:extension then [ file ] else [])
      | S_LNK -> Diagnostic.error ~file ~line:1 "symlinks are not authored source paths"
      | S_CHR | S_BLK | S_FIFO | S_SOCK ->
        Diagnostic.error ~file ~line:1 "unexpected source file kind")
    |> Or_error.combine_errors
    |> Or_error.map ~f:List.concat
  ;;

  let discover repository =
    List.map Root.all ~f:(fun root ->
      let directory = Filename.concat repository (Root.to_string root) in
      let%bind.Or_error paths = files directory in
      List.map (List.sort paths ~compare:String.compare) ~f:(fun file ->
        let relative = String.chop_prefix_exn file ~prefix:[%string "%{directory}/"] in
        let package = package ~root relative in
        load ~root ~file ~relative ~package)
      |> Or_error.combine_errors)
    |> Or_error.combine_errors
    |> Or_error.map ~f:List.concat
  ;;

  let is_float_package ({ root; package; _ } : t) =
    (Root.equal root Theories || Root.equal root Legacy_theories)
    && String.equal package float_package
  ;;

  let is_legacy_comparison ({ root; relative; _ } : t) =
    Root.equal root Tests && String.is_prefix relative ~prefix:"legacy/"
  ;;

  let is_production ({ root; _ } : t) =
    match root with
    | Theories | Examples | Legacy_theories | Legacy_examples -> true
    | Tests | Legacy_tests -> false
  ;;
end

module Scope = struct
  type t =
    | Section of string
    | Module of string
    | Signature of string

  module Assignment = struct
    type t =
      | Body
      | Constraint
  end

  let assignment depth words =
    (* A module-type refinement contains := without closing the module's declaration. *)
    let rec loop depth (state : Assignment.t) = function
      | "(" :: rest -> loop (depth + 1) state rest
      | ")" :: rest -> loop (depth - 1) state rest
      | "with" :: rest when depth = 0 -> loop depth Constraint rest
      | ":" :: "=" :: rest when depth = 0 ->
        (match state with
         | Constraint -> loop depth Body rest
         | Body -> true)
      | _ :: rest -> loop depth state rest
      | [] -> false
    in
    loop depth Body words
  ;;

  let advance ~file ~line scopes = function
    | "Section" :: name :: _ -> Ok (Section name :: scopes)
    | "Module" :: "Type" :: name :: rest ->
      Ok (if assignment 0 rest then scopes else Signature name :: scopes)
    | "Module" :: ("Import" | "Export") :: name :: rest | "Module" :: name :: rest ->
      Ok (if assignment 0 rest then scopes else Module name :: scopes)
    | "End" :: name :: _ ->
      (match scopes with
       | (Section opened | Module opened | Signature opened) :: rest when String.equal opened name
         -> Ok rest
       | (Section _ | Module _ | Signature _) :: _ | [] ->
         Diagnostic.error ~file ~line "unbalanced Module/Section scope during source audit")
    | _ -> Ok scopes
  ;;

  let inside_section scopes =
    List.exists scopes ~f:(function
      | Section _ -> true
      | Module _ | Signature _ -> false)
  ;;

  let inside_signature scopes =
    List.exists scopes ~f:(function
      | Signature _ -> true
      | Section _ | Module _ -> false)
  ;;
end

module Import_policy = struct
  type t =
    { known : String.Set.t
    ; forbidden : String.Set.t
    }

  let empty = ({ known = String.Set.empty; forbidden = String.Set.empty } : t)
  let stdlib = "Stdlib"
  let stdlib_prefix = [%string "%{stdlib}."]

  let paths tokens =
    let identifier word =
      (not (String.is_empty word)) && String.for_all word ~f:Lex.is_identifier
    in
    let rec loop current paths = function
      | "(" :: rest ->
        let%bind.Or_error rest = mask 1 rest in
        loop current paths rest
      | "." :: name :: rest when identifier name && not (List.is_empty current) ->
        loop (name :: current) paths rest
      | name :: rest when identifier name ->
        let paths =
          if List.is_empty current
          then paths
          else String.concat ~sep:"." (List.rev current) :: paths
        in
        loop [ name ] paths rest
      | [] ->
        Ok
          (List.rev
             (if List.is_empty current
              then paths
              else String.concat ~sep:"." (List.rev current) :: paths))
      | tokens -> Or_error.error_s [%message "unrecognized Require path" (tokens : string list)]
    and mask depth = function
      | "(" :: rest -> mask (depth + 1) rest
      | ")" :: rest -> if depth = 1 then Ok rest else mask (depth - 1) rest
      | _ :: rest -> mask depth rest
      | [] -> Or_error.error_string "unclosed Require import mask"
    in
    loop [] [] tokens
  ;;

  let modules = function
    | ("Import" | "Export") :: rest -> paths rest
    | words -> paths words
  ;;

  let imports = function
    | "From" :: rest ->
      let prefix, require =
        List.split_while rest ~f:(fun word -> not (String.equal word "Require"))
      in
      let%bind.Or_error prefix = paths prefix in
      (match prefix, require with
       | [ prefix ], "Require" :: rest ->
         let%map.Or_error names = modules rest in
         List.map names ~f:(fun name -> [%string "%{prefix}.%{name}"])
       | _ -> Or_error.error_string "unrecognized From/Require command")
    | "Require" :: rest -> modules rest
    | _ -> Ok []
  ;;

  module Node = struct
    type t =
      { name : string
      ; imports : string list
      ; postulates : String.Set.t
      }
  end

  module Scan = struct
    type t =
      { scopes : Scope.t list
      ; imports : string list
      ; postulates : String.Set.t
      }
  end

  let postulate scopes words =
    (* Abstract signature fields describe module arguments, rather than global axioms. *)
    (not (Scope.inside_signature scopes))
    &&
    match words with
    | ( "Axiom"
      | "Axioms"
      | "Parameter"
      | "Parameters"
      | "Conjecture"
      | "Conjectures"
      | "Admitted"
      | "Admit" )
      :: _
    | "Declare" :: ("Module" | "Instance") :: _ -> true
    | ("Variable" | "Variables" | "Hypothesis" | "Hypotheses" | "Context") :: _ ->
      not (Scope.inside_section scopes)
    | _ -> false
  ;;

  let node ~directory file =
    let relative =
      String.chop_prefix_exn file ~prefix:[%string "%{directory}/"] |> Filename.chop_extension
    in
    let name = String.concat ~sep:"." (stdlib :: String.split relative ~on:'/') in
    let%bind.Or_error source = Or_error.try_with (fun () -> In_channel.read_all file) in
    let%bind.Or_error sentences = Lex.scan ~file source in
    let%bind.Or_error ({ scopes; imports; postulates } : Scan.t) =
      List.fold_result
        sentences
        ~init:({ scopes = []; imports = []; postulates = String.Set.empty } : Scan.t)
        ~f:
          (fun
            ({ scopes; imports = previous; postulates } : Scan.t)
            ({ line; _ } as sentence : Lex.Sentence.t) ->
          let words = Lex.head (Lex.words sentence) in
          let%bind.Or_error imported = imports words in
          let postulates = if postulate scopes words then Set.add postulates name else postulates in
          let%map.Or_error scopes = Scope.advance ~file ~line scopes words in
          ({ scopes; imports = List.rev_append imported previous; postulates } : Scan.t))
    in
    if List.is_empty scopes
    then Ok ({ name; imports; postulates } : Node.t)
    else Diagnostic.error ~file ~line:1 "unclosed scope while indexing pinned Stdlib"
  ;;

  let suffixes name =
    let rec loop = function
      | [] -> []
      | _ :: rest as parts -> String.concat ~sep:"." parts :: loop rest
    in
    loop (String.split name ~on:'.')
  ;;

  let index nodes =
    let known = List.map nodes ~f:(fun ({ name; _ } : Node.t) -> name) |> String.Set.of_list in
    let aliases =
      Set.to_list known
      |> List.concat_map ~f:(fun name ->
        let relative = String.chop_prefix_exn name ~prefix:stdlib_prefix in
        let paths =
          suffixes relative
          |> List.concat_map ~f:(fun suffix -> [ suffix; [%string "%{stdlib_prefix}%{suffix}"] ])
        in
        List.map paths ~f:(fun suffix -> suffix, name))
      |> String.Map.of_alist_multi
    in
    let reverse =
      List.fold nodes ~init:String.Map.empty ~f:(fun reverse ({ name; imports; _ } : Node.t) ->
        List.concat_map imports ~f:(fun imported ->
          Map.find aliases imported |> Option.value ~default:[])
        |> List.fold ~init:reverse ~f:(fun reverse dependency ->
          Map.update reverse dependency ~f:(fun previous ->
            Set.add (Option.value previous ~default:String.Set.empty) name)))
    in
    let roots =
      List.fold nodes ~init:String.Set.empty ~f:(fun roots ({ postulates; _ } : Node.t) ->
        Set.union roots postulates)
    in
    let rec propagate pending seen =
      match pending with
      | [] -> seen
      | name :: rest when Set.mem seen name -> propagate rest seen
      | name :: rest ->
        let clients =
          Map.find reverse name |> Option.value ~default:String.Set.empty |> Set.to_list
        in
        propagate (List.rev_append clients rest) (Set.add seen name)
    in
    let forbidden = propagate (Set.to_list roots) String.Set.empty in
    let known =
      Map.key_set aliases |> Set.filter ~f:(fun name -> String.is_prefix name ~prefix:stdlib_prefix)
    in
    let forbidden =
      Map.fold aliases ~init:String.Set.empty ~f:(fun ~key ~data names ->
        if List.exists data ~f:(Set.mem forbidden) then Set.add names key else names)
    in
    ({ known; forbidden } : t)
  ;;

  let load () =
    let directory =
      Sys.getenv "ROCQPATH"
      |> Option.value ~default:""
      |> String.split ~on:':'
      |> List.find_map ~f:(fun root ->
        let directory = Filename.concat root stdlib in
        match Sys_unix.is_directory directory with
        | `Yes -> Some directory
        | `No | `Unknown -> None)
    in
    match directory with
    | None -> Or_error.error_string "pinned Stdlib source directory is unavailable through ROCQPATH"
    | Some directory ->
      let%bind.Or_error files = Source.files directory in
      let%map.Or_error nodes = List.map files ~f:(node ~directory) |> Or_error.combine_errors in
      index nodes
  ;;

  let for_sources sources =
    let needs_index sentence =
      match Lex.head (Lex.words sentence) with
      | "From" :: origin :: _ -> String.equal origin stdlib
      | "Require" :: rest -> List.mem rest stdlib ~equal:String.equal
      | _ -> false
    in
    if
      List.exists sources ~f:(fun ({ sentences; _ } : Source.t) ->
        List.exists sentences ~f:needs_index)
    then load ()
    else Ok empty
  ;;
end

module Float_boundary = struct
  let roots = [ "Galois.Float"; "GaloisLegacy.Float" ]

  let is_import name =
    List.exists roots ~f:(fun root ->
      String.equal name root || String.is_prefix name ~prefix:[%string "%{root}."])
  ;;

  let imports_float ({ sentences; _ } : Source.t) =
    let%map.Or_error imports =
      List.map sentences ~f:(fun sentence ->
        let words = Lex.words sentence in
        let controls =
          List.take_while words ~f:(fun word ->
            not (String.equal word "From" || String.equal word "Require"))
        in
        (* Test-control wrappers roll back commands, so they cannot establish a dependency. *)
        if
          List.exists controls ~f:(fun word ->
            String.equal word "Fail" || String.equal word "Succeed")
        then Ok []
        else Import_policy.imports (Lex.head words))
      |> Or_error.combine_errors
    in
    List.exists imports ~f:(List.exists ~f:is_import)
  ;;
end

module Cost_lint = struct
  module Region = struct
    type t =
      | Computation
      | Proof
  end

  let cost_package = "Cost"
  let suffix = "_c"
  let qualified name = [ cost_package; "."; name ]

  let rec contains words pattern =
    List.is_prefix words ~prefix:pattern ~equal:String.equal
    ||
    match words with
    | [] -> false
    | _ :: rest -> contains rest pattern
  ;;

  (* Only a top-level assignment separates a declaration's type from its body. *)
  let split_body words =
    let rec loop depth header = function
      | ":" :: "=" :: body when depth = 0 -> List.rev header, Some body
      | (("(" | "{" | "[") as word) :: rest -> loop (depth + 1) (word :: header) rest
      | ((")" | "}" | "]") as word) :: rest -> loop (depth - 1) (word :: header) rest
      | word :: rest -> loop depth (word :: header) rest
      | [] -> List.rev header, None
    in
    loop 0 [] words
  ;;

  let declaration = function
    | ("Definition" | "Let" | "Fixpoint" | "CoFixpoint") :: name :: rest -> Some (name, rest)
    | _ -> None
  ;;

  (* Balanced groups and top-level separators are the supported lexical boundary.
     This is not Rocq elaboration. In particular, imported aliases and inferred types
     still need source review and cost theorems. *)
  let take_until ~stops words =
    let rec loop depth taken = function
      | word :: _ as rest when depth = 0 && List.mem stops word ~equal:String.equal ->
        List.rev taken, rest
      | (("(" | "{" | "[") as word) :: rest -> loop (depth + 1) (word :: taken) rest
      | ((")" | "}" | "]") as word) :: rest -> loop (depth - 1) (word :: taken) rest
      | word :: rest -> loop depth (word :: taken) rest
      | [] -> List.rev taken, []
    in
    loop 0 [] words
  ;;

  let rec unparenthesize = function
    | "(" :: rest as words ->
      (match take_until ~stops:[ ")" ] rest with
       | inside, [ ")" ] -> unparenthesize inside
       | _ -> words)
    | words -> words
  ;;

  let rec codomain words =
    let words = unparenthesize words in
    match take_until ~stops:[ "-" ] words with
    | _, "-" :: ">" :: rest -> codomain rest
    | _ -> words
  ;;

  (* Recognize explicit arrow families ending in Prop, including parentheses.
     A Prop-valued parameter or arrow domain does not classify the declaration. *)
  let is_prop header =
    match take_until ~stops:[ ":" ] header with
    | _, ":" :: result -> [%equal: string list] (codomain result) [ "Prop" ]
    | _ -> false
  ;;

  module Binding = struct
    type t =
      | Unknown
      | Value
      | Cost_record
  end

  let binding_type words : Binding.t =
    let words = unparenthesize words in
    match take_until ~stops:[ "-" ] words with
    | _, "-" :: ">" :: _ -> Unknown
    | _ ->
      (match words with
       | "Cost" :: "." :: "t" :: _ -> Cost_record
       | _ -> Value)
  ;;

  let identifier word = not (String.is_empty word) && String.for_all word ~f:Lex.is_identifier

  let bind_names env ~(kind : Binding.t) names =
    List.fold names ~init:env ~f:(fun env name ->
      if identifier name then Map.set env ~key:name ~data:kind else env)
  ;;

  module Binder = struct
    type t =
      { names : string list
      ; annotation : string list
      }
  end

  module Binder_sequence = struct
    module Form = struct
      type t =
        | Declaration
        | Lambda
    end

    type t =
      { groups : Binder.t list
      ; result : string list
      }
  end

  let binder_group words =
    let names, tail = take_until ~stops:[ ":" ] words in
    let annotation =
      match tail with
      | ":" :: typ -> typ
      | _ -> []
    in
    ({ names; annotation } : Binder.t)
  ;;

  (* A declaration's bare parameters do not own its return annotation.
     A lambda's trailing bare binder group does own its annotation. *)
  let binder_sequence ~form words =
    let finish groups result =
      ({ groups = List.rev groups; result } : Binder_sequence.t)
    in
    let rec loop groups = function
      | ("(" | "{") :: rest ->
        let group, tail = take_until ~stops:[ ")"; "}" ] rest in
        (match tail with
         | _close :: rest -> loop (binder_group group :: groups) rest
         | [] -> finish (binder_group group :: groups) [])
      | ":" :: result -> finish groups result
      | [] -> finish groups []
      | words ->
        let names, tail = take_until ~stops:[ "("; "{"; ":" ] words in
        (match (form : Binder_sequence.Form.t), tail with
         | Lambda, ":" :: annotation ->
           finish (({ names; annotation } : Binder.t) :: groups) []
         | (Declaration | Lambda), _ ->
           loop (({ names; annotation = [] } : Binder.t) :: groups) tail)
    in
    loop [] words
  ;;

  let namespace scopes =
    List.rev scopes
    |> List.filter_map ~f:(function
      | Scope.Module name | Scope.Signature name -> Some name
      | Scope.Section _ -> None)
  ;;

  let name_at scopes name = String.concat ~sep:"." (namespace scopes @ [ name ])

  module Twins = struct
    type t =
      { declared : String.Set.t
      ; plain : String.Set.t
      ; literals : String.Set.t
      }
  end

  (* Only closed literal data gets a free constant reference at an argument boundary.
     Explicit applications, including explicit type arguments, remain checked.
     No call, projection, traversal or lambda qualifies by having zero parameters. *)
  let literal header body =
    let rec implicit_parameters = function
      | "{" :: rest ->
        (match take_until ~stops:[ "}" ] rest with
         | _, "}" :: rest -> implicit_parameters rest
         | _ -> false)
      | ":" :: _ | [] -> true
      | _ -> false
    in
    implicit_parameters header
    &&
    match unparenthesize body with
    | [ "["; "]" ] | [ "true" ] | [ "false" ] | [ "tt" ] | [ "None" ] -> true
    | [ number ] -> String.for_all number ~f:Char.is_digit
    | _ -> false
  ;;

  let plain_names ~file sentences =
    let%map.Or_error _, declared, literals =
      List.fold_result
        sentences
        ~init:([], String.Set.empty, String.Set.empty)
        ~f:(fun (scopes, declared, literals) (sentence : Lex.Sentence.t) ->
          let words = Lex.head (Lex.words sentence) in
          let declared, literals =
            match declaration words with
            | Some (name, rest) ->
              let name = name_at scopes name in
              let header, body = split_body rest in
              ( Set.add declared name
              , if Option.exists body ~f:(literal header)
                then Set.add literals name
                else literals )
            | None -> declared, literals
          in
          let%map.Or_error scopes = Scope.advance ~file ~line:sentence.line scopes words in
          scopes, declared, literals)
    in
    ({ declared
     ; plain = Set.filter declared ~f:(fun name -> Set.mem declared [%string "%{name}%{suffix}"])
     ; literals
     }
     : Twins.t)
  ;;

  let rec reference = function
    | name :: "." :: next :: rest when identifier name && identifier next ->
      let tail, rest = reference (next :: rest) in
      [%string "%{name}.%{tail}"], rest
    | name :: rest -> name, rest
    | [] -> "", []
  ;;

  let resolve (twins : Twins.t) ~visible ~scopes name =
    let find declared =
      let rec loop path =
        let candidate = String.concat ~sep:"." (path @ [ name ]) in
        if Set.mem declared candidate
        then Some candidate
        else (
          match List.rev path with
          | _ :: rest -> loop (List.rev rest)
          | [] -> None)
      in
      loop (namespace scopes)
    in
    (* Future twins remain discoverable, but future declarations cannot mask
       a name already visible in an enclosing namespace. *)
    match find visible with
    | Some _ as resolved -> resolved
    | None -> find twins.declared
  ;;

  (* Qualified constructor paths introduce no local bindings. Bare identifiers
     in these simple branch patterns are treated as variables without elaboration. *)
  let pattern_bindings env words =
    let rec loop env = function
      | name :: _ as words when identifier name ->
        let name, rest = reference words in
        let env =
          if String.contains name '.'
          then env
          else bind_names env ~kind:Value [ name ]
        in
        loop env rest
      | _ :: rest -> loop env rest
      | [] -> env
    in
    loop env words
  ;;

  module Inspection = struct
    type t =
      { issue : string option
      ; env : Binding.t String.Map.t
      }
  end

  module Scan = struct
    type t =
      { region : Region.t
      ; scopes : Scope.t list
      ; visible : String.Set.t
      }
  end

  let visible_declaration visible ~scopes words =
    match declaration words with
    | Some (name, _) -> Set.add visible (name_at scopes name)
    | None -> visible
  ;;

  let record_head env words =
    let rec head = function
      | "(" :: rest -> head rest
      | words -> words
    in
    let name, _ = reference (head words) in
    match Map.find env name with
    | Some Binding.Cost_record -> true
    | Some Value -> false
    | Some Unknown | None ->
      String.is_suffix name ~suffix
      || List.exists
           [ "ret"; "bind"; "map"; "lift"; "refine"; "tick"; "step"; "tick_bits"; "mk" ]
           ~f:(fun primitive -> String.equal [%string "Cost.%{primitive}"] name)
  ;;

  let plain_reference twins ~visible ~scopes ~env ~name rest =
    if Map.mem env name
    then None
    else
      Option.bind (resolve twins ~visible ~scopes name) ~f:(fun resolved ->
        let ({ plain; literals; _ } : Twins.t) = twins in
        let ends_argument =
          match rest with
          | [] | (")" | "}" | "]" | "," | ";" | "|" | "in" | "end") :: _ -> true
          | _ -> false
        in
        if Set.mem plain resolved && not (Set.mem literals resolved && ends_argument)
        then Some [%string "plain function in costed body: %{name}"]
        else None)
  ;;

  (* The recursive walk restores the environment at groups and match branches.
     let* binds a value, while an ordinary let can alias a cost record.
     Simple lets and bare/grouped binder sequences are supported.
     In branch patterns, qualified paths are constructors and bare identifiers are variables.
     Pattern lets receive no shadowing exemption. Imported module aliases are not resolved.
     The twin index contains this source's declarations. Imports are not elaborated. *)
  let scoped_problem twins ~visible ~scopes ~costed ~env ~sequence words =
    let rec walk env ~stops words =
      match words with
      | [] -> None, []
      | word :: _ when List.mem stops word ~equal:String.equal -> None, words
      | ("(" | "{" | "[") :: rest ->
        let issue, tail = walk env ~stops:[ ")"; "}"; "]" ] rest in
        resume env ~stops issue tail
      | "let" :: rest -> local env ~stops rest
      | "fun" :: rest ->
        let header, tail = take_until ~stops:[ "=" ] rest in
        (match tail with
         | "=" :: ">" :: rest ->
           let issue, env = annotations env (binder_sequence ~form:Lambda header) in
           (match issue with
            | Some _ -> issue, rest
            | None -> walk env ~stops rest)
         | _ -> walk env ~stops rest)
      | "match" :: rest ->
        if record_head env rest
        then Some "computational match on Cost.t outside Cost", []
        else (
          let issue, tail = walk env ~stops:[ "with" ] rest in
          match issue, tail with
          | None, "with" :: rest -> branches env ~stops rest
          | _ -> issue, tail)
      | name :: _ when identifier name ->
        let name, rest = reference words in
        let issue =
          if costed then plain_reference twins ~visible ~scopes ~env ~name rest else None
        in
        (match issue with
         | Some _ -> issue, rest
         | None -> walk env ~stops rest)
      | _ :: rest -> walk env ~stops rest
    and resume env ~stops issue = function
      | _close :: rest when Option.is_none issue -> walk env ~stops rest
      | tail -> issue, tail
    and local env ~stops words =
      let monadic, words =
        match words with
        | "*" :: rest -> true, rest
        | rest -> false, rest
      in
      let header, rhs = split_body words in
      match unparenthesize header, rhs with
      | name :: annotation, Some rhs
        when List.is_empty annotation
             || List.is_prefix annotation ~prefix:[ ":" ] ~equal:String.equal ->
        let kind : Binding.t =
          if monadic
          then Value
          else (
            match annotation with
            | ":" :: typ -> binding_type typ
            | _ -> if record_head env rhs then Cost_record else Value)
        in
        let issue, _ = walk env ~stops:[] annotation in
        let issue, tail =
          match issue with
          | Some _ -> issue, rhs
          | None -> walk env ~stops:[ "in" ] rhs
        in
        (match issue, tail with
         | None, "in" :: rest -> walk (Map.set env ~key:name ~data:kind) ~stops rest
         | _ -> issue, tail)
      | _ ->
        (* Unsupported let patterns receive no shadowing exemption. *)
        walk env ~stops words
    and branches env ~stops words =
      let pattern, tail = take_until ~stops:[ "=" ] words in
      match tail with
      | "=" :: ">" :: rest ->
        let branch_env = pattern_bindings env pattern in
        let issue, tail = walk branch_env ~stops:[ "|"; "end" ] rest in
        (match issue, tail with
         | None, "|" :: rest -> branches env ~stops rest
         | None, "end" :: rest -> walk env ~stops rest
         | _ -> issue, tail)
      | _ -> walk env ~stops words
    and annotations env ({ groups; result } : Binder_sequence.t) =
      match groups with
      | ({ names; annotation } : Binder.t) :: groups ->
        let issue, _ = walk env ~stops:[] annotation in
        (match issue with
         | Some _ -> issue, env
         | None ->
           let kind =
             if List.is_empty annotation then Binding.Unknown else binding_type annotation
           in
           let env = bind_names env ~kind names in
           annotations env ({ groups; result } : Binder_sequence.t))
      | [] ->
        let issue, _ = walk env ~stops:[] result in
        issue, env
    in
    let issue, env = annotations env sequence in
    let issue =
      match issue with
      | Some _ -> issue
      | None -> fst (walk env ~stops:[] words)
    in
    ({ issue; env } : Inspection.t)
  ;;

  let problem ~twins ~visible ~scopes ~header body =
    let words = header @ body in
    if contains words (qualified "mk")
    then Some "cost record construction outside Cost"
    else if contains words (qualified "ticks")
    then Some "computational Cost.ticks outside Cost"
    else (
      let costed, sequence =
        match declaration header with
        | Some (name, parameters) ->
          String.is_suffix name ~suffix, binder_sequence ~form:Declaration parameters
        | None -> false, ({ groups = []; result = header } : Binder_sequence.t)
      in
      let ({ issue; env } : Inspection.t) =
        scoped_problem
          twins
          ~visible
          ~scopes
          ~costed:false
          ~env:String.Map.empty
          ~sequence
          []
      in
      match issue with
      | Some _ as issue -> issue
      | None ->
        let ({ issue; _ } : Inspection.t) =
          scoped_problem
            twins
            ~visible
            ~scopes
            ~costed
            ~env
            ~sequence:({ groups = []; result = [] } : Binder_sequence.t)
            body
        in
        (match issue with
         | Some _ as issue -> issue
         | None ->
           if costed
           then (
             let list_operations =
               [ "length"
               ; "app"
               ; "rev"
               ; "map"
               ; "filter"
               ; "forallb"
               ; "existsb"
               ; "find"
               ; "fold_left"
               ; "fold_right"
               ; "flat_map"
               ; "concat"
               ; "combine"
               ; "partition"
               ]
             in
             List.find_map list_operations ~f:(fun operation ->
               if contains body [ "List"; "."; operation ]
               then Some [%string "uncharged list operation in costed body: List.%{operation}"]
               else None))
           else None))
  ;;

  let source (source : Source.t) =
    match source.root with
    | (Theories | Examples) when not (String.equal source.package cost_package) ->
      let%bind.Or_error twins = plain_names ~file:source.file source.sentences in
      let%map.Or_error (_ : Scan.t) =
        List.fold_result
          source.sentences
          ~init:({ region = Computation; scopes = []; visible = String.Set.empty } : Scan.t)
          ~f:(fun ({ region; scopes; visible } : Scan.t)
                  ({ line; _ } as sentence : Lex.Sentence.t) ->
            let words = Lex.head (Lex.words sentence) in
            let%bind.Or_error next_scopes = Scope.advance ~file:source.file ~line scopes words in
            let%map.Or_error region =
              match words, region with
              | ("Qed" | "Defined" | "Save") :: _, _ -> Ok Region.Computation
              | "Proof" :: _, _ -> Ok Region.Proof
              | ( ( "Lemma"
                  | "Theorem"
                  | "Example"
                  | "Fact"
                  | "Corollary"
                  | "Proposition"
                  | "Remark"
                  | "Goal" )
                  :: _
                , _ ) ->
                let _, body = split_body words in
                Ok (if Option.is_some body then Region.Computation else Proof)
              | _, Proof -> Ok region
              | _, Computation ->
                let header, body = split_body words in
                if is_prop header
                then Ok (if Option.is_none body then Region.Proof else Computation)
                else (
                  match
                    problem ~twins ~visible ~scopes ~header (Option.value body ~default:[])
                  with
                  | None -> Ok region
                  | Some problem -> Diagnostic.error ~file:source.file ~line problem)
            in
            ({ region
             ; scopes = next_scopes
             ; visible = visible_declaration visible ~scopes words
             }
             : Scan.t))
      in
      ()
    | Theories | Examples | Tests | Legacy_theories | Legacy_examples | Legacy_tests -> Ok ()
  ;;
end

module Hygiene = struct
  let forbidden =
    String.Set.of_list
      [ "Admitted"
      ; "admit"
      ; "give_up"
      ; "Axiom"
      ; "Axioms"
      ; "Parameter"
      ; "Parameters"
      ; "Conjecture"
      ; "Conjectures"
      ]
  ;;

  let queries =
    String.Set.of_list
      [ "Print"
      ; "Check"
      ; "Compute"
      ; "Eval"
      ; "About"
      ; "Locate"
      ; "Search"
      ; "SearchPattern"
      ; "SearchRewrite"
      ]
  ;;

  let local_instance words =
    let rec prefix local = function
      | "Local" :: rest -> prefix true rest
      | "Global" :: rest -> prefix false rest
      | "#" :: "[" :: rest -> attribute local rest
      | ("Polymorphic" | "Monomorphic" | "Program" | "Time") :: rest -> prefix local rest
      | _ -> local
    and attribute local = function
      | "]" :: rest -> prefix local rest
      | "local" :: rest -> attribute true rest
      | ("global" | "export") :: rest -> attribute false rest
      | _ :: rest -> attribute local rest
      | [] -> false
    in
    prefix false words
  ;;

  let import_problem ({ known; forbidden } : Import_policy.t) ~float_import source name =
    if String.is_prefix name ~prefix:Import_policy.stdlib_prefix
    then
      if not (Set.mem known name)
      then Some [%string "unknown pinned Stdlib module: %{name}"]
      else if Set.mem forbidden name && not (Source.is_float_package source || float_import)
      then Some [%string "axiom-bearing Stdlib import outside Float: %{name}"]
      else None
    else if
      String.is_prefix name ~prefix:"GaloisLegacy."
      && Source.Generation.equal (Source.Root.generation source.root) New
      && not (Source.is_legacy_comparison source)
    then Some "new sources may import GaloisLegacy only in tests/legacy"
    else if String.is_prefix name ~prefix:"Galois." || String.is_prefix name ~prefix:"GaloisLegacy."
    then None
    else if
      String.is_prefix name ~prefix:"Flocq." && (Source.is_float_package source || float_import)
    then None
    else Some "dependency outside Stdlib/Galois/GaloisLegacy (Flocq requires Float)"
  ;;

  let record_problem words =
    let problem = "record carrier Type field; parameterize the dictionary instead" in
    let rec carrier = function
      | "(" :: rest -> carrier rest
      | "Type" :: _ -> Some problem
      | _ -> None
    in
    let field tokens =
      match List.rev tokens with
      | _name :: ":" :: rest -> carrier rest
      | _ -> None
    in
    let rec fields depth tokens = function
      | (";" | "}") :: rest when depth = 0 ->
        Option.first_some (field tokens) (fields depth [] rest)
      | (("(" | "{" | "[") as token) :: rest -> fields (depth + 1) (token :: tokens) rest
      | ((")" | "}" | "]") as token) :: rest -> fields (depth - 1) (token :: tokens) rest
      | token :: rest -> fields depth (token :: tokens) rest
      | [] -> field tokens
    in
    let rec record_body = function
      | "{" :: rest -> fields 0 [] rest
      | _ :: rest -> record_body rest
      | [] -> None
    in
    let rec body = function
      | ":" :: "=" :: rest -> record_body rest
      | _ :: rest -> body rest
      | [] -> None
    in
    match words with
    | ("Record" | "Structure" | "Class") :: rest -> body rest
    | _ -> None
  ;;

  let kernel_problem = function
    | "Set" :: "Nested" :: "Proofs" :: "Allowed" :: _ ->
      Some "nested proofs prevent unambiguous theorem completion tracking"
    | ("Reset" | "Back" | "BackTo") :: _ ->
      Some "proof editing command can remove discovered declarations"
    | "Unset" :: ("Guard" | "Positivity" | "Universe") :: "Checking" :: _ ->
      Some "disabled kernel checking"
    | "Unset" :: "Rocqtop" :: "Exit" :: "On" :: "Error" :: _ ->
      Some "disabled strict Rocq query failures"
    | "Load" :: _ | "Declare" :: "ML" :: _ ->
      Some "external source or native plugin bypasses the authored source audit"
    | _ -> None
  ;;

  let kernel_safety (source : Source.t) =
    List.map source.sentences ~f:(fun ({ line; _ } as sentence : Lex.Sentence.t) ->
      match kernel_problem (Lex.head (Lex.words sentence)) with
      | None -> Ok ()
      | Some problem -> Diagnostic.error ~file:source.file ~line problem)
    |> Or_error.combine_errors_unit
  ;;

  let sentence
        ~policy
        ~float_import
        (source : Source.t)
        ({ tokens; line } as sentence : Lex.Sentence.t)
    =
    let words = Lex.words sentence in
    let head = Lex.head words in
    let%bind.Or_error imports =
      Import_policy.imports head
      |> Or_error.tag_s ~tag:[%message "source imports" (source.file : Filename.t) (line : int)]
    in
    let problem =
      match List.find tokens ~f:(fun ({ text; _ } : Lex.Token.t) -> Set.mem forbidden text) with
      | Some ({ text; _ } : Lex.Token.t) ->
        Some [%string "forbidden proof escape or declaration: %{text}"]
      | None ->
        (match head with
         | ("Instance" :: _ | "Existing" :: "Instance" :: _ | "Existing" :: "Instances" :: _)
           when not (local_instance words) -> Some "global instance; dictionaries must be explicit"
         | "Declare" :: "Instance" :: _ -> Some "instance declaration introduces an axiom"
         | "Admit" :: _ -> Some "admitted Program obligation"
         | first :: _
           when Source.is_production source
                && (String.is_prefix first ~prefix:"Extract"
                    || Set.mem queries first
                    || (String.equal first "Recursive"
                        && List.mem head "Extraction" ~equal:String.equal)
                    || (String.equal first "Separate"
                        && List.mem head "Extraction" ~equal:String.equal)) ->
           Some "theory extraction or query command belongs in a client or scratch file"
         | _ ->
           Option.first_some
             (kernel_problem head)
             (Option.first_some
                (List.find_map imports ~f:(import_problem policy ~float_import source))
                (record_problem head)))
    in
    match problem with
    | None -> Ok ()
    | Some problem -> Diagnostic.error ~file:source.file ~line problem
  ;;

  let source ~policy (source : Source.t) =
    let%bind.Or_error () = Cost_lint.source source in
    let%bind.Or_error float_import = Float_boundary.imports_float source in
    let%bind.Or_error scopes =
      List.fold_result
        source.sentences
        ~init:[]
        ~f:(fun scopes ({ line; _ } as current : Lex.Sentence.t) ->
          let head = Lex.head (Lex.words current) in
          let%bind.Or_error () =
            match head with
            | ("Variable" | "Variables" | "Hypothesis" | "Hypotheses" | "Context") :: _
              when not (Scope.inside_section scopes) ->
              Diagnostic.error
                ~file:source.file
                ~line
                "global assumption; bind it in a Section or a theorem instead"
            | _ -> Ok ()
          in
          let%bind.Or_error () = sentence ~policy ~float_import source current in
          Scope.advance ~file:source.file ~line scopes head)
    in
    if List.is_empty scopes
    then Ok ()
    else
      Diagnostic.error ~file:source.file ~line:1 "unclosed Module/Section scope during source audit"
  ;;

  let run sources =
    let%bind.Or_error policy = Import_policy.for_sources sources in
    List.map sources ~f:(source ~policy) |> Or_error.combine_errors_unit
  ;;
end

module Layout = struct
  module Warning = struct
    type t =
      { file : Filename.t
      ; lines : int
      ; limit : int
      }
    [@@deriving sexp_of]
  end

  let line_limit = 1500

  let warnings sources =
    List.filter_map sources ~f:(fun ({ file; root; source; _ } : Source.t) ->
      let lines = List.length (String.split_lines source) in
      if Source.Generation.equal (Source.Root.generation root) New && lines > line_limit
      then Some ({ file; lines; limit = line_limit } : Warning.t)
      else None)
  ;;

  let source ({ file; root; package; _ } : Source.t) =
    let allowed =
      match root with
      | Theories -> Source.packages
      | Tests -> Source.test_packages
      | Legacy_theories -> Source.legacy_packages
      | Legacy_tests -> Set.add Source.legacy_packages Source.examples_package
      | Examples | Legacy_examples -> String.Set.singleton Source.examples_package
    in
    if not (Set.mem allowed package)
    then Diagnostic.error ~file ~line:1 "source must be placed under its declared package directory"
    else if not (String.is_prefix (Filename.basename file) ~prefix:package)
    then Diagnostic.error ~file ~line:1 [%string "Rocq basename must start with package %{package}"]
    else Ok ()
  ;;

  let duplicates sources =
    let by_basename =
      List.map sources ~f:(fun ({ file; _ } : Source.t) -> Filename.basename file, file)
      |> String.Map.of_alist_multi
    in
    Map.fold by_basename ~init:[] ~f:(fun ~key:basename ~data:files errors ->
      match files with
      | [] | [ _ ] -> errors
      | _ ->
        Or_error.error_s
          [%message "duplicate Rocq basename" (basename : string) (files : Filename.t list)]
        :: errors)
  ;;

  let run sources =
    let duplicates =
      List.concat_map Source.Generation.all ~f:(fun generation ->
        List.filter sources ~f:(fun ({ root; _ } : Source.t) ->
          Source.Generation.equal (Source.Root.generation root) generation)
        |> duplicates)
    in
    Or_error.combine_errors_unit (List.map sources ~f:source @ duplicates)
  ;;
end

module Claim = struct
  type t =
    { name : string
    ; line : int
    }
  [@@deriving sexp_of]

  module Scan = struct
    type nonrec t =
      { scopes : Scope.t list
      ; claims : t list
      ; pending : t option
      }
  end

  let declaration ~file ~line ~scopes ~words name =
    if Scope.inside_signature scopes
    then
      Diagnostic.error
        ~file
        ~line
        ~claim:name
        "module signature theorem has no auditable implementation"
    else if
      List.mem
        (List.take_while words ~f:(fun word -> not (String.equal word "Theorem")))
        "Fail"
        ~equal:String.equal
    then
      Diagnostic.error
        ~file
        ~line
        ~claim:name
        "failed theorem command has no declaration to inspect"
    else (
      let modules =
        List.filter_map (List.rev scopes) ~f:(function
          | Scope.Module name -> Some name
          | Scope.Section _ | Scope.Signature _ -> None)
      in
      Ok ({ name = String.concat ~sep:"." (modules @ [ name ]); line } : t))
  ;;

  let step ~file ({ scopes; claims; pending } : Scan.t) ({ line; _ } as sentence : Lex.Sentence.t) =
    let original = Lex.words sentence in
    let words = Lex.head original in
    let%bind.Or_error scopes = Scope.advance ~file ~line scopes words in
    match words, pending with
    | "Abort" :: _, Some ({ name; _ } : t) ->
      Diagnostic.error ~file ~line ~claim:name "aborted theorem has no proof to inspect"
    | "Theorem" :: _ :: _, Some ({ name; _ } : t) ->
      Diagnostic.error ~file ~line ~claim:name "previous theorem proof is incomplete"
    | "Theorem" :: name :: _, None ->
      let%map.Or_error claim = declaration ~file ~line ~scopes ~words:original name in
      (* Theorem always opens a proof; := inside its statement may belong to a let expression. *)
      ({ scopes; claims = claim :: claims; pending = Some claim } : Scan.t)
    | ("Qed" | "Defined" | "Save") :: _, _ ->
      let attempted =
        List.mem
          (List.take_while original ~f:(fun word ->
             not (List.mem [ "Qed"; "Defined"; "Save" ] word ~equal:String.equal)))
          "Fail"
          ~equal:String.equal
      in
      Ok ({ scopes; claims; pending = (if attempted then pending else None) } : Scan.t)
    | _, _ -> Ok ({ scopes; claims; pending } : Scan.t)
  ;;

  let discover ({ file; sentences; _ } : Source.t) =
    let%bind.Or_error ({ scopes; claims; pending } : Scan.t) =
      List.fold_result
        sentences
        ~init:({ scopes = []; claims = []; pending = None } : Scan.t)
        ~f:(step ~file)
    in
    match pending with
    | Some ({ name; line } : t) ->
      Diagnostic.error ~file ~line ~claim:name "theorem proof is incomplete"
    | None ->
      if List.is_empty scopes
      then Ok (List.rev claims)
      else Diagnostic.error ~file ~line:1 "unclosed Module/Section scope during theorem discovery"
  ;;
end

module Query = struct
  module Mode = struct
    type t =
      | Repl
      | Compile
    [@@deriving string ~capitalize:"kebab-case"]

    let arguments = function
      | Repl -> [ "-batch" ]
      | Compile -> []
    ;;
  end

  let scratch = "/tmp/galois-TOOL-1"
  let marker = "__GALOIS_AUDIT_"
  let namespace = "GaloisAuditSource"

  (* The fresh module and exact Locate identity prevent imported-name fallback. *)
  let qualified name = String.concat ~sep:"." [ namespace; name ]
  let closed = "Closed under the global context"
  let axioms = "Axioms:"
  let classic_axiom = "Stdlib.Logic.Classical_Prop.classic"

  let allowed_axioms =
    String.Set.of_list
      [ "Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec"
      ; "Stdlib.Reals.ClassicalDedekindReals.sig_not_dec"
      ; "Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep"
      ; classic_axiom
      ]
  ;;

  let preamble = "Set Rocqtop Exit On Error.\nUnset Nested Proofs Allowed.\n"
  let printing = "Set Printing All.\n"
  let null_device = "/dev/null"

  (* Scope names must differ even when several queries reuse a workspace. *)
  let scope_index = Atomic.make 0

  let rec remove_workspace directory =
    let children =
      let%bind.Or_error entries = Or_error.try_with (fun () -> Sys_unix.ls_dir directory) in
      List.map entries ~f:(fun entry ->
        let file = Filename.concat directory entry in
        let%bind.Or_error ({ st_kind; _ } : Core_unix.stats) =
          Or_error.try_with (fun () -> Core_unix.lstat file)
        in
        match st_kind with
        | S_DIR -> remove_workspace file
        | S_REG | S_LNK | S_CHR | S_BLK | S_FIFO | S_SOCK ->
          Or_error.try_with (fun () -> Core_unix.unlink file))
      |> Or_error.combine_errors_unit
    in
    let removal = Or_error.try_with (fun () -> Core_unix.rmdir directory) in
    Or_error.combine_errors_unit [ children; removal ]
  ;;

  let with_workspace ~f =
    let%bind.Or_error directory =
      Or_error.try_with (fun () ->
        Core_unix.mkdir_p scratch;
        Filename_unix.temp_dir ~in_dir:scratch "query-" "")
      |> Cancellation.fail ~stage:Workspace
    in
    let operation =
      match Or_error.try_with (fun () -> f directory) with
      | Ok result -> result
      | Error error -> Cancellation.fail ~stage:Workspace (Error error)
    in
    let cleanup =
      Or_error.try_with_join (fun () -> remove_workspace directory)
      |> Cancellation.fail ~stage:Workspace
    in
    let%map.Or_error result, () = Or_error.both operation cleanup in
    result
  ;;

  let with_descriptor ?perm ~mode file ~f =
    let%bind.Or_error descriptor =
      Or_error.try_with (fun () -> Core_unix.openfile ?perm ~mode file)
      |> Cancellation.fail ~stage:Descriptor
    in
    let operation =
      Or_error.try_with_join (fun () -> f descriptor) |> Cancellation.fail ~stage:Descriptor
    in
    let cleanup =
      Or_error.try_with (fun () -> Core_unix.close descriptor)
      |> Cancellation.fail ~stage:Descriptor
    in
    let%map.Or_error result, () = Or_error.both operation cleanup in
    result
  ;;

  let run_process ~mode ~directory ~args ~output =
    let operation =
      with_descriptor null_device ~mode:[ O_RDONLY ] ~f:(fun input ->
        with_descriptor output ~perm:0o600 ~mode:[ O_WRONLY; O_CREAT; O_TRUNC ] ~f:(fun output ->
          let index = Atomic.fetch_and_add scope_index 1 in
          let owner = Core_unix.getpid () in
          let unit = [%string "galois-%{owner#Pid}-%{index#Int}.scope"] in
          let ({ pid; _ } : (_, _, _) Core_unix.Pid_with_generated_fds.t) =
            Core_unix.create_process_with_fds
              ~working_dir:directory
              ~prog:"systemd-run"
              ~args:
                ([ "--user"
                 ; "--scope"
                 ; "--quiet"
                 ; "--slice=galois.slice"
                 ; [%string "--unit=%{unit}"]
                 ; "--"
                 ; "env"
                 ; "-u"
                 ; "COQPATH"
                 ; "rocq"
                 ; Mode.to_string mode
                 ; "-q"
                 ]
                 @ Mode.arguments mode
                 @ args)
              ~stdin:(Use_this input)
              ~stdout:(Use_this output)
              ~stderr:(Use_this output)
              ()
          in
          let reaped = ref false in
          let proc_file name = [%string "/proc/%{pid#Pid}/%{name}"] in
          let scope_member () =
            let%map.Or_error groups =
              Or_error.try_with (fun () -> In_channel.read_all (proc_file "cgroup"))
            in
            String.split_lines groups
            |> List.exists ~f:(fun line ->
              String.is_suffix line ~suffix:[%string "/%{unit}"]
              || String.is_suffix line ~suffix:[%string "/%{unit} (deleted)"])
          in
          let terminate () =
            let child = Or_error.try_with (fun () -> Signal_unix.send_i Signal.kill (`Pid pid)) in
            let member = scope_member () in
            let scope =
              let%bind.Or_error member = member in
              if not member
              then Ok ()
              else
                Or_error.try_with_join (fun () ->
                  let ({ pid = killer; _ } : (_, _, _) Core_unix.Pid_with_generated_fds.t) =
                    Core_unix.create_process_with_fds
                      ~prog:"systemctl"
                      ~args:[ "--user"; "kill"; "--kill-whom=all"; "--signal=KILL"; unit ]
                      ~stdin:(Use_this input)
                      ~stdout:(Use_this output)
                      ~stderr:(Use_this output)
                      ()
                  in
                  let status = Or_error.try_with (fun () -> Core_unix.waitpid killer) in
                  let status =
                    match status with
                    | Ok _ -> status
                    | Error _ ->
                      let signal =
                        Or_error.try_with (fun () -> Signal_unix.send_i Signal.kill (`Pid killer))
                      in
                      let reap = Or_error.try_with (fun () -> Core_unix.waitpid killer) in
                      Or_error.both status (Or_error.both signal reap) |> Or_error.map ~f:fst
                  in
                  let%bind.Or_error status = status in
                  match status with
                  | Ok () -> Ok ()
                  | Error _ as status ->
                    Or_error.error_s
                      [%message
                        "cannot terminate Rocq scope"
                          (unit : string)
                          (status : Core_unix.Exit_or_signal.t)])
            in
            let status = Or_error.try_with (fun () -> Core_unix.waitpid pid) in
            if Result.is_ok status then reaped := true;
            let%map.Or_error _, status = Or_error.both (Or_error.both scope child) status in
            status
          in
          let rec wait () =
            let process = In_channel.read_all (proc_file "status") in
            if String.is_substring process ~substring:"State:\tZ"
            then (
              let member = scope_member () in
              let status = Core_unix.waitpid pid in
              reaped := true;
              let%bind.Or_error member = member in
              if not member
              then
                Or_error.error_s
                  [%message
                    "Rocq scope was not established"
                      (unit : string)
                      (status : Core_unix.Exit_or_signal.t)]
              else Ok status)
            else if Atomic.get Cancellation.requested
            then terminate ()
            else (
              Caml_threads.Thread.delay 0.05;
              wait ())
          in
          match Or_error.try_with_join wait with
          | Ok _ as result -> result
          | Error _ as result when !reaped -> result
          | Error _ as result -> Or_error.both result (terminate ()) |> Or_error.map ~f:fst))
    in
    let transcript =
      Or_error.try_with (fun () -> In_channel.read_all output)
      |> Cancellation.fail ~stage:Transcript
    in
    let%bind.Or_error status, transcript =
      match operation, transcript with
      | Error error, Ok transcript ->
        Or_error.tag_s (Error error) ~tag:[%message "Rocq process transcript" (transcript : string)]
      | Ok status, Ok transcript -> Ok (status, transcript)
      | Ok _, (Error _ as error) -> error
      | (Error _ as operation), (Error _ as transcript) -> Or_error.both operation transcript
    in
    match status with
    | Ok () -> Ok transcript
    | Error (`Exit_non_zero (125 | 126 | 127) | `Signal _) ->
      Or_error.error_s
        [%message
          "Rocq assumptions query failed"
            (status : Core_unix.Exit_or_signal.t)
            (transcript : string)]
      |> Cancellation.fail ~stage:Process
    | Error (`Exit_non_zero _) ->
      Or_error.error_s
        [%message
          "Rocq assumptions query failed"
            (status : Core_unix.Exit_or_signal.t)
            (transcript : string)]
  ;;

  module Load_path = struct
    type t =
      { relative : Filename.t
      ; logical : string
      }
  end

  let package_paths =
    let packages =
      Set.to_list Source.packages
      |> List.filter ~f:(fun package -> not (String.equal package "Analyses"))
    in
    List.map packages ~f:(fun package ->
      ({ relative = [%string "theories/%{package}"]; logical = [%string "Galois.%{package}"] }
       : Load_path.t))
    @ List.map (Set.to_list Source.analysis_families) ~f:(fun family ->
      ({ relative = [%string "theories/Analyses/%{family}"]
       ; logical = [%string "Galois.Analyses.%{family}"]
       }
       : Load_path.t))
    @ [ ({ relative = "theories/Domains/Memory"; logical = "Galois.Domains.Memory" } : Load_path.t)
      ]
    @ List.map (Set.to_list Source.legacy_packages) ~f:(fun package ->
      ({ relative = [%string "legacy/theories/%{package}"]
       ; logical = [%string "GaloisLegacy.%{package}"]
       }
       : Load_path.t))
    @ List.concat_map (Set.to_list Source.test_packages) ~f:(fun package ->
      [ ({ relative = [%string "tests/%{package}"]; logical = [%string "Galois.Tests.%{package}"] }
         : Load_path.t)
      ; { relative = [%string "tests/legacy/%{package}"]
        ; logical = [%string "Galois.Tests.Legacy.%{package}"]
        }
      ])
  ;;

  let client_paths =
    [ ({ relative = "examples"; logical = "Galois.Examples" } : Load_path.t)
    ; { relative = "legacy/examples"; logical = "GaloisLegacy.Examples" }
    ; { relative = "legacy/tests"; logical = "GaloisLegacy.Tests" }
    ]
  ;;

  let load_paths repository =
    let candidate = Filename.concat repository "_build/default" in
    let build =
      match Sys_unix.is_directory candidate with
      | `Yes -> candidate
      | `No | `Unknown -> repository
    in
    let packages =
      package_paths
      |> List.filter_map ~f:(fun ({ relative; logical } : Load_path.t) ->
        let directory = Filename.concat build relative in
        if
          Sys_unix.is_directory directory
          |> function
          | `Yes -> true
          | `No | `Unknown -> false
        then Some [ "-Q"; directory; logical ]
        else None)
    in
    List.concat
      (packages
       @ List.map client_paths ~f:(fun ({ relative; logical } : Load_path.t) ->
         [ "-Q"; Filename.concat build relative; logical ]))
  ;;

  let delimiter index = [%string "%{marker}%{index#Int}__"]

  let mark index =
    let label = delimiter index in
    [%string "Goal True. Proof. idtac \"%{label}\". Abort.\n"]
  ;;

  let execute ~repository source commands =
    if String.is_substring source ~substring:marker
    then Or_error.error_string "reserved audit delimiter in source"
    else
      with_workspace ~f:(fun directory ->
        let input = Filename.concat directory "Query.v" in
        let script =
          String.concat
            [ preamble
            ; [%string "Module %{namespace}.\n"]
            ; source
            ; [%string "\nEnd %{namespace}.\n"]
            ; printing
            ; List.mapi commands ~f:(fun index command ->
                String.concat [ mark index; command; "\n" ])
              |> String.concat
            ; mark (List.length commands)
            ]
        in
        let%bind.Or_error () =
          Or_error.try_with (fun () -> Out_channel.write_all input ~data:script)
          |> Cancellation.fail ~stage:Script
        in
        let output = Filename.concat directory "Query.log" in
        run_process ~mode:Repl ~directory ~args:(load_paths repository @ [ "-l"; input ]) ~output)
  ;;

  let blocks ~count transcript =
    let lines = String.split_lines transcript in
    let rec loop index lines blocks =
      if index = count
      then
        if List.exists lines ~f:(fun line -> not (String.is_empty (String.strip line)))
        then Or_error.error_string "unexpected trailing assumptions query output"
        else Ok (List.rev blocks)
      else (
        let label = delimiter (index + 1) in
        let block, rest = List.split_while lines ~f:(fun line -> not (String.equal line label)) in
        match rest with
        | [] -> Or_error.error_s [%message "incomplete assumptions query" (index : int)]
        | _ :: rest -> loop (index + 1) rest (block :: blocks))
    in
    let _, remaining =
      List.split_while lines ~f:(fun line -> not (String.equal line (delimiter 0)))
    in
    match remaining with
    | [] -> Or_error.error_string "missing assumptions query delimiter"
    | _ :: rest -> loop 0 rest []
  ;;

  let assumption_names lines =
    match List.filter lines ~f:(fun line -> not (String.is_empty (String.strip line))) with
    | [ line ] when String.equal line closed -> Ok []
    | header :: rest when String.equal header axioms ->
      let names =
        List.filter_map rest ~f:(fun line ->
          if Char.is_whitespace line.[0]
          then None
          else
            Some
              (String.lsplit2 line ~on:':' |> Option.value_map ~default:line ~f:fst |> String.strip))
      in
      if
        List.is_empty names
        || List.exists names ~f:(fun name ->
          String.is_empty name
          || not (String.for_all name ~f:(fun c -> Lex.is_identifier c || Char.equal c '.')))
      then Or_error.error_s [%message "unrecognized axiom report" (lines : string list)]
      else Ok names
    | _ ->
      Or_error.error_s [%message "missing or unrecognized assumptions report" (lines : string list)]
  ;;

  let claim_report ~name = function
    | identity :: report when String.equal identity [%string "Constant Top.%{qualified name}"] ->
      assumption_names report
    | "Constant" :: identity :: report when String.equal identity [%string "Top.%{qualified name}"]
      -> assumption_names report
    | lines ->
      Or_error.error_s
        [%message
          "claim does not resolve to the source declaration" (name : string) (lines : string list)]
  ;;

  let resolve lines =
    match lines with
    | [ line ] ->
      (match String.chop_prefix line ~prefix:"Constant " with
       | Some name when Set.mem allowed_axioms name -> Ok ()
       | Some name -> Or_error.error_s [%message "unexpected Float axiom" (name : string)]
       | None -> Or_error.error_s [%message "unrecognized axiom identity" (line : string)])
    | _ -> Or_error.error_s [%message "ambiguous axiom identity" (lines : string list)]
  ;;
end

module Claims = struct
  module Report = struct
    type t =
      { claim : Claim.t
      ; assumptions : string list
      }
  end

  let check_names (source : Source.t) (claim : Claim.t) names =
    let%bind.Or_error float_import = Float_boundary.imports_float source in
    if List.is_empty names || float_import
    then Ok ()
    else
      Diagnostic.error
        ~file:source.file
        ~line:claim.line
        ~claim:claim.name
        [%string "theorem depends on axioms: %{String.concat ~sep:\", \" names}"]
  ;;

  let inspect (source : Source.t) ~claims ~transcript =
    let%bind.Or_error blocks =
      Query.blocks ~count:(List.length claims) transcript
      |> Or_error.tag_s
           ~tag:
             [%message
               "incomplete source inspection" (source.file : Filename.t) (claims : Claim.t list)]
    in
    List.map2_exn claims blocks ~f:(fun claim block ->
      let%bind.Or_error assumptions =
        Query.claim_report ~name:claim.name block
        |> Or_error.tag_s
             ~tag:
               [%message "incomplete claim inspection" (source.file : Filename.t) (claim : Claim.t)]
      in
      let%map.Or_error () = check_names source claim assumptions in
      ({ claim; assumptions } : Report.t))
    |> Or_error.combine_errors
  ;;

  let validate_float (source : Source.t) ~reports ~axioms ~transcript =
    let%bind.Or_error blocks = Query.blocks ~count:(List.length axioms) transcript in
    let resolutions =
      List.map2_exn axioms blocks ~f:(fun axiom block -> axiom, Query.resolve block)
      |> String.Map.of_alist_exn
    in
    List.concat_map reports ~f:(fun ({ claim; assumptions } : Report.t) ->
      List.map assumptions ~f:(fun axiom ->
        Map.find resolutions axiom
        |> Option.value
             ~default:(Or_error.error_s [%message "missing axiom resolution" (axiom : string)])
        |> Or_error.tag_s
             ~tag:[%message "Float theorem assumption" (source.file : Filename.t) (claim : Claim.t)]))
    |> Or_error.combine_errors_unit
  ;;

  let source ~repository (source : Source.t) =
    let%bind.Or_error () = Hygiene.kernel_safety source in
    let%bind.Or_error claims = Claim.discover source in
    if List.is_empty claims
    then Ok ()
    else (
      let commands =
        List.map claims ~f:(fun ({ name; _ } : Claim.t) ->
          let name = Query.qualified name in
          [%string "Locate %{name}.\nPrint Assumptions %{name}."])
      in
      let%bind.Or_error transcript =
        Query.execute ~repository source.source commands
        |> Or_error.tag_s
             ~tag:
               [%message
                 "cannot inspect source claims" (source.file : Filename.t) (claims : Claim.t list)]
      in
      let%bind.Or_error reports = inspect source ~claims ~transcript in
      let axioms =
        List.concat_map reports ~f:(fun ({ assumptions; _ } : Report.t) -> assumptions)
        |> String.Set.of_list
        |> Set.to_list
      in
      if List.is_empty axioms
      then Ok ()
      else (
        let commands = List.map axioms ~f:(fun name -> [%string "Locate %{name}."]) in
        let result =
          let%bind.Or_error transcript = Query.execute ~repository source.source commands in
          validate_float source ~reports ~axioms ~transcript
        in
        Or_error.tag_s
          result
          ~tag:
            [%message
              "Float assumptions inspection" (source.file : Filename.t) (claims : Claim.t list)]))
  ;;

  let run_workers ~(jobs : Jobs.t) ~f sources =
    let run_parallel () =
      let sources = Array.of_list sources in
      let results = Array.create ~len:(Array.length sources) None in
      let lock = Caml_threads.Mutex.create () in
      (* The lock protects assignment of each index to exactly one worker. *)
      let next = ref 0 in
      let rec worker () =
        Caml_threads.Mutex.lock lock;
        let index = !next in
        Int.incr next;
        Caml_threads.Mutex.unlock lock;
        if index < Array.length sources && not (Atomic.get Cancellation.requested)
        then (
          let result =
            match Or_error.try_with (fun () -> f sources.(index)) with
            | Ok result -> result
            | Error error ->
              Atomic.set Cancellation.requested true;
              Or_error.tag_s
                (Error error)
                ~tag:[%message "fatal claims worker failure; coverage incomplete" (index : int)]
          in
          results.(index) <- Some result;
          worker ())
      in
      let failure = ref (Ok ()) in
      let run_worker () =
        let result = Or_error.try_with worker in
        if Result.is_error result
        then (
          Atomic.set Cancellation.requested true;
          Caml_threads.Mutex.lock lock;
          failure := Or_error.combine_errors_unit [ !failure; result ];
          Caml_threads.Mutex.unlock lock)
      in
      let thread = Or_error.try_with (fun () -> Caml_threads.Thread.create run_worker ()) in
      if Result.is_error thread then Atomic.set Cancellation.requested true;
      run_worker ();
      let joined =
        match thread with
        | Ok thread -> Or_error.try_with (fun () -> Caml_threads.Thread.join thread)
        | Error error ->
          Atomic.set Cancellation.requested true;
          Error error
      in
      let coverage =
        Array.to_list results
        |> List.map ~f:(Option.value ~default:(Or_error.error_string "incomplete claims coverage"))
        |> Or_error.combine_errors_unit
      in
      Or_error.combine_errors_unit [ !failure; joined; coverage ]
    in
    match jobs with
    | One ->
      List.map sources ~f:(fun item ->
        if Atomic.get Cancellation.requested
        then Or_error.error_string "incomplete claims coverage"
        else (
          match Or_error.try_with (fun () -> f item) with
          | Ok result -> result
          | Error error ->
            Atomic.set Cancellation.requested true;
            Or_error.tag_s
              (Error error)
              ~tag:[%message "fatal claims worker failure; coverage incomplete"]))
      |> Or_error.combine_errors_unit
    | Two -> run_parallel ()
  ;;

  let run ~repository sources =
    let%bind.Or_error jobs = Jobs.parse (Sys.getenv Jobs.variable) in
    Atomic.set Cancellation.requested false;
    let handler = `Handle (fun _ -> Atomic.set Cancellation.requested true) in
    let%bind.Or_error previous_int =
      Or_error.try_with (fun () -> Signal.Expert.signal Signal.int handler)
    in
    let operation =
      Or_error.try_with_join (fun () ->
        let%bind.Or_error previous_term =
          Or_error.try_with (fun () -> Signal.Expert.signal Signal.term handler)
        in
        let inspect_source (item : Source.t) =
          match Or_error.try_with (fun () -> source ~repository item) with
          | Ok result -> result
          | Error error ->
            Atomic.set Cancellation.requested true;
            Or_error.tag_s
              (Error error)
              ~tag:[%message "fatal source failure; coverage incomplete" (item.file : Filename.t)]
        in
        let result =
          Or_error.try_with_join (fun () -> run_workers ~jobs ~f:inspect_source sources)
        in
        let restore = Or_error.try_with (fun () -> Signal.Expert.set Signal.term previous_term) in
        let%map.Or_error result, () = Or_error.both result restore in
        result)
    in
    let restore = Or_error.try_with (fun () -> Signal.Expert.set Signal.int previous_int) in
    let result = Or_error.both operation restore |> Or_error.map ~f:fst in
    let cancelled = Atomic.get Cancellation.requested in
    Atomic.set Cancellation.requested false;
    if cancelled
    then Or_error.combine_errors_unit [ result; Or_error.error_string "claims coverage incomplete" ]
    else result
  ;;
end

let run ~repository audits =
  let%bind.Or_error repository = Or_error.try_with (fun () -> Filename_unix.realpath repository) in
  let%bind.Or_error sources = Source.discover repository in
  List.map audits ~f:(fun (audit : Audit.t) ->
    match audit with
    | Hygiene -> Hygiene.run sources
    | Layout ->
      List.iter (Layout.warnings sources) ~f:(fun warning ->
        eprint_s
          [%message "warning: new Rocq source exceeds line limit" (warning : Layout.Warning.t)]);
      Layout.run sources
    | Claims -> Claims.run ~repository sources)
  |> Or_error.combine_errors_unit
;;

let check_command audits =
  Command.basic_or_error
    ~summary:"Audit authored Rocq sources and kernel-reported theorem assumptions"
    (let%map_open.Command repository =
       flag "root" (optional_with_default "." string) ~doc:"DIRECTORY repository root"
     in
     fun () -> run ~repository audits)
;;

module Extraction = struct
  let artifacts = [ "algorithms.ml"; "algorithms.mli"; "rules_solver.ml"; "rules_solver.mli" ]
  let solver_implementation = "rules_solver.ml"
  let solver_interface = "rules_solver.mli"
  let compact source = String.filter source ~f:(fun c -> not (Char.is_whitespace c))
  let cost_sentinel = "GALOIS_COST_TICKS"

  let cost_leak ~file source =
    if String.is_substring source ~substring:cost_sentinel
    then Or_error.error_s [%message "cost observation leaked into extraction" (file : Filename.t)]
    else Ok ()
  ;;

  let forbidden ~file source spelling =
    if String.is_substring (compact source) ~substring:spelling
    then
      Or_error.error_s
        [%message "forbidden extraction dependency" (file : Filename.t) (spelling : string)]
    else Ok ()
  ;;

  let required ~file source spelling =
    if String.is_substring (compact source) ~substring:spelling
    then Ok ()
    else
      Or_error.error_s
        [%message "missing extraction declaration" (file : Filename.t) (spelling : string)]
  ;;

  (* Each monolithic extraction includes its complete transitive dependency closure. Checking
     the whole solver output also catches universe enumeration hidden behind helper calls. *)
  let inspect ~file source =
    let%bind.Or_error () = cost_leak ~file source in
    let%bind.Or_error () = forbidden ~file source "Obj.magic" in
    let basename = Filename.basename file in
    if String.equal basename solver_implementation || String.equal basename solver_interface
    then (
      let%bind.Or_error () =
        List.map [ "herbrand"; "tuple_words" ] ~f:(forbidden ~file (String.lowercase source))
        |> Or_error.combine_errors_unit
      in
      if String.equal basename solver_interface
      then (
        let%bind.Or_error () =
          required ~file source "valfinite_powerset_lattice:'a1encoding->'a1finite_setlattice"
        in
        required ~file source "valsolve_program:'a1program->'a1ground_atomlist->'a1databaseoption")
      else required ~file source "letsolve_programprogfacts=")
    else if String.is_empty (String.strip source)
    then Or_error.error_s [%message "empty extraction artifact" (file : Filename.t)]
    else Ok ()
  ;;

  let run files =
    let actual = List.map files ~f:Filename.basename |> List.sort ~compare:String.compare in
    let expected = List.sort artifacts ~compare:String.compare in
    if not ([%equal: string list] actual expected)
    then
      Or_error.error_s
        [%message "incomplete extraction inventory" (actual : string list) (expected : string list)]
    else
      List.map files ~f:(fun file ->
        let%bind.Or_error source = Or_error.try_with (fun () -> In_channel.read_all file) in
        inspect ~file source)
      |> Or_error.combine_errors_unit
  ;;

  let command =
    Command.basic_or_error
      ~summary:"Inspect all generated artifacts and the complete Rules solver closure"
      (let%map_open.Command files = anon (sequence ("ARTIFACT" %: string)) in
       fun () -> run files)
  ;;

  let cost_command =
    Command.basic_or_error
      ~summary:"Inspect cost-erased generated artifacts without the legacy inventory"
      (let%map_open.Command files = anon (non_empty_sequence_as_list ("ARTIFACT" %: string)) in
       fun () ->
         List.map files ~f:(fun file ->
           let%bind.Or_error source = Or_error.try_with (fun () -> In_channel.read_all file) in
           inspect ~file source)
         |> Or_error.combine_errors_unit)
  ;;
end

let command =
  Command.group
    ~summary:"Check source hygiene, layout and theorem assumptions"
    ~preserve_subcommand_order:()
    ~body:(fun ~path:_ ->
      match run ~repository:"." Audit.all with
      | Ok () -> ()
      | Error error ->
        eprint_s [%sexp (error : Error.t)];
        exit 1)
    (List.map Audit.all ~f:(fun audit -> Audit.to_string audit, check_command [ audit ])
     @ [ "extraction", Extraction.command; "cost-extraction", Extraction.cost_command ])
;;

module Fixture = struct
  let file = "legacy/theories/Collections/CollectionsFixture.v"
  let closed = "Theorem closed : True. Proof. exact I. Qed."

  let classical =
    "From Stdlib.Logic Require Import Classical_Prop. Theorem classical_claim : forall P, P \\/ ~ \
     P. Proof. exact classic. Qed."
  ;;

  let reals =
    "From Stdlib.Reals Require Import Reals. Theorem real_claim : forall x y, Rplus x y = Rplus y \
     x. Proof. exact Rplus_comm. Qed."
  ;;

  let repository = Query.scratch
  let while_file = "While/ExamplesWhileFixture.v"
  let ssa_file = "Ssa/ExamplesSsaFixture.v"
  let examples_test_file = "Examples/ExamplesTestFixture.v"

  module Path = struct
    type t =
      { root : Source.Root.t
      ; relative : Filename.t
      }
  end

  let example_paths =
    [ ({ root = Legacy_examples; relative = while_file } : Path.t)
    ; ({ root = Legacy_examples; relative = ssa_file } : Path.t)
    ; ({ root = Legacy_tests; relative = examples_test_file } : Path.t)
    ]
  ;;

  let source ?(root = Source.Root.Legacy_theories) ?(package = "Collections") ?(file = file) source =
    let sentences = Lex.scan ~file source |> Or_error.ok_exn in
    let relative =
      String.chop_prefix file ~prefix:[%string "%{Source.Root.to_string root}/"]
      |> Option.value ~default:file
    in
    ({ file; root; relative; package; source; sentences } : Source.t)
  ;;

  let at ~root relative text =
    let file = Filename.concat (Source.Root.to_string root) relative in
    source ~root ~package:(Source.package ~root relative) ~file text
  ;;

  let examples text =
    List.map example_paths ~f:(fun ({ root; relative } : Path.t) -> at ~root relative text)
  ;;

  let with_repository ~f =
    let relative =
      [ file
      ; "legacy/tests/Collections/CollectionsTestFixture.v"
      ; "theories/Base/BaseFixture.v"
      ; "examples/Tutorial/ExamplesTutorialFixture.v"
      ; "tests/Base/BaseTestFixture.v"
      ; "tests/legacy/Base/BaseLegacyTestFixture.v"
      ]
      @ List.map example_paths ~f:(fun ({ root; relative } : Path.t) ->
        Filename.concat (Source.Root.to_string root) relative)
    in
    Query.with_workspace ~f:(fun directory ->
      List.iter Source.Root.all ~f:(fun root ->
        Core_unix.mkdir_p (Filename.concat directory (Source.Root.to_string root)));
      let files = List.map relative ~f:(Filename.concat directory) in
      List.iter files ~f:(fun file ->
        Core_unix.mkdir_p (Filename.dirname file);
        Out_channel.write_all file ~data:closed);
      f directory;
      Ok ())
    |> Or_error.ok_exn
  ;;

  let float_import = "From GaloisLegacy.Float Require Import FloatPrelude.\n"
  let float_source text = source (String.concat [ float_import; text ])

  let with_float_repository ~f =
    Query.with_workspace ~f:(fun repository ->
      let files =
        List.map [ "theories/Float"; "legacy/theories/Float" ] ~f:(fun relative ->
          let directory = Filename.concat repository relative in
          Core_unix.mkdir_p directory;
          let file = Filename.concat directory "FloatPrelude.v" in
          Out_channel.write_all file ~data:"From Stdlib.Reals Require Export Reals.";
          file)
      in
      let output = Filename.concat repository "Compile.log" in
      let%bind.Or_error () =
        List.map files ~f:(fun file ->
          let%map.Or_error _ =
            Query.run_process
              ~mode:Compile
              ~directory:repository
              ~args:(Query.load_paths repository @ [ file ])
              ~output
          in
          ())
        |> Or_error.combine_errors_unit
      in
      f repository)
  ;;
end

let%expect_test "new package and family load paths resolve alongside reused legacy basenames" =
  let sources =
    [ Fixture.at ~root:Theories "Graph/GraphFixture.v" Fixture.closed
    ; Fixture.at ~root:Legacy_theories "Graph/GraphFixture.v" Fixture.closed
    ; Fixture.at ~root:Theories "Analyses/Memory/AnalysesFixture.v" Fixture.closed
    ; Fixture.at ~root:Theories "Next/Extension/NextFixture.v" Fixture.closed
    ; Fixture.at ~root:Tests "Graph/GraphTestFixture.v" Fixture.closed
    ; Fixture.at ~root:Tests "legacy/Graph/GraphLegacyTestFixture.v" Fixture.closed
    ; Fixture.at ~root:Examples "Tutorial/ExamplesTutorialFixture.v" Fixture.closed
    ; Fixture.at ~root:Theories "Domains/DomainsFixture.v" Fixture.closed
    ; Fixture.at ~root:Theories "Domains/Memory/DomainsMemoryFixture.v" Fixture.closed
    ; Fixture.at ~root:Tests "Domains/Memory/DomainsDemandTestFixture.v" Fixture.closed
    ; Fixture.at ~root:Tests "legacy/Domains/Memory/DomainsDemandLegacyTestFixture.v" Fixture.closed
    ; Fixture.at ~root:Tests "Examples/Ssa/ExamplesSsaSyntaxTestFixture.v" Fixture.closed
    ; Fixture.at
        ~root:Tests
        "legacy/Examples/Ssa/ExamplesSsaTypingLegacyTestFixture.v"
        Fixture.closed
    ]
  in
  let result =
    Query.with_workspace ~f:(fun repository ->
      let%bind.Or_error () = Layout.run sources in
      List.iter sources ~f:(fun ({ file; source; _ } : Source.t) ->
        let file = Filename.concat repository file in
        Core_unix.mkdir_p (Filename.dirname file);
        Out_channel.write_all file ~data:source);
      let args = Query.load_paths repository in
      let output = Filename.concat repository "Compile.log" in
      let%bind.Or_error () =
        List.map sources ~f:(fun ({ file; _ } : Source.t) ->
          let file = Filename.concat repository file in
          let%map.Or_error _ =
            Query.run_process ~mode:Compile ~directory:repository ~args:(args @ [ file ]) ~output
          in
          ())
        |> Or_error.combine_errors_unit
      in
      let linked =
        {|From Galois.Graph Require GraphFixture.
From GaloisLegacy.Graph Require GraphFixture.
From Galois.Analyses.Memory Require AnalysesFixture.
From Galois.Next.Extension Require NextFixture.
From Galois.Tests.Graph Require GraphTestFixture.
From Galois.Tests.Legacy.Graph Require GraphLegacyTestFixture.
From Galois.Examples.Tutorial Require ExamplesTutorialFixture.
From Galois.Domains Require DomainsFixture.
From Galois.Domains.Memory Require DomainsMemoryFixture.
From Galois.Tests.Domains.Memory Require DomainsDemandTestFixture.
From Galois.Tests.Legacy.Domains.Memory Require DomainsDemandLegacyTestFixture.
From Galois.Tests.Examples.Ssa Require ExamplesSsaSyntaxTestFixture.
From Galois.Tests.Legacy.Examples.Ssa Require ExamplesSsaTypingLegacyTestFixture.
Theorem linked : True.
Proof.
  pose proof Galois.Graph.GraphFixture.closed.
  pose proof GaloisLegacy.Graph.GraphFixture.closed.
  pose proof AnalysesFixture.closed.
  pose proof NextFixture.closed.
  pose proof GraphTestFixture.closed.
  pose proof GraphLegacyTestFixture.closed.
  pose proof DomainsFixture.closed.
  pose proof DomainsMemoryFixture.closed.
  pose proof DomainsDemandTestFixture.closed.
  pose proof DomainsDemandLegacyTestFixture.closed.
  pose proof ExamplesSsaSyntaxTestFixture.closed.
  pose proof ExamplesSsaTypingLegacyTestFixture.closed.
  exact ExamplesTutorialFixture.closed.
Qed.|}
      in
      let source = Fixture.at ~root:Tests "legacy/Graph/GraphLinkedTest.v" linked in
      let%bind.Or_error () = Hygiene.run [ source ] in
      Claims.source ~repository source)
  in
  print_s [%sexp (result : unit Or_error.t)];
  [%expect {| (Ok ()) |}]
;;

let%expect_test "new package and client directories are accepted independently of legacy packages" =
  print_s [%sexp (Source.packages : String.Set.t)];
  print_s [%sexp (Source.legacy_packages : String.Set.t)];
  let theories =
    Set.to_list Source.packages
    |> List.map ~f:(fun package ->
      let directory =
        if String.equal package "Analyses"
        then "Analyses/Memory"
        else if String.equal package "Next"
        then "Next/Extension"
        else package
      in
      Fixture.at ~root:Theories [%string "%{directory}/%{package}Fixture.v"] Fixture.closed)
  in
  let tests =
    Set.to_list Source.packages
    |> List.concat_map ~f:(fun package ->
      List.map
        [ package; [%string "legacy/%{package}"] ]
        ~f:(fun directory ->
          Fixture.at ~root:Tests [%string "%{directory}/%{package}TestFixture.v"] Fixture.closed))
  in
  let examples =
    Set.to_list Source.example_directories
    |> List.map ~f:(fun directory ->
      Fixture.at
        ~root:Examples
        [%string "%{directory}/Examples%{directory}Fixture.v"]
        Fixture.closed)
  in
  List.iter
    (theories @ tests @ examples)
    ~f:(fun source -> Layout.run [ source ] |> Or_error.ok_exn);
  print_s [%sexp (Layout.run (theories @ examples) : unit Or_error.t)];
  [%expect
    {|
    (Analyses Base Bits Cost Datalog Domains Egraph Fixpoint Float Framework
     Graph Lattice Next Program)
    (Analyses Bits Collections Domains Fixpoint Float Graph Order Rewrite Rules
     Views)
    (Ok ())
    |}]
;;

let%expect_test "memory domains and example tests mirror their supported subdirectories" =
  let memory =
    [ Fixture.at ~root:Theories "Domains/Memory/DomainsDemand.v" Fixture.closed
    ; Fixture.at ~root:Tests "Domains/Memory/DomainsDemandTest.v" Fixture.closed
    ; Fixture.at ~root:Tests "legacy/Domains/Memory/DomainsDemandLegacyTest.v" Fixture.closed
    ]
  in
  let examples =
    Set.to_list Source.example_directories
    |> List.concat_map ~f:(fun directory ->
      [ Fixture.at
          ~root:Tests
          [%string "Examples/%{directory}/Examples%{directory}Test.v"]
          Fixture.closed
      ; Fixture.at
          ~root:Tests
          [%string "legacy/Examples/%{directory}/Examples%{directory}LegacyTest.v"]
          Fixture.closed
      ])
  in
  print_s [%sexp (Source.test_packages : String.Set.t)];
  print_s [%sexp (Layout.run (memory @ examples) : unit Or_error.t)];
  [%expect
    {|
    (Analyses Base Bits Cost Datalog Domains Egraph Examples Fixpoint Float
     Framework Graph Lattice Next Program)
    (Ok ())
    |}]
;;

let%expect_test "unknown memory and example test directories remain invalid" =
  List.iter
    [ Fixture.at ~root:Theories "Domains/Unknown/DomainsDemand.v" Fixture.closed
    ; Fixture.at ~root:Tests "Domains/Unknown/DomainsDemandTest.v" Fixture.closed
    ; Fixture.at ~root:Tests "legacy/Domains/Unknown/DomainsDemandLegacyTest.v" Fixture.closed
    ; Fixture.at ~root:Theories "Domains/Memory/Nested/DomainsDemand.v" Fixture.closed
    ; Fixture.at ~root:Tests "Examples/Unknown/ExamplesTest.v" Fixture.closed
    ; Fixture.at ~root:Tests "legacy/Examples/Unknown/ExamplesLegacyTest.v" Fixture.closed
    ; Fixture.at ~root:Tests "Examples/ExamplesTest.v" Fixture.closed
    ; Fixture.at ~root:Tests "legacy/Examples/ExamplesLegacyTest.v" Fixture.closed
    ; Fixture.at ~root:Tests "Examples/Ssa/Nested/ExamplesTest.v" Fixture.closed
    ; Fixture.at ~root:Tests "legacy/Examples/Ssa/Nested/ExamplesLegacyTest.v" Fixture.closed
    ]
    ~f:(fun source -> print_s [%sexp (Result.is_error (Layout.run [ source ]) : bool)]);
  [%expect
    {|
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    |}]
;;

let%expect_test "new layout rejects legacy packages unknown families and misplaced extension files" =
  List.iter
    [ Fixture.at ~root:Theories "Collections/CollectionsFixture.v" Fixture.closed
    ; Fixture.at ~root:Legacy_theories "Base/BaseFixture.v" Fixture.closed
    ; Fixture.at ~root:Theories "Analyses/Unknown/AnalysesFixture.v" Fixture.closed
    ; Fixture.at ~root:Theories "Analyses/AnalysesFixture.v" Fixture.closed
    ; Fixture.at ~root:Theories "Next/NextFixture.v" Fixture.closed
    ; Fixture.at ~root:Legacy_examples "Tutorial/ExamplesTutorialFixture.v" Fixture.closed
    ; Fixture.at ~root:Tests "Unknown/UnknownTest.v" Fixture.closed
    ]
    ~f:(fun source -> print_s [%sexp (Result.is_error (Layout.run [ source ]) : bool)]);
  [%expect
    {|
    true
    true
    true
    true
    true
    true
    true
    |}]
;;

let%expect_test "Analyses families retain their package prefix" =
  let sources =
    Set.to_list Source.analysis_families
    |> List.map ~f:(fun family ->
      Fixture.at ~root:Theories [%string "Analyses/%{family}/Analyses%{family}.v"] Fixture.closed)
  in
  print_s [%sexp (Layout.run sources : unit Or_error.t)];
  let wrong = Fixture.at ~root:Theories "Analyses/Memory/MemoryWalk.v" Fixture.closed in
  print_s [%sexp (Layout.run [ wrong ] : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Error
     ((file theories/Analyses/Memory/MemoryWalk.v) (line 1) (claim ())
      (problem "Rocq basename must start with package Analyses")))
    |}]
;;

let%expect_test "basename uniqueness separates generations and includes new differential tests" =
  let legacy = Fixture.at ~root:Legacy_theories "Graph/GraphFixture.v" Fixture.closed in
  let fresh = Fixture.at ~root:Theories "Graph/GraphFixture.v" Fixture.closed in
  let comparison = Fixture.at ~root:Tests "legacy/Graph/GraphFixture.v" Fixture.closed in
  print_s [%sexp (Layout.run [ legacy; fresh ] : unit Or_error.t)];
  print_s [%sexp (Layout.run [ legacy; fresh; comparison ] : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Error
     ("duplicate Rocq basename" (basename GraphFixture.v)
      (files (theories/Graph/GraphFixture.v tests/legacy/Graph/GraphFixture.v))))
    |}]
;;

let%expect_test "line limits warn for new files strictly above the boundary" =
  let text lines = List.init lines ~f:(fun _ -> "(* source *)") |> String.concat ~sep:"\n" in
  let at_limit = Fixture.at ~root:Theories "Base/BaseLimit.v" (text Layout.line_limit) in
  let over_limit = Fixture.at ~root:Tests "Base/BaseLongTest.v" (text (Layout.line_limit + 1)) in
  let legacy =
    Fixture.at ~root:Legacy_theories "Collections/CollectionsLong.v" (text (Layout.line_limit + 1))
  in
  let sources = [ at_limit; over_limit; legacy ] in
  print_s [%sexp (Layout.warnings sources : Layout.Warning.t list)];
  print_s [%sexp (Layout.run sources : unit Or_error.t)];
  [%expect
    {|
    (((file tests/Base/BaseLongTest.v) (lines 1501) (limit 1500)))
    (Ok ())
    |}]
;;

let%expect_test "Float boundaries inspect exact parsed imports in both namespaces" =
  List.iter
    [ "From Galois.Float Require Import FloatPrelude."
    ; "From Galois Require Import Float.FloatPrelude."
    ; "Require Export GaloisLegacy.Float.FloatPrelude."
    ; "From GaloisLegacy Require Import Float.FloatPrelude."
    ; "From Galois.FloatSpoof Require Import FloatPrelude."
    ; "From GaloisLegacy.FloatSpoof Require Import FloatPrelude."
    ; "(* From Galois.Float Require Import FloatPrelude. *)"
    ; {|Definition message := "From Galois.Float Require Import FloatPrelude.".|}
    ; "Fail From Galois.Float Require Import Missing."
    ; "Succeed From Galois.Float Require Import FloatPrelude."
    ]
    ~f:(fun text ->
      print_s [%sexp (Float_boundary.imports_float (Fixture.source text) : bool Or_error.t)]);
  [%expect
    {|
    (Ok true)
    (Ok true)
    (Ok true)
    (Ok true)
    (Ok false)
    (Ok false)
    (Ok false)
    (Ok false)
    (Ok false)
    (Ok false)
    |}]
;;

let%expect_test "Float paths alone never grant an axiom allowance" =
  List.iter [ Source.Root.Theories; Legacy_theories ] ~f:(fun root ->
    let source = Fixture.at ~root "Float/FloatFixture.v" Fixture.classical in
    print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Float/FloatFixture.v) (line 1) (claim (classical_claim))
      (problem "theorem depends on axioms: Classical_Prop.classic")))
    (Error
     ((file legacy/theories/Float/FloatFixture.v) (line 1)
      (claim (classical_claim))
      (problem "theorem depends on axioms: Classical_Prop.classic")))
    |}]
;;

let%expect_test "explicit Float clients replay approved axioms wherever the file lives" =
  let paths =
    [ ({ root = Theories; relative = "Graph/GraphFloat.v" } : Fixture.Path.t)
    ; { root = Examples; relative = "SsaFloat/ExamplesSsaFloat.v" }
    ; { root = Tests; relative = "Float/FloatTest.v" }
    ; { root = Tests; relative = "legacy/Float/FloatLegacyTest.v" }
    ; { root = Legacy_theories; relative = "Graph/GraphFloat.v" }
    ; { root = Legacy_examples; relative = Fixture.while_file }
    ; { root = Legacy_tests; relative = "Float/FloatTest.v" }
    ]
  in
  let result =
    Fixture.with_float_repository ~f:(fun repository ->
      List.map paths ~f:(fun ({ root; relative } : Fixture.Path.t) ->
        let namespace =
          if
            Source.Generation.equal (Source.Root.generation root) Legacy
            || String.is_prefix relative ~prefix:"legacy/"
          then "GaloisLegacy"
          else "Galois"
        in
        let imports = [%string "From %{namespace}.Float Require Import FloatPrelude.\n"] in
        let source = Fixture.at ~root relative (String.concat [ imports; Fixture.classical ]) in
        let%bind.Or_error () = Hygiene.run [ source ] in
        Claims.source ~repository source)
      |> Or_error.combine_errors_unit)
  in
  print_s [%sexp (result : unit Or_error.t)];
  [%expect {| (Ok ()) |}]
;;

let%expect_test "only differential tests may import the legacy library from new roots" =
  let text = "From GaloisLegacy.Graph Require Import GraphCore." in
  List.iter
    [ Fixture.at ~root:Theories "Graph/GraphClient.v" text
    ; Fixture.at ~root:Examples "Tutorial/ExamplesClient.v" text
    ; Fixture.at ~root:Tests "Graph/GraphTest.v" text
    ; Fixture.at ~root:Tests "legacy/Graph/GraphLegacyTest.v" text
    ]
    ~f:(fun source -> print_s [%sexp (Result.is_ok (Hygiene.run [ source ]) : bool)]);
  [%expect
    {|
    false
    false
    false
    true
    |}]
;;

let%expect_test "clean source ignores nested comments and doubled quotes in strings" =
  let text =
    {|(* Axiom bad : False. (* Theorem ghost : False. Admitted. *) *)
Definition message := "Admitted. "" Axiom bad. (* not a comment *)".
Theorem valid : True. Proof. exact I. Qed.|}
  in
  let source = Fixture.source text in
  print_s [%sexp (Hygiene.run [ source ] : unit Or_error.t)];
  print_s [%sexp (Claim.discover source : Claim.t list Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Ok (((name valid) (line 3))))
    |}]
;;

let%expect_test "proof escapes declarations and unsafe checking identify their file" =
  List.iter
    [ "Axiom bad : False."
    ; "Theorem bad : False. Proof. admit. Qed."
    ; "#[global] Instance bad : local."
    ; "Unset Guard Checking."
    ; "Extraction Language OCaml."
    ; "Print Assumptions valid."
    ; "From Flocq Require Import IEEE754.Binary."
    ; "Record dictionary := { carrier : Type }."
    ]
    ~f:(fun text -> print_s [%sexp (Hygiene.run [ Fixture.source text ] : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "forbidden proof escape or declaration: Axiom")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "forbidden proof escape or declaration: admit")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "global instance; dictionaries must be explicit")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "disabled kernel checking")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "theory extraction or query command belongs in a client or scratch file")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "theory extraction or query command belongs in a client or scratch file")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "dependency outside Stdlib/Galois/GaloisLegacy (Flocq requires Float)")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "record carrier Type field; parameterize the dictionary instead")))
    |}]
;;

let%expect_test "explicitly local instances are distinguished from an instance named local" =
  List.iter
    [ "Local Instance local_ok : True."
    ; "#[local] Instance attribute_ok : True."
    ; "Instance global_bad : local."
    ]
    ~f:(fun text -> print_s [%sexp (Hygiene.run [ Fixture.source text ] : unit Or_error.t)]);
  [%expect
    {|
    (Ok ())
    (Ok ())
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "global instance; dictionaries must be explicit")))
    |}]
;;

let%expect_test "malformed comments and strings fail discovery" =
  List.iter
    [ "(* unfinished"; "Definition x := \"unfinished"; "Theorem unfinished : True" ]
    ~f:(fun text ->
      print_s [%sexp (Lex.scan ~file:Fixture.file text : Lex.Sentence.t list Or_error.t)]);
  [%expect
    {|
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "unterminated Rocq comment")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "unterminated Rocq string")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "incomplete Rocq sentence (missing final period)")))
    |}]
;;

let%expect_test "layout checks duplicate names package prefixes and placement" =
  let clean = Fixture.source Fixture.closed in
  let duplicate =
    Fixture.source
      ~root:Legacy_tests
      ~file:"legacy/tests/Collections/CollectionsFixture.v"
      Fixture.closed
  in
  let wrong_prefix = Fixture.source ~file:"legacy/theories/Collections/Wrong.v" Fixture.closed in
  let wrong_package = Fixture.source ~package:"Unknown" Fixture.closed in
  print_s [%sexp (Layout.run [ clean ] : unit Or_error.t)];
  print_s [%sexp (Layout.run [ clean; duplicate ] : unit Or_error.t)];
  print_s [%sexp (Layout.run [ wrong_prefix; wrong_package ] : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Error
     ("duplicate Rocq basename" (basename CollectionsFixture.v)
      (files
       (legacy/theories/Collections/CollectionsFixture.v
        legacy/tests/Collections/CollectionsFixture.v))))
    (Error
     (((file legacy/theories/Collections/Wrong.v) (line 1) (claim ())
       (problem "Rocq basename must start with package Collections"))
      ((file legacy/theories/Collections/CollectionsFixture.v) (line 1)
       (claim ())
       (problem "source must be placed under its declared package directory"))))
    |}]
;;

let%expect_test "Rewrite theory and test files have valid package placement" =
  let sources =
    [ Fixture.source
        ~package:Source.rewrite_package
        ~file:"legacy/theories/Rewrite/RewriteSyntax.v"
        Fixture.closed
    ; Fixture.source
        ~root:Legacy_tests
        ~package:Source.rewrite_package
        ~file:"legacy/tests/Rewrite/RewriteSyntaxTest.v"
        Fixture.closed
    ]
  in
  print_s [%sexp (Layout.run sources : unit Or_error.t)];
  print_s [%sexp (Hygiene.run sources : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Ok ())
    |}]
;;

let%expect_test "Rewrite logical load path resolves a compiled theorem dependency" =
  let result =
    Query.with_workspace ~f:(fun repository ->
      let package = Source.rewrite_package in
      let directory = Filename.concat repository [%string "legacy/theories/%{package}"] in
      Core_unix.mkdir_p directory;
      let dependency = Filename.concat directory [%string "RewriteSyntax%{Source.extension}"] in
      Out_channel.write_all dependency ~data:Fixture.closed;
      let args = Query.load_paths repository in
      print_s
        [%sexp
          (List.map args ~f:(String.substr_replace_all ~pattern:repository ~with_:"<repository>")
           : string list)];
      let output = Filename.concat repository "Compile.log" in
      let%bind.Or_error _ =
        Query.run_process ~mode:Compile ~directory:repository ~args:(args @ [ dependency ]) ~output
      in
      let source =
        Fixture.source
          ~root:Legacy_tests
          ~package
          ~file:"legacy/tests/Rewrite/RewriteDependencyTest.v"
          {|From GaloisLegacy.Rewrite Require Import RewriteSyntax.
Theorem dependency_closed : True.
Proof.
  exact closed.
Qed.|}
      in
      let%bind.Or_error () = Hygiene.run [ source ] in
      Claims.source ~repository source)
  in
  print_s [%sexp (result : unit Or_error.t)];
  [%expect
    {|
    (-Q <repository>/legacy/theories/Rewrite GaloisLegacy.Rewrite -Q
     <repository>/examples Galois.Examples -Q <repository>/legacy/examples
     GaloisLegacy.Examples -Q <repository>/legacy/tests GaloisLegacy.Tests)
    (Ok ())
    |}]
;;

let%expect_test "theorem discovery tracks modules and generalizes sections" =
  let source =
    Fixture.source
      {|Module Outer. Section Variables. Context (P : Prop) (p : P).
#[local] Theorem generalized : P. Proof. exact p. Qed. End Variables.
Module Inner. End Inner. Module Alias := Inner. End Outer.|}
  in
  print_s [%sexp (Claim.discover source : Claim.t list Or_error.t)];
  print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)];
  [%expect
    {|
    (Ok (((name Outer.generalized) (line 2))))
    (Ok ())
    |}]
;;

let%expect_test "every authored source root discovers and inspects its theorems" =
  let module Discovery = struct
    type t =
      { file : Filename.t
      ; root : Source.Root.t
      ; package : string
      ; claims : Claim.t list
      }
    [@@deriving sexp_of]
  end
  in
  Fixture.with_repository ~f:(fun repository ->
    let sources = Source.discover repository |> Or_error.ok_exn in
    List.iter sources ~f:(fun ({ file; root; package; _ } as source : Source.t) ->
      let file = String.chop_prefix_exn file ~prefix:[%string "%{repository}/"] in
      let claims = Claim.discover source |> Or_error.ok_exn in
      print_s [%sexp ({ file; root; package; claims } : Discovery.t)]);
    print_s [%sexp (Claims.run ~repository sources : unit Or_error.t)]);
  [%expect
    {|
    ((file theories/Base/BaseFixture.v) (root Theories) (package Base)
     (claims (((name closed) (line 1)))))
    ((file examples/Tutorial/ExamplesTutorialFixture.v) (root Examples)
     (package Examples) (claims (((name closed) (line 1)))))
    ((file tests/Base/BaseTestFixture.v) (root Tests) (package Base)
     (claims (((name closed) (line 1)))))
    ((file tests/legacy/Base/BaseLegacyTestFixture.v) (root Tests) (package Base)
     (claims (((name closed) (line 1)))))
    ((file legacy/theories/Collections/CollectionsFixture.v)
     (root Legacy_theories) (package Collections)
     (claims (((name closed) (line 1)))))
    ((file legacy/examples/Ssa/ExamplesSsaFixture.v) (root Legacy_examples)
     (package Examples) (claims (((name closed) (line 1)))))
    ((file legacy/examples/While/ExamplesWhileFixture.v) (root Legacy_examples)
     (package Examples) (claims (((name closed) (line 1)))))
    ((file legacy/tests/Collections/CollectionsTestFixture.v) (root Legacy_tests)
     (package Collections) (claims (((name closed) (line 1)))))
    ((file legacy/tests/Examples/ExamplesTestFixture.v) (root Legacy_tests)
     (package Examples) (claims (((name closed) (line 1)))))
    (Ok ())
    |}]
;;

let%expect_test "kernel reports a closed theorem" =
  let source = Fixture.source Fixture.closed in
  print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)];
  [%expect {| (Ok ()) |}]
;;

let%expect_test "a non Float theorem cannot inherit any axiom" =
  let source = Fixture.source Fixture.classical in
  print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)];
  [%expect
    {|
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1)
      (claim (classical_claim))
      (problem "theorem depends on axioms: Classical_Prop.classic")))
    |}]
;;

let%expect_test "Float permits only the exact four qualified axiom identities" =
  Set.iter Query.allowed_axioms ~f:(fun name ->
    let line = [%string "Constant %{name}"] in
    print_s [%sexp (Query.resolve [ line ] : unit Or_error.t)]);
  let result =
    Fixture.with_float_repository ~f:(fun repository ->
      Claims.source ~repository (Fixture.float_source Fixture.reals))
  in
  print_s [%sexp (result : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Ok ())
    (Ok ())
    (Ok ())
    (Ok ())
    |}]
;;

let%expect_test "Float rejects an unexpected kernel reported axiom" =
  let source =
    Fixture.float_source
      "From Stdlib.Logic Require Import ProofIrrelevance. Theorem unrelated_claim : forall (P : \
       Prop) (p q : P), p = q. Proof. exact proof_irrelevance. Qed."
  in
  let result =
    Fixture.with_float_repository ~f:(fun repository -> Claims.source ~repository source)
  in
  print_s [%sexp (result : unit Or_error.t)];
  [%expect
    {|
    (Error
     (("Float assumptions inspection"
       (source.file legacy/theories/Collections/CollectionsFixture.v)
       (claims (((name unrelated_claim) (line 2)))))
      (("Float theorem assumption"
        (source.file legacy/theories/Collections/CollectionsFixture.v)
        (claim ((name unrelated_claim) (line 2))))
       ("unexpected Float axiom"
        (name Stdlib.Logic.ProofIrrelevance.proof_irrelevance)))))
    |}]
;;

let%expect_test "Float claims resolve classic and every prior foundation through the kernel" =
  List.iter
    [ Fixture.classical
    ; "From Stdlib.Reals Require Import ClassicalDedekindReals. Theorem forall_claim : forall (P : \
       nat -> Prop), (forall n, {P n} + {~ P n}) -> {n | ~ P n} + {forall n, P n}. Proof. exact \
       sig_forall_dec. Qed."
    ; "From Stdlib.Reals Require Import ClassicalDedekindReals. Theorem not_claim : forall P : \
       Prop, {~~ P} + {~ P}. Proof. exact sig_not_dec. Qed."
    ; "From Stdlib.Logic Require Import FunctionalExtensionality. Theorem ext_claim : forall (A : \
       Type) (B : A -> Type) (f g : forall x, B x), (forall x, f x = g x) -> f = g. Proof. exact \
       @functional_extensionality_dep. Qed."
    ]
    ~f:(fun text ->
      let result =
        Fixture.with_float_repository ~f:(fun repository ->
          Claims.source ~repository (Fixture.float_source text))
      in
      print_s [%sexp (result : unit Or_error.t)]);
  [%expect
    {|
    (Ok ())
    (Ok ())
    (Ok ())
    (Ok ())
    |}]
;;

let%expect_test "Float axiom resolution rejects ambiguous unrecognized and spoofed identities" =
  let classic = Query.classic_axiom in
  let identity = [%string "Constant %{classic}"] in
  List.iter
    [ []
    ; [ identity; identity ]
    ; [ [%string "Constructor %{classic}"] ]
    ; [ "Constant Classical_Prop.classic" ]
    ; [ [%string "Constant Top.%{classic}"] ]
    ; [ [%string "Constant %{classic}_spoof"] ]
    ]
    ~f:(fun lines -> print_s [%sexp (Query.resolve lines : unit Or_error.t)]);
  [%expect
    {|
    (Error ("ambiguous axiom identity" (lines ())))
    (Error
     ("ambiguous axiom identity"
      (lines
       ("Constant Stdlib.Logic.Classical_Prop.classic"
        "Constant Stdlib.Logic.Classical_Prop.classic"))))
    (Error
     ("unrecognized axiom identity"
      (line "Constructor Stdlib.Logic.Classical_Prop.classic")))
    (Error ("unexpected Float axiom" (name Classical_Prop.classic)))
    (Error
     ("unexpected Float axiom" (name Top.Stdlib.Logic.Classical_Prop.classic)))
    (Error
     ("unexpected Float axiom" (name Stdlib.Logic.Classical_Prop.classic_spoof)))
    |}]
;;

let%expect_test "actual non Float paths reject classic including Float tests" =
  let paths =
    [ ({ root = Legacy_theories; relative = "Collections/CollectionsFixture.v" } : Fixture.Path.t)
    ; ({ root = Legacy_examples; relative = Fixture.while_file } : Fixture.Path.t)
    ; ({ root = Legacy_examples; relative = Fixture.ssa_file } : Fixture.Path.t)
    ; ({ root = Legacy_tests; relative = "Float/FloatTestFixture.v" } : Fixture.Path.t)
    ]
  in
  List.iter paths ~f:(fun ({ root; relative } : Fixture.Path.t) ->
    let source = Fixture.at ~root relative Fixture.classical in
    print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1)
      (claim (classical_claim))
      (problem "theorem depends on axioms: Classical_Prop.classic")))
    (Error
     ((file legacy/examples/While/ExamplesWhileFixture.v) (line 1)
      (claim (classical_claim))
      (problem "theorem depends on axioms: Classical_Prop.classic")))
    (Error
     ((file legacy/examples/Ssa/ExamplesSsaFixture.v) (line 1)
      (claim (classical_claim))
      (problem "theorem depends on axioms: Classical_Prop.classic")))
    (Error
     ((file legacy/tests/Float/FloatTestFixture.v) (line 1)
      (claim (classical_claim))
      (problem "theorem depends on axioms: Classical_Prop.classic")))
    |}]
;;

let%expect_test "the Float allowance does not extend to examples or tests" =
  List.iter [ Source.Root.Legacy_examples; Source.Root.Legacy_tests ] ~f:(fun root ->
    let source = Fixture.source ~root ~package:Source.float_package Fixture.classical in
    print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1)
      (claim (classical_claim))
      (problem "theorem depends on axioms: Classical_Prop.classic")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1)
      (claim (classical_claim))
      (problem "theorem depends on axioms: Classical_Prop.classic")))
    |}]
;;

let%expect_test "incomplete and malformed assumption output cannot report closure" =
  print_s [%sexp (Query.blocks ~count:1 "" : string list list Or_error.t)];
  print_s [%sexp (Query.blocks ~count:1 (Query.delimiter 0) : string list list Or_error.t)];
  List.iter
    [ []; [ Query.axioms ]; [ "Error: cannot inspect claim" ]; [ Query.closed; Query.closed ] ]
    ~f:(fun lines -> print_s [%sexp (Query.assumption_names lines : string list Or_error.t)]);
  [%expect
    {|
    (Error "missing assumptions query delimiter")
    (Error ("incomplete assumptions query" (index 0)))
    (Error ("missing or unrecognized assumptions report" (lines ())))
    (Error ("unrecognized axiom report" (lines (Axioms:))))
    (Error
     ("missing or unrecognized assumptions report"
      (lines ("Error: cannot inspect claim"))))
    (Error
     ("missing or unrecognized assumptions report"
      (lines
       ("Closed under the global context" "Closed under the global context"))))
    |}]
;;

let%expect_test "a failed Rocq process never returns a successful report" =
  Query.with_workspace ~f:(fun directory ->
    let output = Filename.concat directory "Query.log" in
    let result =
      Query.run_process
        ~mode:Repl
        ~directory
        ~args:[ "-l"; "/tmp/galois-TOOL-1/absent-file.v" ]
        ~output
    in
    print_s [%sexp (result : string Or_error.t)];
    Ok ())
  |> Or_error.ok_exn;
  [%expect
    {|
    (Error
     ("Rocq assumptions query failed" (status (Error (Exit_non_zero 1)))
      (transcript
        "Error: Can't find file /tmp/galois-TOOL-1/absent-file.v.\
       \n\
       \n")))
    |}]
;;

let%expect_test "dictionary parameters are accepted and parenthesized carrier fields rejected" =
  List.iter
    [ "Record dictionary {A : Type} := { value : A }."
    ; "Record dictionary := { carrier : (Type) }."
    ]
    ~f:(fun text -> print_s [%sexp (Hygiene.run [ Fixture.source text ] : unit Or_error.t)]);
  [%expect
    {|
    (Ok ())
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "record carrier Type field; parameterize the dictionary instead")))
    |}]
;;

let%expect_test "claims reject disabled kernel checking before querying" =
  let source = Fixture.source "Unset Guard Checking. Theorem bad : True. Proof. exact I. Qed." in
  print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)];
  [%expect
    {|
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "disabled kernel checking")))
    |}]
;;

let%expect_test "invalid proof replay fails with source and theorem context" =
  let module Inspection = struct
    type t =
      | Unexpected_success
      | Rejected
      | Unexpected_error of Error.t
    [@@deriving sexp_of]
  end
  in
  let source = Fixture.source "Theorem invalid_claim : False. Proof. exact I. Qed." in
  let result : Inspection.t =
    match Claims.source ~repository:Fixture.repository source with
    | Ok () -> Unexpected_success
    | Error error ->
      let diagnostic = Error.to_string_hum error in
      if
        List.for_all
          [ "Rocq assumptions query failed"; Fixture.file; "invalid_claim" ]
          ~f:(fun substring -> String.is_substring diagnostic ~substring)
      then Rejected
      else Unexpected_error error
  in
  print_s [%sexp (result : Inspection.t)];
  [%expect {| Rejected |}]
;;

let%expect_test "quoted comment terminators cannot expose a fake theorem" =
  let source =
    Fixture.source
      {|(* "*)" Theorem ghost : False. (* nested *) "(*" *)
Theorem valid : True. Proof. exact I. Qed.|}
  in
  print_s [%sexp (Hygiene.run [ source ] : unit Or_error.t)];
  print_s [%sexp (Claim.discover source : Claim.t list Or_error.t)];
  print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Ok (((name valid) (line 2))))
    (Ok ())
    |}]
;;

let%expect_test "section assumptions generalize but global hypotheses are axioms" =
  List.iter
    [ "Section S. Context (P : Prop) (p : P). Theorem bound : P. Proof. exact p. Qed. End S."
    ; "Hypothesis global : True."
    ; "Module M. Variable global : Type. End M."
    ]
    ~f:(fun text -> print_s [%sexp (Hygiene.run [ Fixture.source text ] : unit Or_error.t)]);
  [%expect
    {|
    (Ok ())
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "global assumption; bind it in a Section or a theorem instead")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "global assumption; bind it in a Section or a theorem instead")))
    |}]
;;

let%expect_test "polymorphic record operations do not introduce carrier fields" =
  let source = Fixture.source "Record operations := { apply : forall {A : Type}, A -> A }." in
  print_s [%sexp (Hygiene.run [ source ] : unit Or_error.t)];
  [%expect {| (Ok ()) |}]
;;

let%expect_test "an aborted theorem cannot fall back to an imported closed constructor" =
  let aborted = Fixture.source "Theorem I : False. Abort." in
  let completed = Fixture.source "Theorem I : True. Proof. exact Logic.I. Qed." in
  print_s [%sexp (Claims.source ~repository:Fixture.repository aborted : unit Or_error.t)];
  print_s [%sexp (Claims.source ~repository:Fixture.repository completed : unit Or_error.t)];
  [%expect
    {|
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1)
      (claim (I)) (problem "aborted theorem has no proof to inspect")))
    (Ok ())
    |}]
;;

let%expect_test "claim identity must be the exact source constant" =
  print_s
    [%sexp
      (Query.claim_report ~name:"I" [ "Constructor Stdlib.Init.Logic.I"; Query.closed ]
       : string list Or_error.t)];
  print_s
    [%sexp
      (Claims.source
         ~repository:Fixture.repository
         (Fixture.source "Theorem I : True. Proof. exact Logic.I. Qed. Reset I.")
       : unit Or_error.t)];
  [%expect
    {|
    (Error
     ("claim does not resolve to the source declaration" (name I)
      (lines
       ("Constructor Stdlib.Init.Logic.I" "Closed under the global context"))))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "proof editing command can remove discovered declarations")))
    |}]
;;

let%expect_test "exact claim identities preserve assumption reports" =
  let name = "claim" in
  let full = [%string "Top.%{Query.qualified name}"] in
  let forms = [ [ [%string "Constant %{full}"] ]; [ "Constant"; full ] ] in
  List.iter forms ~f:(fun identity ->
    let reports =
      [ [ Query.closed ]
      ; []
      ; [ "malformed" ]
      ; [ Query.closed; Query.closed ]
      ; [ Query.axioms; "Example.axiom : forall x,"; "  x = x" ]
      ]
    in
    List.iter reports ~f:(fun report ->
      print_s [%sexp (Query.claim_report ~name (identity @ report) : string list Or_error.t)]));
  [%expect
    {|
    (Ok ())
    (Error ("missing or unrecognized assumptions report" (lines ())))
    (Error ("missing or unrecognized assumptions report" (lines (malformed))))
    (Error
     ("missing or unrecognized assumptions report"
      (lines
       ("Closed under the global context" "Closed under the global context"))))
    (Ok (Example.axiom))
    (Ok ())
    (Error ("missing or unrecognized assumptions report" (lines ())))
    (Error ("missing or unrecognized assumptions report" (lines (malformed))))
    (Error
     ("missing or unrecognized assumptions report"
      (lines
       ("Closed under the global context" "Closed under the global context"))))
    (Ok (Example.axiom))
    |}]
;;

let%expect_test "claim identities reject malformed and foreign lines" =
  let name = "claim" in
  let full = [%string "Top.%{Query.qualified name}"] in
  let identities = [ [ [%string "Constant %{full}"] ]; [ "Constant"; full ] ] in
  List.iter identities ~f:(fun identity ->
    let bad =
      [ identity @ [ "extra" ]
      ; "extra" :: identity
      ; List.map identity ~f:(fun line -> [%string " %{line}"])
      ; [ "Constant Top.Foreign.claim" ]
      ; [ "Constant"; "Top.Foreign.claim" ]
      ; [ "Constant claim" ]
      ; [ "Constant"; "claim" ]
      ; [ "Constant Top.GaloisAuditSource.clai" ]
      ; [ "Constant"; "Top.GaloisAuditSource.clai" ]
      ; [ [%string "Constant %{full}.suffix"] ]
      ; [ "Constant"; [%string "%{full}.suffix"] ]
      ; [ "Constant" ]
      ]
    in
    List.iter bad ~f:(fun lines ->
      print_s [%sexp (Result.is_error (Query.claim_report ~name (lines @ [ Query.closed ])) : bool)]));
  [%expect
    {|
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    |}]
;;

let%expect_test "wrapped identity passes axioms to the existing non Float policy" =
  let name = "claim" in
  let source = Fixture.source Fixture.closed in
  let claim = ({ name; line = 1 } : Claim.t) in
  List.iter
    [ [ [%string "Constant Top.%{Query.qualified name}"] ]
    ; [ "Constant"; [%string "Top.%{Query.qualified name}"] ]
    ]
    ~f:(fun identity ->
      let result =
        let%bind.Or_error names =
          Query.claim_report ~name (identity @ [ Query.axioms; "Example.axiom : True"; "  -> True" ])
        in
        Claims.check_names source claim names
      in
      print_s [%sexp (result : unit Or_error.t)];
      let float_source = Fixture.float_source Fixture.closed in
      let float_result =
        let%bind.Or_error names =
          Query.claim_report ~name (identity @ [ Query.axioms; "Example.axiom : True" ])
        in
        Claims.check_names float_source claim names
      in
      print_s [%sexp (float_result : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1)
      (claim (claim)) (problem "theorem depends on axioms: Example.axiom")))
    (Ok ())
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1)
      (claim (claim)) (problem "theorem depends on axioms: Example.axiom")))
    (Ok ())
    |}]
;;

let%expect_test "strict replay captures the long wrapped source identity" =
  let name = "graph_source_successor_correspondence_holds_with_a_wrapped_name" in
  let source = [%string "Theorem %{name} : True. Proof. exact I. Qed."] in
  let qualified = Query.qualified name in
  let command = [%string "Locate %{qualified}.\nPrint Assumptions %{qualified}."] in
  Fixture.with_repository ~f:(fun repository ->
    let transcript = Query.execute ~repository source [ command ] |> Or_error.ok_exn in
    print_string transcript;
    print_s [%sexp (Claims.source ~repository (Fixture.source source) : unit Or_error.t)]);
  [%expect
    {|
    __GALOIS_AUDIT_0__
    Constant
    Top.GaloisAuditSource.graph_source_successor_correspondence_holds_with_a_wrapped_name
    Closed under the global context
    __GALOIS_AUDIT_1__
    (Ok ())
    |}]
;;

let%expect_test "both source identity forms retain Float axiom resolution" =
  let name = "claim" in
  let claim = ({ name; line = 1 } : Claim.t) in
  let source = Fixture.float_source Fixture.closed in
  let axiom = "classic" in
  List.iter
    [ [ [%string "Constant Top.%{Query.qualified name}"] ]
    ; [ "Constant"; [%string "Top.%{Query.qualified name}"] ]
    ]
    ~f:(fun identity ->
      let assumptions =
        Query.claim_report ~name (identity @ [ Query.axioms; [%string "%{axiom} : True"] ])
        |> Or_error.ok_exn
      in
      let reports = [ ({ claim; assumptions } : Claims.Report.t) ] in
      List.iter [ Query.classic_axiom; "Foreign.classic" ] ~f:(fun resolved ->
        let transcript =
          String.concat
            ~sep:"\n"
            [ Query.delimiter 0; [%string "Constant %{resolved}"]; Query.delimiter 1 ]
        in
        print_s
          [%sexp
            (Result.is_ok (Claims.validate_float source ~reports ~axioms:[ axiom ] ~transcript)
             : bool)]));
  [%expect
    {|
    true
    false
    true
    false
    |}]
;;

let%expect_test "Program admission is rejected without any theorem roots" =
  let source = Fixture.source "Program Definition unfinished : False := _. Admit Obligations." in
  print_s [%sexp (Claim.discover source : Claim.t list Or_error.t)];
  print_s [%sexp (Hygiene.run [ source ] : unit Or_error.t)];
  print_s
    [%sexp
      (Hygiene.run
         [ Fixture.source {|(* Admit Obligations. *) Definition message := "Admit Obligations.".|} ]
       : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "admitted Program obligation")))
    (Ok ())
    |}]
;;

let%expect_test "unused axiom imports are rejected in qualified and split spellings" =
  let policy = Import_policy.load () |> Or_error.ok_exn in
  List.iter
    [ "From Stdlib.Logic Require Import Classical_Prop."
    ; "From Stdlib Require Import Logic.Classical_Prop."
    ; "Require Import Stdlib.Logic.Classical_Prop."
    ; "From Stdlib.Logic Require Import Classical."
    ; "From Stdlib.Logic Require Import FunctionalExtensionality ProofIrrelevance."
    ; "From Stdlib Require Import Classical_Prop."
    ; "From Stdlib.Reals Require Import Reals."
    ]
    ~f:(fun imports ->
      let source = Fixture.source (String.concat ~sep:" " [ imports; Fixture.closed ]) in
      print_s [%sexp (Hygiene.source ~policy source : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "axiom-bearing Stdlib import outside Float: Stdlib.Logic.Classical_Prop")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "axiom-bearing Stdlib import outside Float: Stdlib.Logic.Classical_Prop")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "axiom-bearing Stdlib import outside Float: Stdlib.Logic.Classical_Prop")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "axiom-bearing Stdlib import outside Float: Stdlib.Logic.Classical")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "axiom-bearing Stdlib import outside Float: Stdlib.Logic.FunctionalExtensionality")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "axiom-bearing Stdlib import outside Float: Stdlib.Classical_Prop")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "axiom-bearing Stdlib import outside Float: Stdlib.Reals.Reals")))
    |}]
;;

let%expect_test "constructive Stdlib imports and approved Float dependencies remain accepted" =
  let source =
    Fixture.source
      "From Stdlib.Lists Require Import List. From Stdlib.ZArith Require Import ZArith. From \
       Stdlib.Logic Require Import Eqdep_dec ProofIrrelevanceFacts. From Stdlib Require Import \
       List ZArith Lia. Require Import Stdlib.Lists.List."
  in
  let float = Fixture.source ~package:Source.float_package Fixture.reals in
  print_s [%sexp (Hygiene.run [ source; float ] : unit Or_error.t)];
  [%expect {| (Ok ()) |}]
;;

let%expect_test "failed closure cannot hide an aborted theorem followed by a replacement" =
  List.iter
    [ "Theorem I : False. Fail Qed. Abort. Definition I : True := Logic.I."
    ; "Theorem I : let p := False in p. Abort. Definition I : True := Logic.I."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Claims.source ~repository:Fixture.repository (Fixture.source text) : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1)
      (claim (I)) (problem "aborted theorem has no proof to inspect")))
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1)
      (claim (I)) (problem "aborted theorem has no proof to inspect")))
    |}]
;;

let%expect_test "unused classical import is a hygiene failure even for a kernel closed theorem" =
  let source =
    Fixture.source
      (String.concat
         ~sep:" "
         [ "From Stdlib.Logic Require Import Classical_Prop."; Fixture.closed ])
  in
  print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)];
  print_s [%sexp (Hygiene.run [ source ] : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Error
     ((file legacy/theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "axiom-bearing Stdlib import outside Float: Stdlib.Logic.Classical_Prop")))
    |}]
;;

let%expect_test "legacy examples and their computed tests retain the Examples prefix" =
  let sources = Fixture.examples Fixture.closed in
  print_s [%sexp (Layout.run sources : unit Or_error.t)];
  print_s [%sexp (Hygiene.run sources : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Ok ())
    |}]
;;

let%expect_test "legacy example paths reject language prefixes and wrong or unknown directories" =
  List.iter
    [ Fixture.at ~root:Legacy_examples "While/WhileWrong.v" Fixture.closed
    ; Fixture.at ~root:Legacy_examples "Ssa/SsaWrong.v" Fixture.closed
    ; Fixture.at ~root:Legacy_tests "Examples/SsaWrongTest.v" Fixture.closed
    ; Fixture.at ~root:Legacy_examples "Collections/ExamplesWrong.v" Fixture.closed
    ; Fixture.at ~root:Legacy_examples "Unknown/ExamplesUnknown.v" Fixture.closed
    ; Fixture.at ~root:Legacy_examples "ExamplesMisplaced.v" Fixture.closed
    ; Fixture.at ~root:Legacy_theories "Examples/ExamplesWrongTheory.v" Fixture.closed
    ; Fixture.at ~root:Legacy_tests "While/ExamplesWrongTest.v" Fixture.closed
    ; Fixture.at ~root:Legacy_tests "Unknown/ExamplesUnknownTest.v" Fixture.closed
    ; Fixture.at ~root:Legacy_theories "CollectionsMisplaced.v" Fixture.closed
    ; Fixture.at ~root:Legacy_tests "ExamplesMisplacedTest.v" Fixture.closed
    ]
    ~f:(fun source -> print_s [%sexp (Layout.run [ source ] : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file legacy/examples/While/WhileWrong.v) (line 1) (claim ())
      (problem "Rocq basename must start with package Examples")))
    (Error
     ((file legacy/examples/Ssa/SsaWrong.v) (line 1) (claim ())
      (problem "Rocq basename must start with package Examples")))
    (Error
     ((file legacy/tests/Examples/SsaWrongTest.v) (line 1) (claim ())
      (problem "Rocq basename must start with package Examples")))
    (Error
     ((file legacy/examples/Collections/ExamplesWrong.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    (Error
     ((file legacy/examples/Unknown/ExamplesUnknown.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    (Error
     ((file legacy/examples/ExamplesMisplaced.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    (Error
     ((file legacy/theories/Examples/ExamplesWrongTheory.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    (Error
     ((file legacy/tests/While/ExamplesWrongTest.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    (Error
     ((file legacy/tests/Unknown/ExamplesUnknownTest.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    (Error
     ((file legacy/theories/CollectionsMisplaced.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    (Error
     ((file legacy/tests/ExamplesMisplacedTest.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    |}]
;;

let%expect_test "legacy example basenames are unique across both client directories and tests" =
  let basename = "ExamplesDuplicate.v" in
  let sources =
    List.map Fixture.example_paths ~f:(fun ({ root; relative } : Fixture.Path.t) ->
      let relative = Filename.concat (Filename.dirname relative) basename in
      Fixture.at ~root relative Fixture.closed)
  in
  print_s [%sexp (Layout.run sources : unit Or_error.t)];
  [%expect
    {|
    (Error
     ("duplicate Rocq basename" (basename ExamplesDuplicate.v)
      (files
       (legacy/examples/While/ExamplesDuplicate.v
        legacy/examples/Ssa/ExamplesDuplicate.v
        legacy/tests/Examples/ExamplesDuplicate.v))))
    |}]
;;

let%expect_test "legacy examples retain theory hygiene and accept explicit Float imports" =
  List.iter
    [ "Print nat."
    ; "Extraction Language OCaml."
    ; "From GaloisLegacy.Float Require Import FloatFixture."
    ]
    ~f:(fun text ->
      List.iter
        (List.take (Fixture.examples text) 2)
        ~f:(fun source -> print_s [%sexp (Hygiene.run [ source ] : unit Or_error.t)]));
  [%expect
    {|
    (Error
     ((file legacy/examples/While/ExamplesWhileFixture.v) (line 1) (claim ())
      (problem
       "theory extraction or query command belongs in a client or scratch file")))
    (Error
     ((file legacy/examples/Ssa/ExamplesSsaFixture.v) (line 1) (claim ())
      (problem
       "theory extraction or query command belongs in a client or scratch file")))
    (Error
     ((file legacy/examples/While/ExamplesWhileFixture.v) (line 1) (claim ())
      (problem
       "theory extraction or query command belongs in a client or scratch file")))
    (Error
     ((file legacy/examples/Ssa/ExamplesSsaFixture.v) (line 1) (claim ())
      (problem
       "theory extraction or query command belongs in a client or scratch file")))
    (Ok ())
    (Ok ())
    |}]
;;

let%expect_test "legacy clients without Float imports reject the approved real axioms" =
  List.iter (Fixture.examples Fixture.reals) ~f:(fun source ->
    print_s [%sexp (Claim.discover source : Claim.t list Or_error.t)];
    print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)]);
  [%expect
    {|
    (Ok (((name real_claim) (line 1))))
    (Error
     ((file legacy/examples/While/ExamplesWhileFixture.v) (line 1)
      (claim (real_claim))
      (problem
       "theorem depends on axioms: ClassicalDedekindReals.sig_forall_dec, FunctionalExtensionality.functional_extensionality_dep")))
    (Ok (((name real_claim) (line 1))))
    (Error
     ((file legacy/examples/Ssa/ExamplesSsaFixture.v) (line 1)
      (claim (real_claim))
      (problem
       "theorem depends on axioms: ClassicalDedekindReals.sig_forall_dec, FunctionalExtensionality.functional_extensionality_dep")))
    (Ok (((name real_claim) (line 1))))
    (Error
     ((file legacy/tests/Examples/ExamplesTestFixture.v) (line 1)
      (claim (real_claim))
      (problem
       "theorem depends on axioms: ClassicalDedekindReals.sig_forall_dec, FunctionalExtensionality.functional_extensionality_dep")))
    |}]
;;

let%expect_test "legacy example and test logical module paths resolve compiled theorem dependencies"
  =
  let result =
    Query.with_workspace ~f:(fun repository ->
      let sources = Fixture.examples Fixture.closed in
      let args = Query.load_paths repository in
      let output = Filename.concat repository "Compile.log" in
      let%bind.Or_error () =
        List.fold_result sources ~init:() ~f:(fun () ({ file; source; _ } : Source.t) ->
          let file = Filename.concat repository file in
          Core_unix.mkdir_p (Filename.dirname file);
          Out_channel.write_all file ~data:source;
          let%map.Or_error _ =
            Query.run_process ~mode:Compile ~directory:repository ~args:(args @ [ file ]) ~output
          in
          ())
      in
      let linked =
        {|From GaloisLegacy.Examples.While Require Import ExamplesWhileFixture.
From GaloisLegacy.Examples.Ssa Require Import ExamplesSsaFixture.
From GaloisLegacy.Tests.Examples Require Import ExamplesTestFixture.
Theorem linked : True /\ True /\ True.
Proof.
  exact (conj ExamplesWhileFixture.closed
    (conj ExamplesSsaFixture.closed ExamplesTestFixture.closed)).
Qed.|}
      in
      let sources = Fixture.examples linked in
      let%bind.Or_error () = Layout.run sources in
      let%bind.Or_error () = Hygiene.run sources in
      Claims.run ~repository sources)
  in
  print_s [%sexp (result : unit Or_error.t)];
  [%expect {| (Ok ()) |}]
;;

let%expect_test "extraction rejects casts in any artifact including interfaces" =
  List.iter Extraction.artifacts ~f:(fun file ->
    print_s [%sexp (Extraction.inspect ~file "let unsafe = Obj . magic" : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ("forbidden extraction dependency" (file algorithms.ml)
      (spelling Obj.magic)))
    (Error
     ("forbidden extraction dependency" (file algorithms.mli)
      (spelling Obj.magic)))
    (Error
     ("forbidden extraction dependency" (file rules_solver.ml)
      (spelling Obj.magic)))
    (Error
     ("forbidden extraction dependency" (file rules_solver.mli)
      (spelling Obj.magic)))
    |}]
;;

let%expect_test "extraction inspects solver helpers and rejects universe enumeration" =
  List.iter [ "herbrand"; "tuple_words" ] ~f:(fun helper ->
    let source = [%string "let helper = %{helper}\nlet solve_program prog facts = helper"] in
    print_s
      [%sexp (Extraction.inspect ~file:Extraction.solver_implementation source : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ("forbidden extraction dependency" (file rules_solver.ml)
      (spelling herbrand)))
    (Error
     ("forbidden extraction dependency" (file rules_solver.ml)
      (spelling tuple_words)))
    |}]
;;

let%expect_test "extraction inventory and unreadable outputs fail closed" =
  print_s [%sexp (Extraction.run [] : unit Or_error.t)];
  let files = List.map Extraction.artifacts ~f:(Filename.concat "/dev/null") in
  let result = Extraction.run files in
  print_s [%message (Result.is_error result : bool)];
  [%expect
    {|
    (Error
     ("incomplete extraction inventory" (actual ())
      (expected (algorithms.ml algorithms.mli rules_solver.ml rules_solver.mli))))
    ("Result.is_error result" true)
    |}]
;;

let%expect_test "finite universe erasure is checked in the generated solver signature" =
  let signature =
    "val finite_powerset_lattice : 'a1 encoding -> 'a1 finite_set lattice\n\
     val solve_program : 'a1 program -> 'a1 ground_atom list -> 'a1 database option"
  in
  print_s [%sexp (Extraction.inspect ~file:Extraction.solver_interface signature : unit Or_error.t)];
  let unerased =
    String.substr_replace_all signature ~pattern:"encoding ->" ~with_:"encoding -> 'a1 list ->"
  in
  print_s [%sexp (Extraction.inspect ~file:Extraction.solver_interface unerased : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Error
     ("missing extraction declaration" (file rules_solver.mli)
      (spelling valfinite_powerset_lattice:'a1encoding->'a1finite_setlattice)))
    |}]
;;

let%expect_test "claims worker setting accepts only one and two" =
  List.iter [ None; Some "1"; Some "2"; Some ""; Some "01"; Some "3" ] ~f:(fun value ->
    print_s [%sexp (Jobs.parse value : Jobs.t Or_error.t)]);
  [%expect
    {|
    (Ok Two)
    (Ok One)
    (Ok Two)
    (Error
     ("invalid claims worker setting" (variable GALOIS_CHECK_JOBS) (value "")))
    (Error
     ("invalid claims worker setting" (variable GALOIS_CHECK_JOBS) (value 01)))
    (Error
     ("invalid claims worker setting" (variable GALOIS_CHECK_JOBS) (value 3)))
    |}]
;;

let%expect_test "claims worker results retain all failures in source order" =
  let fail item = Or_error.error_s [%message "source failure" (item : int)] in
  List.iter [ Jobs.One; Jobs.Two ] ~f:(fun jobs ->
    print_s [%sexp (Claims.run_workers ~jobs ~f:fail [] : unit Or_error.t)];
    print_s [%sexp (Claims.run_workers ~jobs ~f:fail [ 1; 2; 3 ] : unit Or_error.t)]);
  [%expect
    {|
    (Ok ())
    (Error
     (("source failure" (item 1)) ("source failure" (item 2))
      ("source failure" (item 3))))
    (Ok ())
    (Error
     (("source failure" (item 1)) ("source failure" (item 2))
      ("source failure" (item 3))))
    |}]
;;

let%expect_test "two workers can finish out of order without reordering errors" =
  let lock = Caml_threads.Mutex.create () in
  let condition = Caml_threads.Condition.create () in
  (* The condition forces the first item to wait until the second has finished. *)
  let active = ref 0 in
  let maximum = ref 0 in
  let first_started = ref false in
  let second_done = ref false in
  let completed = ref [] in
  let run item =
    Caml_threads.Mutex.lock lock;
    Int.incr active;
    maximum := Int.max !maximum !active;
    if item = 1
    then (
      first_started := true;
      Caml_threads.Condition.signal condition);
    while item = 2 && not !first_started do
      Caml_threads.Condition.wait condition lock
    done;
    while item = 1 && not !second_done do
      Caml_threads.Condition.wait condition lock
    done;
    completed := item :: !completed;
    Int.decr active;
    if item = 2
    then (
      second_done := true;
      Caml_threads.Condition.signal condition);
    Caml_threads.Mutex.unlock lock;
    Or_error.error_s [%message "source failure" (item : int)]
  in
  let result = Claims.run_workers ~jobs:Two ~f:run [ 1; 2 ] in
  print_s [%message (!maximum : int) (List.rev !completed : int list)];
  print_s [%sexp (result : unit Or_error.t)];
  [%expect
    {|
    ((!maximum 2) ("List.rev (!completed)" (2 1)))
    (Error (("source failure" (item 1)) ("source failure" (item 2))))
    |}]
;;

let%expect_test "one worker visits every item sequentially" =
  let active = ref 0 in
  let maximum = ref 0 in
  let visited = ref [] in
  let run item =
    Int.incr active;
    maximum := Int.max !maximum !active;
    visited := item :: !visited;
    Int.decr active;
    Ok ()
  in
  let result = Claims.run_workers ~jobs:One ~f:run [ 1; 2; 3 ] in
  let visited = List.rev !visited in
  print_s [%message (!maximum : int) (visited : int list) (result : unit Or_error.t)];
  [%expect {| ((!maximum 1) (visited (1 2 3)) (result (Ok ()))) |}]
;;

let%expect_test "invalid worker setting affects claims but not other audits" =
  let previous = Sys.getenv Jobs.variable in
  Exn.protect
    ~f:(fun () ->
      Core_unix.putenv ~key:Jobs.variable ~data:"invalid";
      Fixture.with_repository ~f:(fun repository ->
        List.iter [ Audit.Claims; Hygiene; Layout ] ~f:(fun audit ->
          let result = Result.is_error (run ~repository [ audit ]) in
          print_s [%message (audit : Audit.t) (result : bool)]);
        print_s [%sexp (Result.is_error (Extraction.run []) : bool)]))
    ~finally:(fun () ->
      match previous with
      | None -> Core_unix.unsetenv Jobs.variable
      | Some value -> Core_unix.putenv ~key:Jobs.variable ~data:value);
  [%expect
    {|
    ((audit Claims) (result true))
    ((audit Hygiene) (result false))
    ((audit Layout) (result false))
    true
    |}]
;;

let%expect_test "workspace cleanup retains operation and cleanup failures" =
  let directory = ref "" in
  let result =
    Query.with_workspace ~f:(fun path ->
      directory := path;
      Out_channel.write_all (Filename.concat path "held") ~data:"held";
      Core_unix.chmod path ~perm:0;
      Or_error.error_string "primary failure")
  in
  Core_unix.chmod !directory ~perm:0o700;
  let cleaned = Query.remove_workspace !directory in
  let cancelled = Atomic.get Cancellation.requested in
  Atomic.set Cancellation.requested false;
  let text = Result.error result |> Option.value_exn |> Error.to_string_hum in
  let primary = String.is_substring text ~substring:"primary failure" in
  let cleanup = String.is_substring text ~substring:!directory in
  print_s
    [%message (primary : bool) (cleanup : bool) (cancelled : bool) (cleaned : unit Or_error.t)];
  [%expect
    {|
    ((primary true) (cleanup true) (cancelled true) (cleaned (Ok ())))
    |}]
;;

let%expect_test "process spawn failure cancels coverage and cleans its workspace" =
  let previous = Sys.getenv "PATH" in
  let result =
    Exn.protect
      ~f:(fun () ->
        Core_unix.putenv ~key:"PATH" ~data:"";
        Query.with_workspace ~f:(fun directory ->
          let output = Filename.concat directory "Query.log" in
          Query.run_process ~mode:Repl ~directory ~args:[] ~output))
      ~finally:(fun () ->
        match previous with
        | None -> Core_unix.unsetenv "PATH"
        | Some value -> Core_unix.putenv ~key:"PATH" ~data:value)
  in
  let cancelled = Atomic.get Cancellation.requested in
  Atomic.set Cancellation.requested false;
  let text = Result.error result |> Option.value_exn |> Error.to_string_hum in
  let fatal = String.is_substring text ~substring:"fatal claims orchestration failure" in
  print_s [%message (fatal : bool) (cancelled : bool)];
  [%expect {| ((fatal true) (cancelled true)) |}]
;;

let%expect_test "fatal worker exception reports incomplete coverage" =
  let run item = if item = 1 then raise_s [%message "worker exception"] else Ok () in
  let result = Claims.run_workers ~jobs:One ~f:run [ 1; 2 ] in
  Atomic.set Cancellation.requested false;
  let text = Result.error result |> Option.value_exn |> Error.to_string_hum in
  let exception_seen = String.is_substring text ~substring:"worker exception" in
  let incomplete = String.is_substring text ~substring:"incomplete" in
  print_s [%message (exception_seen : bool) (incomplete : bool)];
  [%expect
    {|
    ((exception_seen true) (incomplete true))
    |}]
;;

let%expect_test "cost lint rejects computational count observations and record construction" =
  List.iter
    [ "Definition bad_c := Cost.ticks (Cost.ret true)."
    ; "Definition bad_c := Cost.mk true 0."
    ; "Definition clean_c := Cost.ret true."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational Cost.ticks outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "cost record construction outside Cost")))
    (Ok ())
    |}]
;;

let%expect_test "cost lint distinguishes record matches from value matches" =
  List.iter
    [ "Definition bad_c (m : Cost.t nat) := match m with x => x end."
    ; "Definition bad_c := let m := Cost.ret true in match m with x => x end."
    ; "Definition bad_c := match other_c true with x => x end."
    ; "Definition clean_c (m : Cost.t nat) := match Cost.value m with x => Cost.ret x end."
    ; "Definition clean_c (f : nat -> Cost.t nat) := match Cost.value (f 0) with x => Cost.ret x \
       end."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Examples "Tutorial/ExamplesCost.v" text)
           : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file examples/Tutorial/ExamplesCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file examples/Tutorial/ExamplesCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file examples/Tutorial/ExamplesCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Ok ())
    (Ok ())
    |}]
;;

let%expect_test "cost lint allows theorem statements proofs Prop laws and the owning package" =
  let text =
    {|Definition law (m : Cost.t nat) : Prop := Cost.ticks m = 0.
Record component_cost_laws (f : nat -> Cost.t nat) : Prop :=
  { bounded : forall n, Cost.ticks (f n) <= 7 }.
Lemma statement (m : Cost.t nat) : Cost.ticks m = Cost.ticks m.
Proof. destruct m. reflexivity. Qed.
Theorem named : True. Proof. pose (Cost.mk true 0). exact I. Qed.
Definition law_proof : True. Proof. pose (Cost.ticks (Cost.ret true)). exact I. Defined.
Definition clean_c := Cost.ret true.
(* Cost.ticks (Cost.mk true 0) *)
Definition message := "Cost.ticks (Cost.mk true 0)".|}
  in
  print_s
    [%sexp (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)];
  print_s
    [%sexp
      (Cost_lint.source
         (Fixture.at ~root:Theories "Cost/CostFixture.v" "Definition primitive := Cost.mk true 0.")
       : unit Or_error.t)];
  print_s
    [%sexp
      (Cost_lint.source
         (Fixture.at
            ~root:Theories
            "Base/BaseCost.v"
            "Definition bad_c (P : Prop) := Cost.ticks (Cost.ret true).")
       : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Ok ())
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational Cost.ticks outside Cost")))
    |}]
;;

let%expect_test "cost lint resumes after proofs and does not exempt computational Prop arguments" =
  let text =
    "Lemma fine : True. Proof. exact I. Qed.\n\
     Definition bad_c (P : Prop) := Cost.ticks (Cost.ret true)."
  in
  print_s
    [%sexp (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)];
  [%expect
    {|
    (Error
     ((file theories/Base/BaseCost.v) (line 2) (claim ())
      (problem "computational Cost.ticks outside Cost")))
    |}]
;;

let%expect_test "cost lint forbids the plain twin in every costed body" =
  List.iter
    [ "Definition f := 0. Definition f_c := Cost.ret (f 0)."
    ; "Definition g_c := Cost.ret (f 0). Definition f_c := Cost.ret 0. Definition f := 0."
    ; "Definition f_c := Cost.ret 0. Definition f := Cost.value f_c. Definition g_c := f_c."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: f")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: f")))
    (Ok ())
    |}]
;;

let%expect_test "cost lint distinguishes local values from record aliases" =
  List.iter
    [ "Definition clean_c m := let v := Cost.value m in match v with x => Cost.ret x end."
    ; "Definition bad_c (m : Cost.t nat) := let alias := m in match alias with x => x end."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Ok ())
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    |}]
;;

let%expect_test "cost lint checks grouped binders and computational signatures" =
  List.iter
    [ "Definition bad_c (m n : Cost.t nat) := match m with x => x end."
    ; "Definition bad_c (n : Fin.t (N.to_nat (Cost.ticks m))) := Cost.ret n."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational Cost.ticks outside Cost")))
    |}]
;;

let%expect_test "cost lint rejects uncharged qualified list operations" =
  List.iter
    [ "Definition bad_c xs := Cost.ret (List.map f xs)."; "Definition clean_c xs := map_c f xs." ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "uncharged list operation in costed body: List.map")))
    (Ok ())
    |}]
;;

let%expect_test "cost lint separates return annotations from record binders" =
  List.iter
    [ "Fixpoint walk_c n : Cost.t nat := match n with O => Cost.ret O | S k => walk_c k end."
    ; "Definition rows_c xs : Cost.t (list nat) := match xs with [] => Cost.ret [] | x :: xs => \
       Cost.ret xs end."
    ; "Definition run_c (f : nat -> Cost.t nat) n : Cost.t nat := match n with O => f O | S k \
       => f k end."
    ; "Definition bad_c (m n : Cost.t nat) k : Cost.t nat := match n with x => x end."
    ; "Definition bad_c (m : (Cost.t nat)) n : Cost.t nat := match (m) with x => x end."
    ; "Definition bad_c next_c := match next_c O with x => x end."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Ok ())
    (Ok ())
    (Ok ())
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    |}]
;;

let%expect_test "cost lint recognizes Prop codomains without exempting Prop domains" =
  List.iter
    [ "Inductive bounded : nat -> Cost.t nat -> Prop := B m : Cost.ticks m = 0 -> bounded 0 m."
    ; "Definition law : nat -> Prop := fun n => Cost.ticks (Cost.ret n) = 0."
    ; "Definition law : (nat -> Prop) := fun n => Cost.ticks (Cost.ret n) = 0."
    ; "Definition bad : Prop -> nat := fun P => Cost.ticks (Cost.ret O)."
    ; "Definition bad : (Prop -> nat) := fun P => Cost.ticks (Cost.ret O)."
    ; "Definition bad (P : nat -> Prop) : nat := Cost.ticks (Cost.ret O)."
    ; "Inductive bounded : nat -> Prop := B m : Cost.ticks m = 0 -> bounded 0. \
       Definition bad_c := Cost.ticks (Cost.ret O)."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Ok ())
    (Ok ())
    (Ok ())
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational Cost.ticks outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational Cost.ticks outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational Cost.ticks outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational Cost.ticks outside Cost")))
    |}]
;;

let%expect_test "cost lint resolves twin references in their lexical module namespace" =
  List.iter
    [ "Module Local. Definition empty_c := Cost.ret Other.empty. \
       Definition empty := Cost.value empty_c. End Local."
    ; "Module Jump. Definition rows x := x. Definition rows_c x := Cost.ret x. End Jump. \
       Definition bad_c x := Cost.ret (Jump.rows x)."
    ; "Module Jump. Definition rows x := x. Definition rows_c x := Cost.ret x. \
       Definition bad_c x := Cost.ret (rows x). End Jump."
    ; "Module A. Definition f x := x. Definition f_c x := Cost.ret x. End A. \
       Module B. Definition f x := x. Definition run_c x := Cost.ret (f x). End B."
    ; "Module A. Definition f x := x. Definition f_c x := Cost.ret x. \
       Module B. Definition bad_c x := Cost.ret (f x). End B. End A."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Ok ())
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: Jump.rows")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: rows")))
    (Ok ())
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: f")))
    |}]
;;

let%expect_test "cost lint permits literal constants without exempting zero argument work" =
  List.iter
    [ "Definition nil {A} : list A := []. Definition nil_c {A} := Cost.ret (@nil A)."
    ; "Definition nil {A} : list A := []. Definition nil_c {A} := Cost.ret nil."
    ; "Definition hidden := List.rev xs. Definition hidden_c := Cost.ret hidden."
    ; "Definition hidden := fun xs => List.rev xs. Definition hidden_c := Cost.ret hidden."
    ; "Definition f xs := []. Definition f_c xs := Cost.ret (f xs)."
    ; "Definition f := 0. Definition f_c := Cost.ret (f 0)."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: nil")))
    (Ok ())
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: hidden")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: hidden")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: f")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: f")))
    |}]
;;

let%expect_test "cost lint scopes monadic let lambda and pattern values" =
  List.iter
    [ "Definition rows x := x. Definition rows_c x := Cost.ret x. \
       Definition run_c x := let* rows := rows_c x in Cost.ret rows."
    ; "Definition f x := x. Definition f_c x := Cost.ret x. \
       Definition run_c f := Cost.ret (f 0)."
    ; "Definition f x := x. Definition f_c x := Cost.ret x. \
       Definition run_c := Cost.map (fun f => f) (Cost.ret 0)."
    ; "Definition f x := x. Definition f_c x := Cost.ret x. \
       Definition run_c xs := match xs with Some f => Cost.ret f | None => Cost.ret 0 end."
    ; "Definition f x := x. Definition f_c x := Cost.ret x. \
       Definition bad_c := (let* f := Cost.ret 0 in Cost.ret f) ;; Cost.ret (f 0)."
    ; "Definition f x := x. Definition f_c x := Cost.ret x. \
       Definition bad_c := Cost.map (fun f => f) (Cost.ret (f 0))."
    ; "Definition f x := x. Definition f_c x := Cost.ret x. \
       Definition bad_c xs := match xs with Some f => Cost.ret f | None => Cost.ret (f 0) end."
    ; "Module M. Definition f x := x. Definition f_c x := Cost.ret x. End M. \
       Definition bad_c := let* f := Cost.ret 0 in Cost.ret (M.f f)."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Ok ())
    (Ok ())
    (Ok ())
    (Ok ())
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: f")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: f")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: f")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: M.f")))
    |}]
;;

let%expect_test "cost lint keeps record aliases scoped separately from monadic values" =
  List.iter
    [ "Definition run_c (m : Cost.t nat) := let* m := m in match m with x => Cost.ret x end."
    ; "Definition run_c (m : Cost.t nat) := Cost.map (fun m => match m with x => x end) m."
    ; "Definition bad_c (m : Cost.t nat) := let alias := m in match alias with x => x end."
    ; "Definition bad_c := let m : Cost.t nat := other_c O in match m with x => x end."
    ; "Definition bad_c (m : Cost.t nat) := \
       (let* m := m in Cost.ret m) ;; match m with x => x end."
    ; "Definition bad_c (m : Cost.t nat) := \
       Cost.map (fun m => m) (match m with x => x end)."
    ; "Definition bad_c := Cost.map (fun (m n : Cost.t nat) => match n with x => x end) input."
    ; "Definition bad_c (m : Cost.t nat) (n : Fin.t (N.to_nat (Cost.ticks m))) := Cost.ret n."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Ok ())
    (Ok ())
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational Cost.ticks outside Cost")))
    |}]
;;

let%expect_test "cost lint never treats a literal lift charge as evidence for a leaf" =
  List.iter
    [ "Definition code x := x. Definition code_c := Cost.lift (fun _ => 1) code."
    ; "Definition scan xs := List.map f xs. Definition scan_c := Cost.lift (fun _ => 1) scan."
    ; "Definition bad_c xs := Cost.lift (fun _ => 1) (List.map f) xs."
    ; "Definition scan xs := List.map f xs. Definition scan_c xs := Cost.step ;; \
       Cost.ret (scan xs)."
    ; "Definition adapter_c f x := Cost.lift (fun _ => 1) f x."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: code")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: scan")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "uncharged list operation in costed body: List.map")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: scan")))
    (Ok ())
    |}]
;;

let%expect_test "cost lint never binds qualified constructor path components" =
  List.iter
    [ "Module Tag. Inductive t := m. End Tag. \
       Definition bad_c (m : Cost.t nat) (tag : Tag.t) := \
       match tag with | Tag.m => match m with r => r end end."
    ; "Module Tag. Inductive t := f. End Tag. \
       Definition f (xs : list nat) := xs. Definition f_c xs := Cost.ret xs. \
       Definition bad_c (tag : Tag.t) xs := match tag with | Tag.f => Cost.ret (f xs) end."
    ; "Module Tag. Inductive t := Wrap (n : nat). End Tag. \
       Definition run_c (m : Cost.t nat) (tag : Tag.t) := \
       match tag with | Tag.Wrap m => match m with O => Cost.ret O | S k => Cost.ret k end end."
    ; "Module Tag. Inductive t := Wrap (n : nat). End Tag. \
       Definition f x := x. Definition f_c x := Cost.ret x. \
       Definition run_c (tag : Tag.t) := match tag with | Tag.Wrap f => Cost.ret f end."
    ; "Module Tag. Inductive t := Wrap (n : nat) | Empty. End Tag. \
       Definition bad_c (m : Cost.t nat) (tag : Tag.t) := \
       match tag with | Tag.Wrap m => Cost.ret m | Tag.Empty => match m with r => r end end."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: f")))
    (Ok ())
    (Ok ())
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    |}]
;;

let%expect_test "cost lint reads mixed lambda binder sequences in order" =
  List.iter
    [ "Definition bad_c : nat -> Cost.t nat -> Cost.t nat := \
       fun x (m : Cost.t nat) => match m with r => r end."
    ; "Definition bad_c := fun (x : nat) y (m n : Cost.t nat) => match n with r => r end."
    ; "Definition run_c (m : Cost.t nat) := \
       fun x m => match m with O => Cost.ret x | S k => Cost.ret k end."
    ; "Definition run_c (m : Cost.t nat) := \
       fun x (m : nat) => match m with O => Cost.ret x | S k => Cost.ret k end."
    ; "Definition run_c (m : Cost.t nat) := \
       fun (x : nat) m (n : nat) => match m with O => Cost.ret x | S k => Cost.ret n end."
    ; "Definition f x := x. Definition f_c x := Cost.ret x. \
       Definition run_c := fun x (f : nat -> nat) => Cost.ret (f x)."
    ; "Definition run_c := fun x y : nat => Cost.ret (x + y)."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Ok ())
    (Ok ())
    (Ok ())
    (Ok ())
    (Ok ())
    |}]
;;

let%expect_test "cost lint prefers visible names while discovering twins across the file" =
  List.iter
    [ "Module A. Definition f (xs : list nat) := xs. \
       Definition f_c (xs : list nat) := Cost.ret xs. Module B. \
       Definition bad_c (xs : list nat) := Cost.ret (f xs). \
       Definition f (xs : list nat) := xs. End B. End A."
    ; "Module A. Definition f (xs : list nat) := xs. \
       Definition f_c (xs : list nat) := Cost.ret xs. Module B. \
       Definition f (xs : list nat) := xs. \
       Definition run_c (xs : list nat) := Cost.ret (f xs). End B. End A."
    ; "Module A. Definition f (xs : list nat) := xs. \
       Definition f_c (xs : list nat) := Cost.ret xs. Module B. \
       Definition f (xs : list nat) := xs. \
       Definition bad_c (xs : list nat) := Cost.ret (f xs). \
       Definition f_c xs := Cost.ret xs. End B. End A."
    ; "Definition f (xs : list nat) := xs. \
       Definition bad_c xs := Cost.ret (f xs). Definition f_c xs := Cost.ret xs."
    ; "Definition bad_c xs := Cost.ret (f xs). \
       Definition f (xs : list nat) := xs. Definition f_c xs := Cost.ret xs."
    ; "Module A. Definition f (xs : list nat) := xs. \
       Definition f_c xs := Cost.ret xs. Module B. \
       Definition bad_c xs := Cost.ret (A.f xs). \
       Definition f (xs : list nat) := xs. End B. End A."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: f")))
    (Ok ())
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: f")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: f")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: f")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "plain function in costed body: A.f")))
    |}]
;;

let%expect_test "cost lint checks annotations before introducing their binders" =
  List.iter
    [ "Definition bad_c (m : Cost.t nat) := \
       let n : (match m with r => nat end) := 0 in Cost.ret n."
    ; "Definition bad_c (m : Cost.t nat) := \
       let m : (match m with r => nat end) := 0 in Cost.ret m."
    ; "Definition bad_c (m : Cost.t nat) := \
       fun (n : (match m with r => nat end)) => Cost.ret n."
    ; "Definition bad_c (m : Cost.t nat) := \
       fun x (m : (match m with r => nat end)) => Cost.ret x."
    ; "Definition bad_c (m : Cost.t nat) := \
       fun x (n : (match m with r => nat end)) (m : nat) => Cost.ret x."
    ; "Definition run_c (m : Cost.t nat) := \
       fun x (m : nat) (n : (match m with r => nat end)) => Cost.ret x."
    ; "Definition run_c (m : Cost.t nat) := \
       let m : nat := 0 in let n : (match m with r => nat end) := 0 in Cost.ret n."
    ; "Definition run_c (m : Cost.t nat) := \
       let* m := m in let n : (match m with r => nat end) := 0 in Cost.ret n."
    ; "Definition bad_c (m : Cost.t nat) (n : (match m with r => nat end)) := Cost.ret n."
    ; "Definition bad_c (m : Cost.t nat) : (match m with r => nat end) := 0."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Cost_lint.source (Fixture.at ~root:Theories "Base/BaseCost.v" text) : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Ok ())
    (Ok ())
    (Ok ())
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    (Error
     ((file theories/Base/BaseCost.v) (line 1) (claim ())
      (problem "computational match on Cost.t outside Cost")))
    |}]
;;

let%expect_test "extraction rejects the exact cost sentinel in implementation and interface" =
  List.iter [ "cost_erased.ml"; "cost_erased.mli" ] ~f:(fun file ->
    List.iter
      [ {|let bad = failwith "GALOIS_COST_TICKS"|}
      ; {|(* GALOIS_COST_TICKS *)|}
      ; {|let clean = "GALOIS_COST_ TICKS"|}
      ; {|let clean = Galois_cost.value|}
      ]
      ~f:(fun source -> print_s [%sexp (Extraction.inspect ~file source : unit Or_error.t)]));
  [%expect
    {|
    (Error ("cost observation leaked into extraction" (file cost_erased.ml)))
    (Error ("cost observation leaked into extraction" (file cost_erased.ml)))
    (Ok ())
    (Ok ())
    (Error ("cost observation leaked into extraction" (file cost_erased.mli)))
    (Error ("cost observation leaked into extraction" (file cost_erased.mli)))
    (Ok ())
    (Ok ())
    |}]
;;
