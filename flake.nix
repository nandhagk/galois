{
  description = "Galois: general, composable program analyses in Rocq";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/c9fe7d12cd78d1adcd12dd15e24432dde5b155a0";
  inputs.argent.url = "github:nandhagk/argent/23341be2dec5be487f52054f7bc492df40c8eeda";
  inputs.argent.inputs.nixpkgs.follows = "nixpkgs";

  outputs =
    { nixpkgs, argent, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-darwin"
      ];
      pkgsFor = system: import nixpkgs { inherit system; };
    in
    {
      devShells = nixpkgs.lib.genAttrs systems (system: {
        default = (import ./nix { pkgs = pkgsFor system; argent = argent.packages.${system}.default; }).devShell;
        session = (import ./nix { pkgs = pkgsFor system; argent = argent.packages.${system}.default; }).sessionShell;
      });
      formatter = nixpkgs.lib.genAttrs systems (system: (pkgsFor system).nixfmt);
    };
}
