#!/usr/bin/env perl
use strict;
use warnings;

# Glob offsets identify declarations and resolved module references.
my (%admitted, @copies);
for my $source (@ARGV) {
    (my $glob = $source) =~ s{^theories/}{_build/default/theories/};
    $glob =~ s/\.v$/.glob/;
    open my $src, '<', $source or die "$source: $!\n";
    local $/;
    my $text = <$src>;
    open my $metadata, '<', $glob or die "$glob: $!\n";
    my $data = <$metadata>;
    my ($unit) = $data =~ /^F([^\n]+)$/m;
    defined $unit or die "$glob: missing logical name\n";
    my (@declarations, %references, %modules);
    while ($data =~ /^R(\d+):\d+ (\S+) (\S+) <> mod$/mg) {
        $references{$1} = $3 eq '<>' ? $2 : "$2.$3";
    }
    while ($data =~ /^mod (\d+):\d+ (\S+) \S+$/mg) {
        $modules{$1} = $2;
    }
    while ($data =~ /^(prf|def) (\d+):\d+ (\S+) (\S+)$/mg) {
        push @declarations, [$2, $3, $4];
    }
    @declarations = sort { $a->[0] <=> $b->[0] } @declarations;
    # Preserve byte offsets while removing nested comments and strings.
    my $clean = $text;
    my ($depth, $string) = (0, 0);
    for (my $i = 0; $i < length $text; $i++) {
        my $pair = substr($text, $i, 2);
        if ($depth) {
            if ($pair eq '(*') { $depth++; substr($clean, $i++, 2) = '  '; }
            elsif ($pair eq '*)') { $depth--; substr($clean, $i++, 2) = '  '; }
            else { substr($clean, $i, 1) = ' '; }
        } elsif ($string) {
            if ($pair eq '""') { substr($clean, $i++, 2) = '  '; }
            elsif (substr($text, $i, 1) eq '"') { $string = 0; substr($clean, $i, 1) = ' '; }
            else { substr($clean, $i, 1) = ' '; }
        } elsif ($pair eq '(*') { $depth++; substr($clean, $i++, 2) = '  '; }
        elsif (substr($text, $i, 1) eq '"') { $string = 1; substr($clean, $i, 1) = ' '; }
    }
    while ($clean =~ /\bAdmitted\s*\./g) {
        my $offset = $-[0];
        my @prior = grep { $_->[0] < $offset } @declarations;
        @prior or die "$source: admission has no declaration metadata\n";
        my ($start, $scope, $name) = @{$prior[-1]};
        my $prefix = $scope eq '<>' ? '' : "$scope.";
        $admitted{"$unit.$prefix$name"} = 1;
    }
    # Copy only fields of the resolved module, never arbitrary matching basenames.
    my @scope;
    while ($clean =~ /\b(Module\s+(?:Type\s+)?|End\s+|Include\s+)([\w']+)/g) {
        my ($kind, $name, $offset) = ($1, $2, $-[2]);
        if ($kind =~ /^End/) {
            pop @scope if @scope && ($scope[-1] eq $name || $scope[-1] eq "#$name");
        } elsif ($kind =~ /^Include/) {
            push @copies, [join('.', $unit, @scope), $references{$offset}]
                if @scope && !grep(/^#/, @scope) && defined $references{$offset};
        } elsif ($kind !~ /Type/ && exists $modules{$offset}) {
            @scope = $modules{$offset} eq '<>' ? () : split(/\./, $modules{$offset});
            if (substr($clean, pos($clean)) =~ /^\s*:=\s*([\w']+)/) {
                my $ref_offset = pos($clean) + $-[1];
                push @copies, [join('.', $unit, @scope, $name), $references{$ref_offset}]
                    if defined $references{$ref_offset};
            } else {
                push @scope, $name;
            }
        } elsif ($kind =~ /Type/) {
            push @scope, "#$name" unless substr($clean, pos($clean)) =~ /^[^.]*:=/;
        }
    }
}
my $changed = 1;
while ($changed) {
    $changed = 0;
    for my $copy (@copies) {
        my ($target, $origin) = @$copy;
        for my $name (keys %admitted) {
            next unless $name =~ /^\Q$origin\E\.([^.]+)$/;
            my $copied = "$target.$1";
            $changed = 1 unless $admitted{$copied}++;
        }
    }
}
print "$_\n" for sort keys %admitted;
