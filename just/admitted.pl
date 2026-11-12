#!/usr/bin/env perl
use strict;
use warnings;

# Glob offsets identify declarations; source text identifies which ones end in Admitted.
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
    my @declarations;
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
        print "$unit.$prefix$name\n";
    }
}
