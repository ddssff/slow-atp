This repo contains part of John Harrison's automatic theorem prover
code from his book "Handbook of Practical Logic and Automated
Reasoning", along with a literal translation of some of that code
(specifically, the MESON prover) into 500 lines of Haskell (thanks to
Ruben Zilibowitz for this code.)  Unfortunately, the Haskell version
runs about 400 times more slowly than the ocaml version, and I'm
trying to find out why.

    % cd ocaml
    % apt-get install camlp5
    % ocaml
    # #use "init.ml";;
    # meson wishnu;;
    Searching with depth limit 0
    Searching with depth limit 1
    Searching with depth limit 2
    Searching with depth limit 3
    [counts to 16 twice.]
    Searching with depth limit 14
    Searching with depth limit 15
    Searching with depth limit 16
    - : int list = [16; 16]
    #

To run the haskell version:

    % cd haskell
    % ghc -O2 Main.hs -o test
    % ./test
    Searching with depth limit 0
    Searching with depth limit 1
    Searching with depth limit 2
    Searching with depth limit 3
    [... fifteen minutes later ...]
    Searching with depth limit 16
    [16,16]

My question is, what the heck?
