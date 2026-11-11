This README is human-written.
The Metamath file contains proofs that the formal theory IΔ₀ can prove that these Turing machines run forever:

1. `1RB0RB_0LA---` "cycler"
2. `1RB1RA_1LA---` "translated cycler"
3. `1RB---_1LC1RB_0RA0LC` "binary counter"
4. `1RB0LC_0LC1RA_---1LA` "bouncer"
5. `1RB0LA_1RC---_0RD0RC_1LD0LA` "fractal"
6. `1RB1RE_1LC1RB_0RA0LD_1LB1LD_---0RA` "Finned #3"
7. `1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB` "Skelet #10"

The proofs consist solely of derivations within the formal theory IΔ₀.

The formal theory, Turing machine encoding within the formalization, and the nonhalting proofs for machines #1-6 are explained in "six_nonhalting_proofs-1.pdf". The proof for Skelet #10 is explained in "skelet10_explained.pdf". "quotient_remainder_computation_codes-1.pdf" gives more explanation for the Turing machine encoding.

The rest of the results in the papers are not verified within a proof assistant.

"bb2_idelta0_cps_free.pdf" gives an argument that shows that cyclers and translated cyclers up to period 8 can proven nonhalting in IΔ₀. This could be extended to show that IΔ₀ can prove that BB(2)=6, and almost certainly to prove translated cyclers of any length.
"pa_minus_translated_cycler_and_encodings.pdf" shows that the halting status of machine #2 (the translated cycler) is independent of the formal theory PA^-, which has no induction. "sqrt2_11_state_machine_beginner_paper-1.pdf" gives an 11-state machine which halts if and only if there exists two positive integers x and y where x^2=2y^2. This machine is meant to be independent of the axiomatic foundation IOpen (Arithmetic with open induction), as it cannot prove that √2 is irrational. However, we claim no proof of this independence result.

Some goals and future directions of this research are to create an analogy for Reverse Mathematics to Pi_1 statements, and to potentially discover more concise or natural instances of logical independence.

A human made document will be released at some point within the future.
