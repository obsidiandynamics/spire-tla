---- MODULE SPSafe ----
(*****************************************************************************)
(* Extension of the base `SP' module to facilitate bounded model             *)
(* checking of its safety property.                                          *)
(*****************************************************************************)
EXTENDS SP, TLC

CONSTANTS MaxSlot,     \* an upper bound on `Slots'
          MaxTheta     \* an upper bound on `Thetas'  

\* A finite set of slots, required for bounded model checking.
FiniteSlots == 1..MaxSlot

\* A finite set of `θ' values, required for bounded model checking.
FiniteThetas  == 1..MaxTheta

\* Model symmetry across proposers and commands.
Symmetry == Permutations(Proposers) \union Permutations(Commands)
====