(* -----------------------------------------------------------------------
      Core dependently typed lambda calculus language syntax
   ----------------------------------------------------------------------- 

    a, A, b, B ::=  x                       - Variable
                  | A B                     - Application
                  | λx:A. b                 - Lambda abstraction
                  | (x: A) -> B             - Dependent function type (Πx:A. B)
                  | Type                    - Universe type
                  | (t : A)                 - Type annotation
                  | Bool                    - Bool type
                  | True | False            - Bool values
                  | if a then a else a      - If expression 
                  | {x : A | B}             - Dependent pair type
                  | (a, b)                  - Pair constructor
                  | let (x, y) = a in b     - Pair deconstruction
                  | let x = a in b          - Let statement
                  | Unit                    - Unit type
                  | ()                      - Unit value
                  | Sorry                   - An axiom 'sorry', inhabits all types
                  | PrintMe                 - print context
*)
