
Definition admit {T: Set}: T. Admitted.

Inductive nat: Set :=
  | O: nat
  | S: nat -> nat.

Inductive vec (A: Set): nat -> Set :=
  | nil :                     vec A (O  )
  | cons: forall m, A -> vec A m -> vec A (S m).

Arguments nil  {A}.
Arguments cons {A m} _ _.
Infix "::" := cons.

Inductive eq {A: Set} (x: A): A -> Set :=
  | eq_refl: eq x x.

Arguments eq_refl {A x}.
Infix "=" := eq : type_scope.

Definition succ_rewrite {T: nat -> Set} {m n: nat} (H: S m = S n): T n -> T m.
  refine (
      match H in _ = j return
            match j with
              | O   => Empty_set
              | S i => T i -> T m
            end
      with
        | eq_refl => fun t => t
      end
    ).
Defined.

Definition nat_disc {T: Set} {m: nat} (H: S m = O): T.
  refine (
      match H in _ = j return
            match j with
              | O   => T
              | S i => unit
            end
      with
        | eq_refl => tt
      end
    ).
Defined.

Definition zip' {A B C: Set} (f: A -> B -> C): forall n, vec A n -> vec B n -> vec C n.
  refine (
      fix zip {n} xs :=
        match xs in vec _ j return vec B j -> vec C j with
          | nil         => fun ys => nil
          | cons p x xt => fun ys =>
            match ys in vec _ j return S p = j -> vec C (S p) with
              | nil         => nat_disc
              | cons q y yt => fun Heq => f x y :: zip xt (succ_rewrite Heq yt)
            end eq_refl
        end
    ).
Defined.

Definition uncons {A: Set} {m: nat} (v: vec A (S m)): A * vec A m.
  refine (
      match v in vec _ j return
            match j with
              | O   => unit
              | S i => A * vec A i
            end
      with
        | nil         => tt
        | cons p x xt => (x, xt)
      end
    ).
Defined.

Definition zip {A B C: Set} (f: A -> B -> C): forall n, vec A n -> vec B n -> vec C n.
  refine (
      fix zip {n}: vec A n -> vec B n -> vec C n :=
        match n with
          | O   => fun xs ys => nil
          | S p => fun xs ys =>
                    match uncons xs, uncons ys with
                      | (x, xt), (y, yt) => f x y :: zip xt yt
                    end
        end
    ).
Defined.

Print zip.

