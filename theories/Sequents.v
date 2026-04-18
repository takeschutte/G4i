Require Export G4i.Environments.
Require Export G4i.Substitutions.
Open Scope stdpp_scope.

(** * Sequent calculus G4iSL *)

(** We implement the sequent calculus G4ip, a contraction-free
 refinement of the usual Gentzen sequent calculus LJ for intuitionistic
 propositional logic, which was developed by the Soviet school of proof theory
 (Vorob'ev 1970) and introduced in the West by (Hudelmaier 1989) and (Dyckhoff
 1990). This calculus is also referred to as "LJT" in the literature, but we this name has also been used in the literature for other, unrelated calculi, so we prefer to use "G4ip" to avoid ambiguity.

 The calculus G4ip is important because it allows for a terminating proof
 search, and in our proof of Pitts' theorem, it therefore lets us perform
 well-founded induction on proofs. Technically, this is thanks to the absence of
 a contraction rule. The left implication rule is refined into four separate
 proof rules.  *)

(** ** Definition of provability in G4iSL *)
Reserved Notation "Γ ⊢ φ" (at level 90).
Inductive Provable : env -> form -> Type :=
| Init :    ∀  Γ i xs, Γ • (Atom i xs) ⊢ (Atom i xs)
| ExFalso : ∀  Γ φ, Γ • ⊥ ⊢ φ
| AndR : ∀  Γ φ ψ,
    Γ ⊢ φ ->    Γ ⊢ ψ ->
      Γ ⊢ (φ ∧ ψ)
| AndL :    ∀  Γ φ ψ θ,
    Γ • φ • ψ ⊢ θ ->
      Γ • (φ ∧ ψ) ⊢ θ
| OrR1 :    ∀  Γ φ ψ,
    Γ ⊢ φ ->
      Γ ⊢ (φ ∨ ψ)
| OrR2 :    ∀  Γ φ ψ,
    Γ ⊢ ψ ->
      Γ ⊢ (φ ∨ ψ)
| OrL :     ∀  Γ φ ψ θ,
    Γ • φ  ⊢ θ -> Γ • ψ ⊢ θ ->
      Γ • (φ ∨ ψ) ⊢ θ
| ImpR :    ∀  Γ φ ψ,
    Γ • φ ⊢ ψ ->
      Γ ⊢ (φ → ψ)
| ImpL0 : ∀  Γ i xs φ ψ,
    Γ • (Atom i xs) • φ ⊢ ψ ->
      Γ • (Atom i xs) • ((Atom i xs) → φ) ⊢ ψ
| ImpLAnd : ∀  Γ φ1 φ2 φ3 ψ,
    Γ • (φ1 → (φ2 → φ3)) ⊢ ψ ->
      Γ • ((φ1 ∧ φ2) → φ3) ⊢ ψ
| ImpLOr :  ∀  Γ φ1 φ2 φ3 ψ,
    Γ • (φ1 → φ3) • (φ2 → φ3) ⊢ ψ ->
      Γ • ((φ1 ∨ φ2) → φ3) ⊢ ψ
| ImpLImp : ∀  Γ φ1 φ2 φ3 ψ,
    Γ • φ1 • (φ2 → φ3) ⊢ φ2 ->Γ • φ3 ⊢ ψ ->
    Γ • ((φ1 → φ2) → φ3) ⊢ ψ
| ForAllR : ∀ Γ φ,
    gmultiset_map (subst_form S') Γ ⊢ φ -> Γ ⊢ (ForAll φ)
| ForAllL : ∀ Γ φ ψ t,
    Γ • (ForAll φ) • (subst_form (bind_var t) φ) ⊢ ψ ->
    Γ • (ForAll φ) ⊢ ψ
| ExistsR : ∀ Γ φ t,
    Γ ⊢ (subst_form (bind_var t) φ) -> Γ ⊢ (Exists φ)
| ExistsL : ∀ Γ φ ψ,
    (gmultiset_map (subst_form S') Γ) • φ ⊢ (subst_form S' ψ) -> Γ • (Exists φ) ⊢ ψ
| ImpLForAll : ∀ Γ φ1 φ2 ψ,
    Γ • (ForAll (φ1) → φ2) ⊢ (ForAll φ1) -> (Γ • φ2) ⊢ ψ ->
    Γ • (ForAll (φ1) → φ2) ⊢ ψ
| ImpLExists : ∀ Γ φ1 φ2 ψ,
    Γ • ForAll (φ1 → (subst_form S' φ2)) ⊢ ψ ->
    Γ • (Exists (φ1) → φ2) ⊢ ψ
where "Γ ⊢ φ" := (Provable Γ φ).

Notation "Γ ⊢ φ" := (Provable Γ φ) (at level 90).

Global Hint Constructors Provable : proof.

(** We show that equivalent multisets prove the same things. *)
Global Instance proper_Provable : Proper ((≡@{env}) ==> (=) ==> (=)) Provable.
Proof. intros Γ Γ' Heq φ φ' Heq'. ms. Qed.

Global Ltac equiv_tac :=
  repeat rewrite <- list_to_set_disj_rm;
  repeat rewrite <- list_to_set_disj_env_add;
  repeat (rewrite <- difference_singleton; trivial);
  try rewrite <- list_to_set_disj_rm;
  try (rewrite union_difference_L by trivial);
  try (rewrite union_difference_R by trivial);
  try ms.

(** We introduce a tactic "peapply" which allows for application of a G4ip rule
   even in case the environment needs to be reordered *)
Ltac peapply th :=
  (erewrite proper_Provable;  [| |reflexivity]);  [eapply th|try ms].

(** ** Tactics *)

(** We introduce a few tactics that we will need to prove the admissibility of
  the weakening and exchange rules in the proof calculus. *)

(** The tactic "exch" swaps the nth pair of formulas of a sequent, counting from the right. *)

Ltac exch n := match n with
| O => match goal with |- ?a • ?b • ?c ⊢ _ =>
  rewrite (proper_Provable _ _ (env_add_comm a b c) _ _ eq_refl) end
| S O => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (env_add_comm _ _ _)) _ _ eq_refl)
| S (S O) => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_add_comm _ _ _))) _ _ eq_refl)
| S (S (S O)) => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_add_comm _ _ _)))) _ _ eq_refl)
end.

(** The tactic "exhibit" exhibits an element that is in the environment. *)
Ltac exhibit Hin n := match n with
| 0 => rewrite (proper_Provable _ _ (difference_singleton _ _ Hin) _ _ eq_refl)
| 1 => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (difference_singleton _ _ Hin)) _ _ eq_refl)
| 2 => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (equiv_disj_union_compat_r (difference_singleton _ _ Hin))) _ _ eq_refl)
| 3 => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r (equiv_disj_union_compat_r (difference_singleton _ _ Hin)))) _ _ eq_refl)
end.

(** The tactic "forward" tries to change a goal of the form :

((Γ•φ ∖ {[ψ]}•…) ⊢ …

into

((Γ ∖ {[ψ]}•…•φ) ⊢ … ,

by first proving that ψ ∈ Γ. *)

Ltac forward := match goal with
| |- (?Γ•?φ) ∖ {[?ψ]} ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (env_replace φ Hin) _ _ eq_refl)
| |- (?Γ•?φ) ∖ {[?ψ]}•_ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (env_replace φ Hin)) _ _ eq_refl);
  exch 0
| |- (?Γ•?φ) ∖ {[?ψ]}•_•_ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin))) _ _ eq_refl);
  exch 1; exch 0
| |- (?Γ•?φ) ∖ {[?ψ]}•_•_•_ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin)))) _ _ eq_refl);
  exch 2; exch 1; exch 0
| |- (?Γ•?φ) ∖ {[?ψ]}•_•_•_•_ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin))))) _ _ eq_refl);
  exch 3; exch 2; exch 1; exch 0
(* Added 03/2025 - forward when φ ≠ ψ, then (Γ • φ) ∖ {[ ψ ]} = Γ ∖ {[ ψ ]} • φ *)
| |- context[ (?Γ • ?φ) ∖ {[ ?ψ ]} ] =>
  replace ((Γ • φ) ∖ {[ ψ ]}) with ((Γ ∖ {[ ψ ]}) • φ) by (apply gmultiset_neq_forward; easy)
end.

(** The tactic "backward" changes a goal of the form :

((Γ ∖ {[ψ]}•…•φ) ⊢ …

into

((Γ•φ ∖ {[ψ]}•…) ⊢ …,

by first proving that ψ ∈ Γ.

*)

Ltac backward := match goal with
| |- ?Γ ∖ {[?ψ]}•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof);
  rewrite (proper_Provable _ _ (symmetry(env_replace _ Hin)) _ _ eq_refl)
| |- ?Γ ∖ {[?ψ]}•_•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof); try exch 0;
  rewrite (proper_Provable _ _ (symmetry(equiv_disj_union_compat_r (env_replace _ Hin))) _ _ eq_refl)
| |- ?Γ ∖ {[?ψ]}•_•_•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof); exch 0; exch 1;
  rewrite (proper_Provable _ _ (symmetry(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin)))) _ _ eq_refl)
| |- ?Γ ∖ {[?ψ]}•_•_•_•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof); exch 0; exch 1; exch 2;
  rewrite (proper_Provable _ _ (symmetry(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin))))) _ _ eq_refl)
| |- ?Γ ∖ {[?ψ]}•_•_•_•_•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof); exch 0; exch 1; exch 2; exch 3;
  rewrite (proper_Provable _ _ (symmetry(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin)))))) _ _ eq_refl)
(* Added 03/2025 - backward when φ ≠ ψ, then (Γ • φ) ∖ {[ ψ ]} = Γ ∖ {[ ψ ]} • φ *)
| |- context[ (?Γ ∖ {[ ?ψ ]}) • ?φ ] =>
  replace ((Γ ∖ {[ ψ ]}) • φ) with ((Γ • φ) ∖ {[ ψ ]}) by (symmetry; apply gmultiset_neq_forward; easy)
end.

(** The tactic "rw" rewrites the environment equivalence Heq under the nth formula in the premise. *)
Ltac rw Heq n := match n with
| 0 => erewrite (proper_Provable _ _ Heq _ _ eq_refl)
| 1 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r Heq) _ _ eq_refl)
| 2 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r Heq)) _ _ eq_refl)
| 3 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r Heq))) _ _ eq_refl)
| 4 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (equiv_disj_union_compat_r Heq)))) _ _ eq_refl)
| 5 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (equiv_disj_union_compat_r Heq))))) _ _ eq_refl)
end.
