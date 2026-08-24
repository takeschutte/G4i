(** * Environments

  An environment is a multiset of formulas. We rely on stdpp multisets
  mostly for their powerful multiset equivalence tactic.*)


(** Notion of wellfoundedness *)
Require Import Stdlib.Program.Wf.

(** Stdpp implementation of multisets and finite sets *)
Require Export stdpp.gmultiset.
Require Import stdpp.fin_sets.

(** Our propositional formulas, including their countability. *)
Require Export G4i.Formulas.

Require Import Stdlib.Program.Equality.

(** An environment is defined as a finite multiset of formulas (in the sense of the stdpp library).
This requires decidable equality and countability of the underlying set. *)
Definition env := @gmultiset form form_eq_dec form_count. 
Global Instance singleton : Singleton form env := gmultiset_singleton.
Global Instance singletonMS : SingletonMS form env := base.singleton.

Global Hint Unfold mult empty singleton union intersection env : mset.
(* useful notations :
  {[ x ]} : singleton
      ⊎ : disjoint union
   \: difference (setminus)
   {[ x; y; … ]} union of singletons
   [{[+ x; y; … +]}] *disjoint* union of singletons
      ⊂@ : include
*)

Definition empty := ∅ : env.

Ltac ms :=
  unfold base.singletonMS, singletonMS, base.empty, gmultiset_empty in *;
  autounfold with mset in *; autounfold with mset;
  repeat rewrite gmultiset_elem_of_disj_union; try tauto;
  multiset_solver.

Notation "Γ • φ" := (disj_union Γ (base.singletonMS φ)) (at level 105, φ at level 85, left associativity).

Section GeneralEnvironments.

Global Instance proper_elem_of : Proper ((=) ==> (≡@{env}) ==> (fun x y => x <-> y)) elem_of.
Proof. intros Γ Γ' Heq φ φ' Heq'. ms. Qed.

Global Instance proper_disj_union : Proper ((≡@{env}) ==> (≡@{env}) ==> (≡@{env})) disj_union.
Proof. intros Γ Γ' Heq Δ Δ' Heq'. ms. Qed.

Lemma elements_env_add (Γ : env) φ : elements(Γ • φ) ≡ₚ φ :: elements Γ.
Proof.
setoid_rewrite (gmultiset_elements_disj_union Γ).
setoid_rewrite (gmultiset_elements_singleton φ).
symmetry. apply Permutation_cons_append.
Qed.

(** ** Multiset utilities *)

Lemma multeq_meq (M N: env) : (forall x, multiplicity x M = multiplicity x N) -> M ≡  N.
  Proof. multiset_solver. Qed.

Lemma diff_mult (M N : env) x:
  multiplicity x (M ∖ N) = (multiplicity x M - multiplicity x N)%nat.
Proof. apply multiplicity_difference. Qed.

Lemma union_mult (M N : env) x :
  multiplicity x (M ⊎ N) = (multiplicity x M + multiplicity x N)%nat.
Proof. apply multiplicity_disj_union. Qed.

Lemma singleton_mult_in x y: x = y -> multiplicity x {[+ y +]} = 1.
Proof. intros Heq; rewrite Heq; apply multiplicity_singleton_eq. Qed.

Lemma singleton_mult_notin x y: x <> y -> multiplicity x {[y]} = 0.
Proof. apply multiplicity_singleton_ne. Qed.

(* Two useful basic facts about multisets containing (or not) certain elements. *)
Lemma env_replace {Γ : env} φ {ψ}:
  (ψ ∈ Γ) -> (Γ • φ) ∖ {[ψ]} ≡ (Γ ∖ {[ψ]} • φ).
Proof.
intro Hin. apply multeq_meq. intros θ.
rewrite diff_mult, union_mult, union_mult, diff_mult.
apply PeanoNat.Nat.add_sub_swap.
case (decide (θ = ψ)); intro; subst.
- now rewrite singleton_mult_in.
- rewrite singleton_mult_notin; trivial. lia.
Qed.

Lemma diff_not_in (Γ : env) φ : φ ∉ Γ -> Γ ∖ {[φ]} ≡ Γ.
Proof.
intro Hf. apply multeq_meq. intros ψ.
rewrite diff_mult. rewrite (elem_of_multiplicity φ Γ) in Hf.
unfold mult.
case (decide (φ = ψ)).
- intro; subst. lia.
- intro Hneq. setoid_rewrite (multiplicity_singleton_ne ψ φ); trivial. lia.
  auto.
Qed.

Lemma env_add_remove : ∀ (Γ: env) φ, (Γ • φ) ∖ {[φ]} =Γ.
Proof. intros; ms. Qed.

(** ** Conjunction, disjunction, and implication *)
(** In the construction of propositional quantifiers, we often want to take the
    conjunction, disjunction, or implication of a (multi)set of formulas.
    The following results give some small optimizations of this process, by
    reducing "obvious" conjunctions such as ⊤ ∧ ϕ, ⊥ ∧ ϕ, etc. *)

Definition irreducible (Γ : env) :=
  (∀ k xs φ, (Atom k xs → φ) ∈ Γ -> ¬ Atom k xs ∈ Γ) /\
  ¬ ⊥ ∈ Γ /\
  ∀ φ ψ, ¬ (φ ∧ ψ) ∈ Γ /\ ¬ (φ ∨ ψ) ∈ Γ.

Definition is_double_negation φ ψ := φ = ¬ ¬ ψ.
Global Instance decidable_is_double_negation φ ψ :
  Decision (is_double_negation φ ψ) := decide (φ =  ¬ ¬ ψ).

Definition is_implication (φ ψ : form) := exists θ, φ = (θ → ψ).
Global Instance decidable_is_implication φ ψ : Decision (is_implication φ ψ).
Proof.
unfold is_implication.
destruct φ; try solve[right; intros [θ Hθ]; discriminate].
case (decide (φ2 = ψ)).
- intro; subst. left. eexists; reflexivity.
- intro n. right; intros [θ Hθ]. now dependent destruction Hθ.
Defined.

Definition is_negation φ ψ := φ = ¬ ψ.
Global Instance decidable_is_negation φ ψ : Decision (is_negation φ ψ) := decide (φ =  ¬ ψ).

(** ** A dependent version of `map` *)
(* a dependent map on lists, with knowledge that we are on that list *)
(* should work with any set-like type *)

Program Fixpoint in_map_aux {A : Type} (Γ : list form) (f : forall φ, (φ ∈ Γ) -> A)
 Γ' (HΓ' : Γ' ⊆ Γ) : list A:=
match Γ' with
| [] => []
| a::Γ' => f a _ :: in_map_aux Γ f Γ' _
end.
Next Obligation.
intros. auto with *.
Qed.
Next Obligation. auto with *. Qed.


Definition in_map {A : Type} Γ
  (f : forall φ, (φ ∈ Γ) -> A) : list A :=
  in_map_aux Γ f Γ (reflexivity _).


(* This generalises to any type. decidability of equality over this type is necessary for a result in "Type" *)
Lemma in_in_map {A : Type} {HD : forall a b : A, Decision (a = b)}
  Γ (f : forall φ, (φ ∈ Γ) -> A) ψ :
  ψ ∈ (in_map Γ f) -> {ψ0 & {Hin | ψ = f ψ0 Hin}}.
Proof.
unfold in_map.
assert(Hcut : forall Γ' (HΓ' : Γ' ⊆ Γ), ψ ∈ in_map_aux Γ f Γ' HΓ'
  → {ψ0 & {Hin : ψ0 ∈ Γ | ψ = f ψ0 Hin}}); [|apply Hcut].
induction Γ'; simpl; intros HΓ' Hin.
- contradict Hin. auto. now rewrite elem_of_nil.
- match goal with | H : ψ ∈ ?a :: (in_map_aux _ _ _ ?HΓ'') |- _ =>
  case (decide (ψ = a)); [| pose (myHΓ' := HΓ'')] end.
  + intro Heq; subst. exists a. eexists. reflexivity.
  + intro Hneq. apply (IHΓ' myHΓ').
    apply elem_of_cons in Hin. tauto.
Qed.

Local Definition in_subset {Γ : env} {Γ'} (Hi : Γ' ⊆ elements Γ) {ψ0} (Hin : ψ0 ∈ Γ') : ψ0 ∈ Γ.
Proof. apply gmultiset_elem_of_elements,Hi, Hin. Defined.

(* converse *)
(* we require proof irrelevance for the mapped function *)
Lemma in_map_in {A : Type} {HD : forall a b : A, Decision (a = b)}
  {Γ} {f : forall φ, (φ ∈ Γ) -> A} {ψ0} (Hin : ψ0 ∈ Γ):
  {Hin' | f ψ0 Hin' ∈ (in_map Γ f)}.
Proof.
unfold in_map.
assert(Hcut : forall Γ' (HΓ' : Γ' ⊆ Γ) ψ0 (Hin : In ψ0 Γ'),
  {Hin' | f ψ0 Hin' ∈ in_map_aux Γ f Γ' HΓ'}).
- induction Γ'; simpl; intros HΓ' ψ' Hin'; [auto with *|].
  case (decide (ψ' = a)).
  + intro; subst a. eexists. left.
  + intro Hneq. assert (Hin'' : In ψ' Γ') by (destruct Hin'; subst; tauto).
      pose (Hincl := (in_map_aux_obligation_2 Γ (a :: Γ') HΓ' a Γ' eq_refl)).
      destruct (IHΓ' Hincl ψ' Hin'') as [Hin0 Hprop].
      eexists. right. apply Hprop.
- destruct (Hcut Γ (reflexivity Γ) ψ0) as [Hin' Hprop].
  + auto. now apply list_elem_of_In.
  + exists Hin'. exact Hprop.
Qed.

Lemma in_map_empty A f : @in_map A [] f = [].
Proof. auto with *. Qed.

Lemma in_map_ext {A} Δ f g:
  (forall φ H, f φ H = g φ H) -> @in_map A Δ f = in_map Δ g.
Proof.
  intros Heq.
  unfold in_map.
  assert(forall Γ HΓ, in_map_aux Δ f Γ  HΓ = in_map_aux Δ g Γ  HΓ); [|trivial].
  induction Γ; intro HΓ.
  - trivial.
  - simpl. now rewrite Heq, IHΓ.
Qed.

Lemma difference_singleton (Δ: env) φ: φ ∈ Δ -> Δ ≡ ((Δ ∖ {[φ]}) • φ).
Proof.
intro Hin. rewrite (gmultiset_disj_union_difference {[φ]}) at 1. ms.
now apply gmultiset_singleton_subseteq_l.
Qed.

Lemma env_in_add (Δ : env) ϕ φ: φ ∈ (Δ • ϕ) <-> φ = ϕ \/ φ ∈ Δ.
Proof.
rewrite (gmultiset_elem_of_disj_union Δ), gmultiset_elem_of_singleton.
tauto.
Qed.

Lemma equiv_disj_union_compat_r {Δ Δ' Δ'' : env} : Δ ≡ Δ'' -> Δ ⊎ Δ' ≡ Δ'' ⊎ Δ'.
Proof. ms. Qed.

Lemma env_add_comm (Δ : env) φ ϕ : (Δ • φ • ϕ) ≡ (Δ • ϕ • φ).
Proof. ms. Qed.

Lemma in_difference (Δ : env) φ ψ : φ ≠ ψ -> φ ∈ Δ -> φ ∈ Δ ∖ {[ψ]}.
Proof.
intros Hne Hin.
unfold elem_of, gmultiset_elem_of.
rewrite (multiplicity_difference Δ {[ψ]} φ).
assert( HH := multiplicity_singleton_ne φ ψ Hne).
unfold singletonMS, base.singletonMS in HH.
unfold base.singleton, Environments.singleton. ms.
Qed.

Hint Resolve in_difference : multiset.

(* could be used in disj_inv *)
Lemma env_add_inv (Γ Γ' : env) φ ψ:
  φ ≠ ψ ->
  ((Γ • φ) ≡ (Γ' • ψ)) ->
    (Γ' ≡  ((Γ ∖ {[ψ]}) • φ)).
Proof.
intros Hneq Heq. rewrite <- env_replace.
- ms.
- assert(ψ ∈ (Γ • φ)); [rewrite Heq|]; ms.
Qed.

Lemma env_add_inv' (Γ Γ' : env) φ: (Γ • φ) ≡ Γ' -> (Γ ≡  (Γ' ∖ {[φ]})).
Proof. intro Heq. ms. Qed.

Lemma env_equiv_eq (Γ Γ' :env) : Γ =  Γ' -> Γ ≡  Γ'.
Proof. intro; subst; trivial. Qed.

(* reprove the following principles, proved in stdpp for Prop, but
   we need them in Type *)
Lemma gmultiset_choose_or_empty (X : env) : {x | x ∈ X} + {X = ∅}.
Proof.
  destruct (elements X) as [|x l] eqn:HX; [right|left].
  - by apply gmultiset_elements_empty_inv.
  - exists x. rewrite <- (gmultiset_elem_of_elements x X).
    replace (elements X) with (x :: l). left.
Qed.

(* We need this induction principle in type. *)
Lemma gmultiset_rec (P : env → Type) :
  P ∅ → (∀ x X, P X → P ({[+ x +]} ⊎ X)) → ∀ X, P X.
Proof.
  intros Hemp Hinsert X. induction (gmultiset_wf X) as [X _ IH].
  destruct (gmultiset_choose_or_empty X) as [[x Hx]| ->]; auto.
  rewrite (gmultiset_disj_union_difference' x X) by done.
  apply Hinsert, IH; multiset_solver.
Qed.

Lemma difference_include θ θ' (Δ : env) :
  (θ' ∈ Δ) ->
  θ ∈ Δ ∖ {[θ']} -> θ ∈ Δ.
Proof.
intros Hin' Hin.
rewrite gmultiset_disj_union_difference with (X := {[θ']}).
- apply gmultiset_elem_of_disj_union. tauto.
- now apply gmultiset_singleton_subseteq_l.
Qed.

Fixpoint rm x l := match l with
| h :: t => if form_eq_dec x h then t else h :: rm x t
| [] => []
end.

Lemma in_rm l x y: In x (rm y l) -> In x l.
Proof.
induction l; simpl. tauto.
destruct form_eq_dec. tauto. firstorder.
Qed.

Lemma remove_include θ θ' Δ : (θ' ∈ Δ) -> θ ∈ rm θ' Δ -> θ ∈ Δ.
Proof. intros Hin' Hin. eapply list_elem_of_In, in_rm, list_elem_of_In, Hin. Qed.


(* technical lemma : one can constructively find whether an environment contains
   an element satisfying a decidable property *)
Lemma decide_in (P : _ -> Prop) (Γ : env) :
  (forall φ, Decision (P φ)) ->
  {φ | (φ ∈ Γ) /\ P φ} + {forall φ, φ ∈ Γ -> ¬ P φ}.
Proof.
intro HP.
induction Γ using gmultiset_rec.
- right. intros φ Hφ; inversion Hφ.
- destruct IHΓ as [(φ&Hφ) | HF].
  + left. exists φ. ms.
  + case (HP x); intro Hx.
    * left; exists x. ms.
    * right. intros. ms.
Qed.

Lemma union_difference_L (Γ : env) Δ ϕ: ϕ ∈ Γ -> (Γ ⊎ Δ) ∖ {[ϕ]} ≡ Γ ∖{[ϕ]} ⊎ Δ.
Proof. intro Hin. pose (difference_singleton _ _ Hin). ms. Qed.

Lemma union_difference_R (Γ : env) Δ ϕ: ϕ ∈ Δ -> (Γ ⊎ Δ) ∖ {[ϕ]} ≡ Γ ⊎ (Δ ∖{[ϕ]}).
Proof. intro Hin. pose (difference_singleton _ _ Hin). ms. Qed.

Global Instance equiv_assoc : @Assoc env equiv disj_union.
Proof. intros x y z. ms. Qed.

Global Instance proper_difference : Proper ((≡@{env}) ==> eq ==> (≡@{env})) difference.
Proof. intros Γ Γ' Heq Δ Heq'. ms. Qed.

(* Definition var_not_in_env p (Γ : env):=  (∀ φ0, φ0 ∈ Γ -> ¬ occurs_in p φ0). *)

(** ** Tactics *)
(* helper tactic split cases given an assumption about belonging to a multiset *)

End GeneralEnvironments.

Global Ltac in_tac :=
repeat
match goal with
| H : ?θ  ∈ {[?θ1; ?θ2]} |- _ => apply gmultiset_elem_of_union in H; destruct H as [H|H]; try subst
| H : ?θ ∈ (?Δ ∖ {[?θ']}) |- _ => apply difference_include in H; trivial
| H : context [?θ  ∈ (?d • ?θ2)] |- _ =>
    rewrite (env_in_add d) in H; destruct H as [H|H]; try subst
| H : context [?θ ∈ {[ ?θ2 ]}] |- _ => rewrite gmultiset_elem_of_singleton in H; subst
end.


Global Hint Immediate equiv_assoc : proof.

Global Instance Proper_elements:
  Proper ((≡) ==> (≡ₚ)) ((λ Γ : env, gmultiset_elements Γ)).
Proof.
intros Γ Δ Heq; apply AntiSymm_instance_0; apply gmultiset_elements_submseteq; ms.
Qed.

Lemma list_to_set_disj_env_add Δ v:
  ((list_to_set_disj Δ : env) • v : env) ≡ list_to_set_disj (v :: Δ).
Proof. ms. Qed.

Lemma list_to_set_disj_rm Δ v:
  (list_to_set_disj Δ : env) ∖ {[v]} ≡ list_to_set_disj (rm v Δ).
Proof.
induction Δ as [|φ Δ]; simpl; [ms|].
case form_eq_dec; intro; subst; [ms|].
simpl. rewrite <- IHΔ. case (decide (v ∈ (list_to_set_disj Δ: env))).
- intro. rewrite union_difference_R by assumption. ms.
- intro. rewrite diff_not_in by auto with *. rewrite diff_not_in; auto with *.
Qed.


Lemma gmultiset_elements_list_to_set_disj (l : list form):
  gmultiset_elements(list_to_set_disj l) ≡ₚ l.
Proof.
induction l as [| x l]; [ms|].
rewrite Proper_elements; [|symmetry; apply list_to_set_disj_env_add].
setoid_rewrite elements_env_add; rewrite IHl. trivial.
Qed.

(* Additional lemmas for gmultiset *)
Lemma gmultiset_neq_forward `{Countable A} (X : gmultiset A) (a b : A) :
  a ≠ b -> (X ∖ {[+ a +]}) ⊎ {[+ b +]} = (X ⊎ {[+ b +]}) ∖ {[+ a +]}.
Proof.
  intros Hneq.
  induction X as [| x X' IHX'] using gmultiset_ind.
  - replace (∅ ∖ {[+ a +]}) with (∅ : gmultiset A) by ms.
    assert (a ∉ ((∅ : gmultiset A) ⊎ {[+ b +]})) by multiset_solver.
    assert (forall Y : gmultiset A, a ∉ Y -> Y ∖ {[+ a +]} = Y) by multiset_solver.
    multiset_solver.
  - multiset_solver.
Qed.
      
Section gmultiset_map.
  Context `{Countable A, Countable B, Countable C}.

  Lemma gmultiset_map_ident (X : gmultiset A) : gmultiset_map (fun x => x) X = X.
  Proof.
    induction X as [|z Z IH] using gmultiset_ind; 
    try rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton, IH; easy.
  Qed.
  
  Context (f : A → B).
  Definition injective_map (g : A → B) := ∀ (x : A) (y : A), g x = g y -> x = y.

  Lemma gmultiset_map_eq (X Y : gmultiset A) : X = Y -> gmultiset_map f X = gmultiset_map f Y.
  Proof. intros H'. f_equal; easy. Qed.


  Lemma gmultiset_map_equiv (X Y : gmultiset A) :
    X ≡ Y -> gmultiset_map f X ≡ gmultiset_map f Y.
  Proof. pose gmultiset_map_eq; unfold_leibniz; apply e. Qed.
  
  Lemma gmultiset_map_elem_of (x : A) (X : gmultiset A): x ∈ X -> f x ∈ gmultiset_map f X.
  Proof. intros Hin; apply elem_of_gmultiset_map; exists x; split; [ easy | easy ]. Qed.

  Lemma gmultiset_diff_not_in `{Countable C} (X : gmultiset C) (x : C) : x ∉ X -> X ∖ {[+ x +]} = X.
  Proof. multiset_solver. Qed.

  (* The following lemmas are mainly for our forward_map tactic *)
  Lemma gmultiset_map_distr_disj_union_under_diff (X Y : gmultiset A) : 
    gmultiset_map f (X ⊎ Y) ∖ gmultiset_map f Y = gmultiset_map f X.
  Proof. rewrite (gmultiset_map_disj_union f X Y). ms. Qed.

  Lemma gmultiset_map_distr_disj_union_under_disj_union (X Y: gmultiset A) (Z : gmultiset B):
          gmultiset_map f (X ⊎ Y) ⊎ Z = (gmultiset_map f X) ⊎ (gmultiset_map f Y) ⊎ Z.
  Proof. rewrite (gmultiset_map_disj_union f X Y). ms. Qed.

  Lemma gmultiset_map_distr_disj_union_singleton (X : gmultiset A) (a : A) :
    gmultiset_map f (X ⊎ {[+ a +]}) = (gmultiset_map f X) ⊎ {[+ f a +]}.
  Proof. rewrite (gmultiset_map_disj_union f X {[+ a +]}), (gmultiset_map_singleton f a). reflexivity. Qed.

  Lemma gmultiset_map_distr_singleton_diff (X : gmultiset A) (a : A):
    injective_map f -> gmultiset_map f (X ∖ {[+ a +]}) = (gmultiset_map f X) ∖ {[+ f a +]}.
  Proof.
    induction X as [|z Z IH] using gmultiset_ind; intros Hinj.
    - rewrite (gmultiset_empty_difference {[+ a +]} ∅ (gmultiset_empty_subseteq {[+ a +]})),
        gmultiset_map_empty; ms.
    - assert (Decision (a = z)) as Hdec by solve_decision.
      destruct Hdec as [Heq | Hneq] .
      + rewrite Heq, <- gmultiset_map_singleton.
        replace (({[+ z +]} ⊎ Z) ∖ {[+ z +]}) with Z by ms.
        replace ({[+ z +]} ⊎ Z) with ((Z ⊎ {[+ z +]})) by ms.
        apply symmetry, (gmultiset_map_distr_disj_union_under_diff Z {[+ z +]}).
      + (* Simplify LHS to {f y} ⊎ f (X \ A) *)
        replace (({[+ z +]} ⊎ Z) ∖ {[+ a +]}) with ({[+ z +]} ⊎ (Z ∖ {[+ a +]})) by multiset_solver.
        rewrite (gmultiset_map_disj_union f {[+ z +]} (Z ∖ {[+ a +]})).
        (* Simplify RHS *)
        rewrite (gmultiset_map_disj_union f {[+ z +]} Z), (gmultiset_map_singleton f z).
        destruct (decide (f a = f z)); [ multiset_solver | multiset_solver ].
  Qed.
  
  Context (g : B → C).
  Lemma gmultiset_map_compose (X : gmultiset A) :
    gmultiset_map g (gmultiset_map f X) = gmultiset_map (g ∘ f) X.
  Proof.
    induction X using gmultiset_ind;
      try (rewrite !gmultiset_map_disj_union, !gmultiset_map_singleton, IHX);
      done.
  Qed.
End gmultiset_map.
