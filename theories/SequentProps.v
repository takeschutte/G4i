(* Required for dependent induction. *)
Require Import Stdlib.Program.Equality.
From Stdlib Require Import FinFun. (* Injectivity *)
From stdpp Require Import countable.
Require Export G4i.Sequents.

(** * Admissible rules in G4ip sequent calculus

This file contains important properties of the sequent calculus G4ip, defined in
Sequents.v, namely the admissibility of various inversion rules, weakening and
contraction. We draw various consequences from this that are used extensively in
the proof of correctness of propositional quantifiers. The first part of this
file closely follows proof in the paper:

(Dyckhoff and Negri 2000). R. Dyckhoff and S. Negri, Admissibility of Structural
Rules for Contraction-Free Systems of Intuitionistic Logic, Journal of Symbolic
Logic (65):4.
*)

(** ** Weakening *)

(** We prove the admissibility of the weakening rule. *)

Ltac forward_map :=
  match goal with
  (* | |-  (gmultiset_map ?f (?Γ • ?α)) ⊢ _ =>
      rewrite (gmultiset_map_distr_disj_union_singleton f Γ α) *)
  | |- context[gmultiset_map ?f (?Γ • ?α)] =>
      rewrite (gmultiset_map_distr_disj_union_singleton f Γ α)
  end.

Ltac backward_map :=
  match goal with
  (* | |-  (gmultiset_map ?f ?Γ) • (?f ?α)  ⊢ _ =>
      replace (gmultiset_map f Γ • f α) with (gmultiset_map f (Γ • α))
      by (apply (gmultiset_map_distr_disj_union_singleton f Γ α)) *)
  | |- context[(gmultiset_map ?f ?Γ) • ?f ?α] =>
      replace (gmultiset_map f Γ • f α) with (gmultiset_map f (Γ • α))
      by (apply (gmultiset_map_distr_disj_union_singleton f Γ α))
  end.

Ltac unmap_diff_singleton :=
  match goal with
  (* | |- (gmultiset_map (subst_form S') (?Γ ∖ {[ ?α ]})) ⊢ _=>
      replace (gmultiset_map (subst_form S') (Γ ∖ {[α]})) with ((gmultiset_map (subst_form S') Γ) ∖ {[subst_form S' (α) ]})
      by (rewrite (gmultiset_map_distr_singleton_diff (subst_form S') Γ α inj_subst_S); ms) *)
  | |- context[(gmultiset_map (subst_form S') (?Γ ∖ {[ ?α ]}))] =>
      replace (gmultiset_map (subst_form S') (Γ ∖ {[α]})) with ((gmultiset_map (subst_form S') Γ) ∖ {[subst_form S' (α) ]})
      by (rewrite (gmultiset_map_distr_singleton_diff (subst_form S') Γ α inj_subst_form_S); ms)
  (* | |- (gmultiset_map (subst_form (upN ?n S)) (?Γ ∖ {[ ?α ]})) ⊢ _=> (* Case for upN *)
      replace (gmultiset_map (subst_form (upN n S)) (Γ ∖ {[α]})) with ((gmultiset_map (subst_form (upN n S)) Γ) ∖ {[subst_form (upN n S) (α) ]})
      by (rewrite (gmultiset_map_distr_singleton_diff (subst_form (upN n S)) Γ α (inj_subst_upN_S n)); ms) *)
  | |- context[(gmultiset_map (subst_form (upN ?n S')) (?Γ ∖ {[ ?α ]}))] =>
      replace (gmultiset_map (subst_form (upN n S')) (Γ ∖ {[α]})) with ((gmultiset_map (subst_form (upN n S')) Γ) ∖ {[subst_form (upN n S') (α) ]})
      by (rewrite (gmultiset_map_distr_singleton_diff (subst_form (upN n S')) Γ α (inj_subst_form_upN_S n)); ms)
  end.

Ltac map_diff_singleton :=
  match goal with
  | |- context[(gmultiset_map (subst_form S') ?Γ) ∖ {[ subst_form S' ?α ]}] =>
      replace (gmultiset_map (subst_form S') Γ ∖ {[ subst_form S' α ]}) with (gmultiset_map (subst_form S') (Γ ∖ {[α]}))
      by (apply (gmultiset_map_distr_singleton_diff (subst_form S') (Γ) (α) inj_subst_form_S))
  | |- context[(gmultiset_map (subst_form (upN ?n S')) ?Γ) ∖ {[ subst_form (upN ?n S') ?α ]}] =>
      replace (gmultiset_map (subst_form (upN n S')) Γ ∖ {[ subst_form (upN n S') α ]}) with (gmultiset_map (subst_form (upN n S')) (Γ ∖ {[α]}))
      by (apply (gmultiset_map_distr_singleton_diff (subst_form (upN n S')) (Γ) (α) (inj_subst_form_upN_S n)))
  end.

Theorem weakening φ' Γ φ : Γ ⊢ φ -> Γ•φ' ⊢ φ.
Proof with (auto with proof).
intro H. revert φ'.  induction H; intro φ'; auto with proof; try (exch 0; auto with proof).
- constructor 4. exch 1; exch 0...
- constructor 7; exch 0...
- constructor 8; exch 0...
- exch 1; constructor 9; exch 1; exch 0...
- constructor 10; exch 0...
- constructor 11. exch 1; exch 0...
- apply ImpLImp. exch 1. exch 0; auto with proof. exch 0...
- apply ForAllR; forward_map...
- apply ForAllL with (t := t); exch 1; exch 0...
- apply ExistsR with (t := t)...
- apply ExistsL; forward_map; exch 0...
- apply ImpLForAll; exch 0...
- apply ImpLExists; exch 0...
Defined.

Global Hint Resolve weakening : proof.

Theorem generalised_weakeningL (Γ Γ' : env) φ: Γ ⊢ φ -> Γ' ⊎ Γ ⊢ φ.
Proof.
intro Hp.
induction Γ' as [| x Γ' IHΓ'] using gmultiset_rec.
- peapply Hp.
- peapply (weakening x). exact IHΓ'. ms.
Qed.

Theorem generalised_weakeningR (Γ Γ' : env) φ: Γ' ⊢ φ -> Γ' ⊎ Γ ⊢ φ.
Proof.
intro Hp.
induction Γ as [| x Γ IHΓ] using gmultiset_rec.
- peapply Hp.
- peapply (weakening x). exact IHΓ. ms.
Qed.

Global Hint Extern 5 (?a <= ?b) => simpl in *; lia : proof.

(** ** Inversion rules *)

(** We prove that the following rules are invertible: implication right, and
  left, or left, top left (i.e., the appliction of weakening for the formula
  top), the four implication left rules, the and right rule and the application of the or right rule with bottom. *)

Lemma ImpR_rev Γ φ ψ :
  (Γ ⊢ (φ →  ψ))
    -> Γ•φ ⊢  ψ.
Proof with (auto with proof).
intro Hp. dependent induction Hp; auto with proof; try exch 0.
- constructor 4. exch 1; exch 0...
- constructor 7; exch 0...
- exch 1; constructor 9; exch 1; exch 0...
- constructor 10; exch 0...
- constructor 11. exch 1; exch 0...
- constructor 12. exch 1; exch 0; auto with proof. exch 0...
- apply ForAllL with (t := t); exch 1; exch 0...
- apply ExistsL; forward_map; exch 0...
- apply ImpLForAll; exch 0...
- apply ImpLExists; exch 0...  
Qed.

Global Hint Resolve ImpR_rev : proof.

Theorem generalised_axiom Γ φ : Γ • φ ⊢ φ.
Proof with (auto with proof).
remember (weight φ) as w.
assert(Hle : weight φ ≤ w) by lia.
clear Heqw. revert Γ φ Hle.
induction w; intros Γ φ Hle.
- assert (Hφ := weight_pos φ). lia.
- destruct φ; simpl in Hle...
  dependent destruction φ1.
  + constructor 8. exch 0...
  + auto with proof.
  + apply ImpR, AndL. exch 1; exch 0. apply ImpLAnd.
    exch 0. apply ImpR_rev. exch 0...
  + apply ImpR. exch 0. apply ImpLOr.
    exch 1; exch 0...
  + apply ImpR. exch 0...
  + apply ImpR.
    exch 0.
    apply ImpLForAll.
    auto with proof.
    auto with proof.
  + apply ImpR.
    exch 0.
    apply ImpLExists.
    exch 0.
    apply ExistsL.
    forward_map.
    exch 0.
    simpl.
    apply ForAllL with (t := var 0).
    exch 1.
    exch 0.
    simpl.
    apply ImpR_rev.    
    rewrite !subst_form_compose_pt, !bind_var_0_upS_ident, !subst_form_ident.
    apply  IHw.
    simpl.
    inversion Hle.
    pose (weight_subst_S φ2).
    lia.
    pose (weight_subst_S φ2).
    simpl in Hle.
    lia.
  + apply ForAllR.
    forward_map.
    simpl.
    apply ForAllL with (t := var 0).
    rewrite !subst_form_compose_pt,  bind_var_0_upS_ident, subst_form_ident.
    auto with proof.
  + apply ExistsL.
    simpl.
    apply ExistsR with (t := var 0).
    rewrite !subst_form_compose_pt,  bind_var_0_upS_ident, subst_form_ident.
    auto with proof.
Qed.

Global Hint Resolve generalised_axiom : proof.

Theorem modus_ponens Γ (φ ψ : form) : Γ • φ • (φ → ψ) ⊢ ψ.
Proof.
  exch 0.
  apply ImpR_rev.
  apply generalised_axiom.
Qed.

Local Ltac lazy_apply th:=
(erewrite proper_Provable;  [| |reflexivity]);  [eapply th|].

Local Hint Resolve env_in_add : proof.

Lemma AndL_rev Γ φ ψ θ: (Γ•φ ∧ ψ) ⊢ θ  → (Γ•φ•ψ) ⊢ θ.
Proof.
intro Hp.
remember (Γ•φ ∧ ψ) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ φ ∧ ψ ]}) by ms.
assert(Hin : (φ ∧ ψ) ∈ Γ')by ms.
rw Heq 2. clear Γ HH Heq. revert φ ψ Hin.
(* we massaged the goal so that the environment of the derivation on which we do
   the induction is not composite anymore *)
induction Hp; intros φ0 ψ0 Hin.
(* auto takes care of the right rules easily *)
- forward. auto with proof.
- forward. auto with proof.
- apply AndR; auto with proof.
(* the main case *)
- (* TODO: forward gets stuck there. *)
  case(decide ((φ ∧ ψ) = (φ0 ∧ ψ0))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp.
  + forward. constructor 4. exch 0. backward. backward. apply IHHp. ms.
(* only left rules remain. Now it's all a matter of putting the right principal
   formula at the front, apply the rule; and put back the front formula at the back
   before applying the induction hypothesis *)
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward. constructor 7; backward; [apply IHHp1 | apply IHHp2]; ms.
- constructor 8. backward. apply IHHp. ms.
- forward. forward. exch 0. constructor 9. exch 0. do 2 backward. apply IHHp. ms.
- forward. constructor 10. backward. apply IHHp. ms.
- forward. constructor 11. exch 0. do 2 backward. apply IHHp. ms.
- forward. constructor 12; backward.
  + forward; exch 0; backward; backward. apply IHHp1. ms.
  + apply IHHp2. ms.
- apply ForAllR; forward_map; forward_map;

    unmap_diff_singleton. apply IHHp.
  replace ((subst_form S' φ0) ∧ (subst_form S' ψ0)) with (subst_form S' (φ0 ∧ ψ0)) by reflexivity.
  now apply (gmultiset_map_elem_of).
- forward; apply ForAllL with (t := t); exch 0; do 2 backward; apply IHHp; ms.
- apply ExistsR with (t := t); now apply IHHp.
- forward; apply ExistsL; forward_map; forward_map.
  unmap_diff_singleton.
  apply (gmultiset_map_elem_of (subst_form S')) in Hin0.
  backward; apply IHHp; ms.
- forward; apply ImpLForAll; backward. now apply IHHp1. apply IHHp2. ms.
- forward; apply ImpLExists; backward; apply IHHp; ms.
Qed.

Lemma OrL_rev Γ φ ψ θ: (Γ•φ ∨ ψ) ⊢ θ  → (Γ•φ ⊢ θ) * (Γ•ψ ⊢ θ).
Proof.
intro Hp.
remember (Γ•φ ∨ ψ) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ φ ∨ ψ ]}) by ms.
assert(Hin : (φ ∨ ψ) ∈ Γ')by ms.
assert(Heq' : ((Γ' ∖ {[φ ∨ ψ]}•φ) ⊢ θ) * ((Γ' ∖ {[φ ∨ ψ]}•ψ) ⊢ θ));
[| split; rw Heq 1; tauto].
clear Γ HH Heq.
revert φ ψ Hin.
induction Hp.
- split; forward; auto with proof.
- split; forward; auto with proof.
- split; constructor 3; now (apply IHHp1 || apply IHHp2).
- split; forward; constructor 4; exch 0; do 2 backward; apply IHHp; ms.
- split; constructor 5; now apply IHHp.
- split; apply OrR2; now apply IHHp.
- intros; case (decide ((φ0 ∨ ψ0) = (φ ∨ ψ))); intro Heq0.
  + dependent destruction Heq0; subst. split; [peapply Hp1| peapply Hp2].
  + split; forward; constructor 7; backward; (apply IHHp1||apply IHHp2); ms.
- split; constructor 8; backward; apply IHHp; ms.
- split; do 2 forward; exch 0; constructor 9; exch 0; do 2 backward; apply IHHp; ms.
- split; forward; constructor 10; backward; apply IHHp; ms.
- split; forward; constructor 11; exch 0; do 2 backward; apply IHHp; ms.
- split; forward; constructor 12; backward;
    ((forward; exch 0; backward; backward; apply IHHp1) || apply IHHp2); ms. 
- split; apply ForAllR; forward_map; unmap_diff_singleton; simpl; apply IHHp;
    replace ((subst_form S' φ0) ∨ (subst_form S' ψ)) with (subst_form S' (φ0 ∨ ψ)) by reflexivity;
    now apply (gmultiset_map_elem_of).
- split; forward; apply ForAllL with (t := t); exch 0; backward; backward; apply IHHp; ms.
- split; apply ExistsR with (t := t); now apply IHHp.
- split; forward; apply ExistsL; forward_map; unmap_diff_singleton;
  apply (gmultiset_map_elem_of (subst_form S')) in Hin0;
  backward; apply IHHp; ms.
- split; forward; apply ImpLForAll; backward; try apply IHHp1; try apply IHHp2;  ms.
- split; forward; apply ImpLExists; backward; apply IHHp; ms.
Qed.

Lemma TopL_rev Γ φ θ: Γ•(⊥ → φ) ⊢ θ -> Γ ⊢ θ.
Proof.
remember (Γ•(⊥ → φ)) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ ⊥ → φ ]}) by ms.
assert(Hin : (⊥ → φ) ∈ Γ')by ms. clear HH.
intro Hp. rw Heq 0.
clear Γ Heq. revert Hin; revert φ; induction Hp; intros φ' Hin;
try forward.
- auto with proof.
- auto with proof.
- auto with proof.
- constructor 4. exch 0. do 2 backward. apply IHHp.  ms.
- auto with proof.
- auto with proof.
- constructor 7; backward; [apply IHHp1 | apply IHHp2];  ms.
- constructor 8. backward. apply IHHp. ms.
- forward. exch 0. constructor 9. exch 0. do 2 backward. apply IHHp. ms.
- constructor 10. backward. apply IHHp. ms.
- constructor 11. exch 0. do 2 backward. apply IHHp. ms.
- constructor 12; backward;  [
      forward; exch 0; backward; backward; apply IHHp1 | apply IHHp2
    ];  ms.
- apply ForAllR. unmap_diff_singleton. simpl. apply IHHp.
  apply (gmultiset_map_elem_of (subst_form S')) in Hin. ms.
- apply ForAllL with (t := t); exch 0; backward; backward; apply IHHp; ms.
- apply ExistsR with (t := t);  apply IHHp; ms.
- apply ExistsL. unmap_diff_singleton; apply (gmultiset_map_elem_of (subst_form S')) in Hin0;
  backward. simpl; apply IHHp; ms.
- apply ImpLForAll; backward. apply IHHp1. ms; backward. apply IHHp2. ms.
- apply ImpLExists; backward; apply IHHp; ms.
Qed.

Local Hint Immediate TopL_rev : proof.

Lemma ImpL0_rev (Γ : env) i xs φ ψ: Γ • (Atom i xs) • ((Atom i xs) → φ) ⊢ ψ  →
                                                      Γ • (Atom i xs) • φ ⊢ ψ.
Proof.
intro Hp.
remember (Γ•Atom i xs•(Atom i xs → φ)) as Γ' eqn:HH.
assert (Heq: (Γ•Atom i xs) ≡ Γ' ∖ {[Atom i xs → φ]}) by ms.
assert(Hin : (Atom i xs → φ) ∈ Γ')by ms.
rw Heq 1. clear Γ HH Heq.
revert Hin. revert φ i xs.
induction Hp; intros; apply (gmultiset_map_elem_of (subst_form S')) in Hin as Hin'.
- forward; auto with proof.
- forward; auto with proof.
- apply AndR; auto with proof.
- forward; apply AndL. exch 0. do 2 backward. apply IHHp. ms.
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward; apply OrL; backward; apply IHHp1 || apply IHHp2; ms.
- apply ImpR. backward. apply IHHp. ms.
- case (decide ((Atom i0 xs0 → φ0) = (Atom i xs → φ))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp.
  + do 2 forward. exch 0. apply ImpL0. exch 0; do 2 backward. apply IHHp. ms.
- forward; apply ImpLAnd. backward. apply IHHp. ms.
- forward; apply ImpLOr. exch 0; do 2 backward. apply IHHp. ms.
- forward; apply ImpLImp; backward;
    ( (forward; exch 0; backward; backward; apply IHHp1) || apply IHHp2); ms. 
- apply ForAllR. forward_map. unmap_diff_singleton. simpl. apply IHHp. ms.
- forward. apply ForAllL with (t := t). exch 0. do 2 backward. apply IHHp. ms.
- apply ExistsR with (t := t). apply IHHp. ms.
- forward. apply ExistsL. forward_map. unmap_diff_singleton. backward. apply IHHp. ms.
- forward. apply ImpLForAll. backward. apply IHHp1. ms. backward. apply IHHp2. ms.
- forward. apply ImpLExists. backward. apply IHHp. ms.
Qed.

(* inversion for ImpLImp is only partial *)
Lemma ImpLImp_prev Γ φ1 φ2 φ3 ψ: (Γ•((φ1 → φ2) → φ3)) ⊢ ψ -> (Γ•φ3) ⊢ ψ.
Proof.
intro Hp.
remember (Γ •((φ1 → φ2) → φ3)) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ ((φ1 → φ2) → φ3) ]}) by ms.
assert(Hin :((φ1 → φ2) → φ3) ∈ Γ')by ms.
rw Heq 1. clear Γ HH Heq.
revert φ1 φ2 φ3 Hin.
induction Hp; intros; apply (gmultiset_map_elem_of (subst_form S')) in Hin as Hin'.
- forward; auto with proof.
- forward; auto with proof.
- apply AndR; auto with proof.
- forward; apply AndL. exch 0; do 2 backward. apply IHHp. ms.
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward; apply OrL; backward; [apply IHHp1 | apply IHHp2]; ms.
- apply ImpR. backward. apply IHHp. ms.
- do 2 forward. exch 0. apply ImpL0. exch 0. do 2 backward. apply IHHp. ms.
- forward; apply ImpLAnd. backward. apply IHHp. ms.
- forward; apply ImpLOr. exch 0. do 2 backward. apply IHHp. ms.
- case (decide (((φ0 → φ4) → φ5) = ((φ1 → φ2) → φ3))); intro Heq0.
  + dependent destruction Heq0; subst. rewrite env_add_remove. easy.
  + forward. apply ImpLImp; backward;
      ((forward; exch 0; backward; backward; apply IHHp1) || apply IHHp2); ms. 
- apply ForAllR. forward_map. unmap_diff_singleton. simpl. apply IHHp. ms. 
- forward. apply ForAllL with (t := t). exch 0. do 2 backward. apply IHHp. ms.
- apply ExistsR with (t := t). apply IHHp. ms.
- forward. apply ExistsL. forward_map. unmap_diff_singleton. simpl. backward. apply IHHp. ms.
- forward. apply ImpLForAll. backward. apply IHHp1. ms. backward. apply IHHp2. ms.
- forward. apply ImpLExists. backward. apply IHHp. ms.
Qed.
       
Lemma ImpLOr_rev Γ φ1 φ2 φ3 ψ:
  Γ•((φ1 ∨ φ2) → φ3) ⊢ ψ -> Γ•(φ1 → φ3)•(φ2 → φ3) ⊢ ψ.
Proof.
intro Hp.
remember (Γ •((φ1 ∨ φ2) → φ3)) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ ((φ1 ∨ φ2) → φ3) ]}) by ms.
assert(Hin :((φ1 ∨ φ2) → φ3) ∈ Γ')by ms.
rw Heq 2. clear Γ HH Heq.
revert φ1 φ2 φ3 Hin.
induction Hp; intros; apply (gmultiset_map_elem_of (subst_form S')) in Hin as Hin'.
- forward; auto with proof.
- forward; auto with proof.
- apply AndR; auto with proof.
- forward; constructor 4. exch 0; do 2 backward. apply IHHp. ms.
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward; constructor 7; backward; [apply IHHp1 | apply IHHp2]; ms.
- constructor 8. backward. apply IHHp. ms.
- do 2 forward. exch 0. constructor 9. exch 0. do 2 backward. apply IHHp. ms.
- forward; constructor 10. backward. apply IHHp. ms.
- case (decide (((φ0 ∨ φ4) → φ5) = ((φ1 ∨ φ2) → φ3))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp.
  + forward. constructor 11; exch 0; do 2 backward; apply IHHp; ms.
- forward; constructor 12; backward;
    ((forward; exch 0; backward; backward; apply IHHp1) || apply IHHp2); ms. 
- apply ForAllR. repeat forward_map. unmap_diff_singleton. apply IHHp. ms.
- forward. apply ForAllL with (t := t). exch 0. do 2 backward. apply IHHp. ms.
- apply ExistsR with (t := t). apply IHHp. ms.
- forward. apply ExistsL. repeat forward_map. unmap_diff_singleton. backward. apply IHHp. ms.
- forward. apply ImpLForAll. backward. apply IHHp1. ms. backward. apply IHHp2. ms.
- forward. apply ImpLExists. backward. apply IHHp. ms.
Qed.

Lemma ImpLAnd_rev Γ φ1 φ2 φ3 ψ: (Γ•(φ1 ∧ φ2 → φ3)) ⊢ ψ ->  (Γ•(φ1 → φ2 → φ3)) ⊢ ψ .
Proof.
intro Hp.
remember (Γ •((φ1 ∧ φ2) → φ3)) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ ((φ1 ∧ φ2) → φ3) ]}) by ms.
assert(Hin :((φ1 ∧ φ2) → φ3) ∈ Γ')by ms.
rw Heq 1. clear Γ HH Heq.
revert φ1 φ2 φ3 Hin.
induction Hp; intros; apply (gmultiset_map_elem_of (subst_form S')) in Hin as Hin'.
- forward; auto with proof.
- forward; auto with proof.
- apply AndR; auto with proof.
- forward; constructor 4. exch 0; do 2 backward. apply IHHp. ms.
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward; constructor 7; backward; [apply IHHp1 | apply IHHp2]; ms.
- constructor 8. backward. apply IHHp. ms.
- do 2 forward. exch 0. constructor 9. exch 0. do 2 backward. apply IHHp. ms.
- case (decide (((φ0 ∧ φ4) → φ5) = ((φ1 ∧ φ2) → φ3))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp.
  + forward. constructor 10. backward. apply IHHp. ms.
- forward; constructor 11; exch 0; do 2 backward; apply IHHp; ms.
- forward; constructor 12; backward;
    ((forward; exch 0; backward; backward; apply IHHp1) || apply IHHp2); ms. 
- apply ForAllR. forward_map. unmap_diff_singleton. apply IHHp. ms.
- forward. apply ForAllL with (t := t). exch 0. do 2 backward. apply IHHp. ms.
- apply ExistsR with (t := t). apply IHHp. ms.
- forward. apply ExistsL. repeat forward_map. unmap_diff_singleton. backward. apply IHHp. ms.
- forward. apply ImpLForAll. backward. apply IHHp1. ms. backward. apply IHHp2. ms.
- forward. apply ImpLExists. backward. apply IHHp. ms.
Qed.

Global Hint Resolve AndL_rev : proof.
Global Hint Resolve OrL_rev : proof.
Global Hint Resolve ImpL0_rev : proof.
Global Hint Resolve ImpLOr_rev : proof.
Global Hint Resolve ImpLAnd_rev : proof.

Lemma exfalso Γ : forall φ, Γ ⊢ ⊥ -> Γ ⊢ φ.
Proof.
  intros φ Hp. revert φ.
  dependent induction Hp; try tauto; auto with proof; try tauto.
  intros φ0. apply ForAllL with (t := t); apply IHHp; tauto. 
Qed.

Global Hint Immediate exfalso : proof.

Lemma AndR_revL {Γ φ1 φ2} : Γ ⊢ φ1 ∧ φ2 -> (Γ ⊢ φ1).
Proof.
  intro Hp. dependent induction Hp;
    try specialize (IHHp _ _ eq_refl);
    try specialize (IHHp1 _ _ eq_refl);
    try specialize (IHHp2 _ _ eq_refl);
    intuition;
    auto with proof.
  apply ForAllL with (t := t); easy.
Qed.

Lemma AndR_revR {Γ φ1 φ2} : Γ ⊢ φ1 ∧ φ2 -> (Γ ⊢ φ2).
Proof.
  intro Hp. dependent induction Hp;
    try specialize (IHHp _ _ eq_refl);
    try specialize (IHHp1 _ _ eq_refl);
    try specialize (IHHp2 _ _ eq_refl);
    intuition;
    auto with proof.
  apply ForAllL with (t := t); easy.
Qed.

Lemma AndR_rev {Γ φ1 φ2} : Γ ⊢ φ1 ∧ φ2 -> (Γ ⊢ φ1) * (Γ ⊢ φ2).
Proof.
  intros Hp.
  split; [ apply (AndR_revL Hp) | apply (AndR_revR Hp) ].
Qed.

(** A general inversion rule for disjunction is not admissible. However, inversion holds if one of the formulas is ⊥. *)

Lemma OrR1Bot_rev Γ φ :  Γ ⊢ φ ∨ ⊥ -> Γ ⊢ φ.
Proof. intro Hd.
       dependent induction Hd generalizing φ; auto using exfalso with proof.
       apply ForAllL with (t := t). auto with proof.
Qed.

Lemma OrR2Bot_rev Γ φ :  Γ ⊢ ⊥ ∨ φ -> Γ ⊢ φ.
Proof. intro Hd. dependent induction Hd; auto using exfalso with proof.
       apply ForAllL with (t := t). auto with proof.
Qed.

Lemma specialise_term Γ ψ t : forall n,
    Γ ⊢ ψ -> (gmultiset_map (subst_form (upN n (bind_var t))) Γ) ⊢ (subst_form (upN n (bind_var t)) ψ).
Proof.
  intros n Hp. revert n t.
  dependent induction Hp; intros; simpl; try (forward_map; auto with proof); simpl.
  - apply AndR. apply IHHp1. apply IHHp2.
  - apply AndL. backward_map. backward_map. apply IHHp.
  - apply OrR1. apply IHHp.
  - apply OrR2. apply IHHp.
  - apply OrL. backward_map. apply IHHp1. backward_map. apply IHHp2.
  - apply ImpR. backward_map. apply IHHp.
  - forward_map. apply ImpL0.
    change (Atom i (map (subst_term (upN n (bind_var t))) xs)) with (subst_form (upN n (bind_var t)) (Atom i xs)).
    do 2 backward_map. apply IHHp.
  - apply ImpLAnd.
    change ((subst_form (upN n (bind_var t)) φ1
             → subst_form (upN n (bind_var t)) φ2 → subst_form (upN n (bind_var t)) φ3)) with
      (subst_form (upN n (bind_var t)) ( φ1 → (φ2 → φ3) )).
    backward_map.
    apply IHHp.
  - apply ImpLOr.
    change (subst_form (upN n (bind_var t)) φ2 → subst_form (upN n (bind_var t)) φ3) with
      (subst_form (upN n (bind_var t)) (φ2 → φ3)).
    change (subst_form (upN n (bind_var t)) φ1 → subst_form (upN n (bind_var t)) φ3) with
      (subst_form (upN n (bind_var t)) (φ1 → φ3)).
    do 2 backward_map.
    apply IHHp.
  - apply ImpLImp.
    change (subst_form (upN n (bind_var t)) φ2 → subst_form (upN n (bind_var t)) φ3) with
      (subst_form (upN n (bind_var t)) (φ2 → φ3)).
    do 2 backward_map.
    apply IHHp1.
    backward_map.
    apply IHHp2.
  - apply ForAllR.
    rewrite gmultiset_map_compose.
    replace (subst_form S' ∘ subst_form (upN n (bind_var t)))
      with  (subst_form (upN (S n) (bind_var t)) ∘ subst_form S')
      by (rewrite !subst_form_compose; f_equal).
    rewrite <- gmultiset_map_compose.
    apply IHHp.
  - apply ForAllL with (t := subst_term (upN n (bind_var t0)) t).
    change (ForAll (subst_form (up (upN n (bind_var t0))) φ)) with
      (subst_form (upN n (bind_var t0)) (ForAll φ)).
    backward_map.
    rewrite subst_form_compose_pt.
    change (up (upN n (bind_var t0))) with (upN (S n) (bind_var t0)).
    rewrite <- upN_bind_var_t_bind_var_u_commute.
    rewrite <- subst_form_compose_pt.
    backward_map.
    apply IHHp.
  - apply ExistsR with (t := subst_term (upN n (bind_var t0)) t).
    rewrite subst_form_compose_pt.
    change (up (upN n (bind_var t0))) with (upN (S n) (bind_var t0)).
    rewrite <- upN_bind_var_t_bind_var_u_commute.
    rewrite <- subst_form_compose_pt.
    apply IHHp.
  - apply ExistsL.
    rewrite gmultiset_map_compose, !subst_form_compose_pt.
    replace (subst_form S' ∘ subst_form (upN n (bind_var t)))
      with  (subst_form (upN (S n) (bind_var t)) ∘ subst_form S')
      by (rewrite !subst_form_compose; f_equal).
    rewrite <- gmultiset_map_compose.
    change (up (upN n (bind_var t))) with (upN (S n) (bind_var t)).
    backward_map.
    replace (subst_form (S' ☉ upN n (bind_var t)) ψ)
      with (subst_form (upN (S n) (bind_var t)) (subst_form S' ψ))
        by (rewrite subst_form_compose_pt; f_equal).
    apply IHHp.
  - apply ImpLForAll.
    change ((ForAll (subst_form (up (upN n (bind_var t))) φ1)) → subst_form (upN n (bind_var t)) φ2)
      with ((subst_form (upN n (bind_var t)) ( (ForAll φ1) → φ2))).
    backward_map.
    apply IHHp1.
    backward_map.
    apply IHHp2.
  - apply ImpLExists.
    rewrite subst_form_compose_pt.
    replace (subst_form (S' ☉ upN n (bind_var t)) φ2)
       with (subst_form (upN (S n) (bind_var t)) (subst_form S' φ2))
         by (rewrite subst_form_compose_pt; f_equal).
    change (ForAll ( subst_form (up (upN n (bind_var t))) φ1 → subst_form (upN (S n) (bind_var t)) (subst_form S' φ2)))
      with (subst_form (upN n (bind_var t)) (ForAll (φ1 → (subst_form S' φ2)))).
    backward_map.
    apply IHHp.
Qed.

Lemma specialise_evar  Γ φ0 ψ t : forall n,
    (gmultiset_map (subst_form (upN n S')) Γ • φ0) ⊢ subst_form (upN n S') ψ ->
    (Γ • subst_form (upN n (bind_var t)) φ0) ⊢ ψ.
Proof.
  intros.
  remember (gmultiset_map (subst_form (upN n S')) Γ • φ0) as Γ'.
  remember (subst_form (upN n S') ψ) as θ.
  (* Rewrite so mapping are in the goal, so we can use specialise_term *)
  replace Γ with ( gmultiset_map (subst_form ( upN n (bind_var t) ) ) (Γ' ∖ {[ φ0 ]}) ) by (
      rewrite HeqΓ', env_add_remove, gmultiset_map_compose, subst_form_compose, upN_compose, upN_ident, subst_form_ident, gmultiset_map_ident; easy
    ).
  replace ψ with (subst_form (upN n (bind_var t)) θ) by (
      rewrite  Heqθ, subst_form_compose_pt, upN_compose, upN_ident, subst_form_ident; easy
    ).
  backward_map.
  apply specialise_term.
  (* Reduce to Γ' ⊢ θ  *)
  case (decide (φ0 ∈ Γ')); intros Hin; [
      replace (Γ' ∖ {[ φ0 ]} • φ0) with (Γ') by multiset_solver | 
      replace (Γ' ∖ {[ φ0 ]}) with (Γ') by (pose (diff_not_in Γ' φ0 Hin); ms); apply weakening
    ]; easy.
Qed.

Lemma specialise_evar2 Γ φ t n :
    (gmultiset_map (subst_form (upN n S')) Γ) ⊢ φ ->
    Γ ⊢ subst_form (upN n (bind_var t)) φ.
Proof.
    intro H.
    replace Γ with (gmultiset_map (subst_form (upN n (bind_var t)))
                      (gmultiset_map (subst_form (upN n S')) Γ)).
    apply specialise_term with (t := t) (n := n) in H.
    apply H.
    rewrite gmultiset_map_compose, subst_form_compose, upN_compose.
    simpl.
    rewrite upN_ident, subst_form_ident, gmultiset_map_ident.
    easy.
Qed.

Lemma ExistsL_rev_specialised Γ φ ψ t: 
  Γ • (Exists φ) ⊢ ψ -> Γ • (subst_form (bind_var t) φ) ⊢ ψ.
Proof.
  intros Hp.
  remember (Γ • (Exists φ)) as Γ'.
  assert ((Exists φ) ∈ Γ') as Hin by ms.
  assert (Γ = Γ' ∖ {[ (Exists φ) ]} ) as Heq by ms.
  rewrite Heq.
  clear Γ HeqΓ' Heq.
  revert Hin. revert φ t.
  induction Hp; intros; 
    apply (gmultiset_map_elem_of (subst_form S')) in Hin as Hin'.
  - forward. apply Init.
  - forward. apply ExFalso.
  - apply AndR. apply IHHp1. ms. apply IHHp2. ms.
  - forward. apply AndL. exch 0. do 2 backward. apply IHHp. ms.
  - apply OrR1. apply IHHp. ms.
  - apply OrR2. apply IHHp. ms.
  - forward. apply OrL. backward. apply IHHp1. ms. backward. apply IHHp2. ms.
  - apply ImpR. backward. apply IHHp. ms.
  - forward. forward. exch 0. apply ImpL0. exch 0. do 2 backward. apply IHHp. ms.
  - forward. apply ImpLAnd. backward. apply IHHp. ms.
  - forward. apply ImpLOr. exch 0. do 2 backward. apply IHHp. ms.
  - forward. apply ImpLImp. exch 0. do 2 backward. apply IHHp1. ms. backward. apply IHHp2. ms.
  - apply ForAllR. forward_map. unmap_diff_singleton. simpl.
    rewrite subst_form_compose_pt,  f_bind_var_t_commute.
    replace ( subst_form (bind_var (subst_term S' t) ☉ up S') φ0) with
      ( subst_form ( bind_var (subst_term S' t)) (subst_form (up S') φ0))
    by (rewrite subst_form_compose_pt; f_equal).
    apply IHHp.
    simpl in Hin'.
    ms.
  - forward. apply ForAllL with (t := t). exch 0. do 2 backward. apply IHHp. ms.
  - apply ExistsR with (t := t). apply IHHp. ms.
  - case (decide (φ = φ0)); intros.
    + subst. rewrite env_add_remove. apply specialise_evar with (n := 0). easy.
    + forward. apply ExistsL. forward_map. unmap_diff_singleton.
      simpl.
      rewrite subst_form_compose_pt, f_bind_var_t_commute.
      
    replace ( subst_form (bind_var (subst_term S' t) ☉ up S') φ0) with
      ( subst_form ( bind_var (subst_term S' t)) (subst_form (up S') φ0))
      by (rewrite subst_form_compose_pt; f_equal).
      apply (gmultiset_map_elem_of (subst_form S')) in Hin0.
      backward.
      apply IHHp.
      ms.
  - forward. apply ImpLForAll. backward. apply IHHp1. ms. backward. apply IHHp2. ms.
  - forward. apply ImpLExists. backward. apply IHHp. ms.
Qed.

Ltac forward2 :=
  match goal with
  | |- context[ (?Γ • ?φ) ∖ {[ ?ψ ]} ] =>
      let Hin := fresh "Hin" in
      assert (Hin : ψ ∈ Γ) by ms;
      replace ((Γ • φ) ∖ {[ ψ ]}) with
        ((Γ ∖ {[ ψ ]}) •  φ) by ( pose (env_replace φ Hin); ms )
  end.
Ltac backward2 :=
  match goal with
  | |- context[ (?Γ ∖ {[ ?ψ ]}) • ?φ ] =>
      let Hin := fresh "Hin" in
      assert (Hin : ψ ∈ Γ) by ms;
      replace ((Γ ∖ {[ ψ ]}) • φ) with
        ((Γ •  φ)∖ {[ ψ ]}) by ( pose (env_replace φ Hin); ms )
  end.

(** An auxiliary definition of **height** of a proof, measured along the leftmost branch. *)
Fixpoint height {Γ φ} (Hp : Γ ⊢ φ) := match Hp with
| Init _ _ _ => 1
| ExFalso _ _ => 1
| AndR Γ φ ψ H1 H2 => 1 + height H1 + height H2
| AndL Γ φ ψ θ H => 1 + height H
| OrR1 Γ φ ψ H => 1 + height H
| OrR2 Γ φ ψ H => 1 + height H
| OrL Γ φ ψ θ H1 H2 => 1 + height H1 + height H2
| ImpR Γ φ ψ H => 1 + height H
| ImpL0 Γ _ _ φ ψ H => 1 + height H
| ImpLAnd Γ φ1 φ2 φ3 ψ H => 1 + height H
| ImpLOr Γ φ1 φ2 φ3 ψ H => 1 + height H
| ImpLImp Γ φ1 φ2 φ3 ψ H1 H2 => 1 + height H1 + height H2
| ForAllR Γ φ H => 1 + height H
| ForAllL Γ φ ψ t H => 1 + height H
| ExistsR Γ φ t H => 1 + height H
| ExistsL Γ φ ψ H => 1 + height H
| ImpLForAll Γ φ1 φ2 ψ H1 H2 => 1 + height H1 + height H2
| ImpLExists Γ φ1 φ2 ψ H => 1 + height H
end.

Lemma height_0 {Γ φ} (Hp : Γ ⊢ φ) : height Hp <> 0.
Proof. destruct Hp; simpl; lia. Qed.

Lemma relabelling_lemma Γ ψ f :
  Γ ⊢ ψ -> (gmultiset_map (subst_form f) Γ) ⊢ (subst_form f ψ).
Proof.
  intros Hp.
  revert f.
  induction Hp; intros; simpl.
  - forward_map. apply Init.
  - forward_map. apply ExFalso.
  - apply AndR; [ apply IHHp1 | apply IHHp2 ].
  - forward_map. simpl. apply AndL.
    backward_map. backward_map. apply IHHp.
  - apply OrR1. apply IHHp.
  - apply OrR2. apply IHHp.
  - forward_map. simpl. apply OrL; backward_map; [ apply IHHp1 |  apply IHHp2].
  - apply ImpR. backward_map. apply IHHp.
  - do 2 forward_map. simpl. apply ImpL0.
    change (Atom i (map (subst_term f) xs)) with (subst_form f (Atom i xs)).
    do 2 backward_map. apply IHHp.
  - forward_map. simpl. apply ImpLAnd.
    change (φ1 〔 f 〕 → φ2 〔 f 〕 → φ3 〔 f 〕) with ((φ1 → φ2 → φ3) 〔 f 〕).
    backward_map. apply IHHp.
  - forward_map. simpl. apply ImpLOr.
    change (φ1 〔 f 〕 → φ3 〔 f 〕) with ((φ1 → φ3)〔 f 〕).
    change (φ2 〔 f 〕 → φ3 〔 f 〕) with ((φ2  → φ3)〔 f 〕).
    do 2 backward_map. apply IHHp.
  - forward_map. simpl. apply ImpLImp.
    change (φ2 〔 f 〕 → φ3 〔 f 〕) with ((φ2 → φ3)〔 f 〕).
    do 2 backward_map. apply IHHp1.
    backward_map. apply IHHp2.
  - apply ForAllR.
    rewrite gmultiset_map_compose, subst_form_compose.
    change (S' ☉ f) with ((up f) ☉  S').
    rewrite <- subst_form_compose.
    rewrite <- gmultiset_map_compose.
    apply IHHp.
  - forward_map. simpl. apply ForAllL with (t := subst_term f t).
    change ( ForAll (subst_form (up f) φ) ) with (subst_form f (ForAll φ)).
    backward_map.
    rewrite subst_form_compose_pt.
    rewrite <- f_bind_var_t_commute, <- subst_form_compose_pt.
    backward_map.
    apply IHHp.
  - apply ExistsR with (t := subst_term f t).
    rewrite subst_form_compose_pt.
    rewrite <- f_bind_var_t_commute, <- subst_form_compose_pt.
    apply IHHp.
  - forward_map. simpl. apply ExistsL.
    rewrite subst_form_compose_pt.
    rewrite gmultiset_map_compose, subst_form_compose.
    change (S' ☉ f) with ((up f) ☉  S').
    rewrite <- subst_form_compose_pt.
    rewrite <- subst_form_compose.
    rewrite <- gmultiset_map_compose.
    backward_map.
    apply IHHp.
  - forward_map. simpl. apply ImpLForAll.
    change ((ForAll φ1 〔 ⇑ f 〕) → φ2 〔 f 〕) with (((ForAll φ1) → φ2) 〔 f 〕).
    change (ForAll φ1 〔 ⇑ f 〕) with ((ForAll φ1) 〔  f 〕).
    backward_map; apply IHHp1.
    backward_map; apply IHHp2.
  - forward_map. simpl. apply ImpLExists.
    rewrite subst_form_compose_pt.
    change (S' ☉ f) with ((up f) ☉  S').
    rewrite <- subst_form_compose_pt.
    change (ForAll (φ1 〔 ⇑ f 〕 → φ2 〔 S' 〕 〔 ⇑ f 〕)) with
      ((ForAll (φ1  → φ2 〔 S' 〕) )〔 f 〕).
    backward_map.
    apply IHHp.
Qed.

Lemma reorder_ev Γ φ0 φ ψ :
  (gmultiset_map (subst_form S') (gmultiset_map (subst_form S') (Γ))) • subst_form (up S') φ0 • subst_form S' φ ⊢ subst_form S' (subst_form S' ψ) ->
  (gmultiset_map (subst_form S') (gmultiset_map (subst_form S') (Γ))) • subst_form S' φ0 • subst_form (up S') φ ⊢ subst_form S' (subst_form S' ψ).
Proof.
  rewrite !gmultiset_map_compose, !subst_form_compose, !subst_form_compose_pt in *.
  intros Hp.
  apply relabelling_lemma with (f := swap) in Hp.
  change (S' ☉ S') with (swap ☉ (S' ☉ S')).
  rewrite <- subst_form_compose.
  rewrite <- gmultiset_map_compose.
  simpl.
  rewrite swap_up_succ at 1.
  rewrite <- subst_form_compose_pt; backward_map.
  change (⇑ S') with (swap ☉ S') at 2.
  rewrite <- subst_form_compose_pt.
  backward_map.
  apply Hp.
Qed.

Lemma reorder_ev2 Γ φ0 φ :
       gmultiset_map (subst_form S') (gmultiset_map (subst_form S') (Γ))  • (subst_form (up S') φ0) ⊢ φ 〔 S' 〕 ->
  gmultiset_map (subst_form S') (gmultiset_map (subst_form S') (Γ)) • (subst_form S' φ0) ⊢ φ 〔 ⇑ S' 〕.
Proof.
  rewrite !gmultiset_map_compose, !subst_form_compose.
  intros Hp.
  apply relabelling_lemma with (f := swap) in Hp.
  change (S' ☉ S') with (swap ☉ (S' ☉ S')).
  rewrite <- subst_form_compose.
  rewrite <- gmultiset_map_compose.
  simpl.
  rewrite swap_up_succ at 1.
  rewrite <- subst_form_compose_pt; backward_map.
  change (⇑ S') with (swap ☉ S') at 2.
  rewrite <- subst_form_compose_pt.
  apply Hp.
Qed.

Lemma ExistsL_rev Γ φ ψ: 
  Γ • (Exists φ) ⊢ ψ -> (gmultiset_map (subst_form S') Γ) • φ ⊢ (subst_form S' ψ).
Proof.
  intros Hp.
  remember (Γ • (Exists φ)) as Γ'.
  assert ((Exists φ) ∈ Γ') as Hin by ms.
  assert (Γ = Γ' ∖ {[ (Exists φ) ]} ) as Heq by ms.
  rewrite Heq.
  clear Γ HeqΓ' Heq.
  revert Hin. revert φ. 
  induction Hp; intros; simpl.
    apply (gmultiset_map_elem_of (subst_form (S'))) in Hin as Hin'.
  - forward. forward_map. exch 0. apply Init.
  - forward. forward_map. exch 0. apply ExFalso.
  - apply AndR. apply IHHp1. ms. apply IHHp2. ms.
  - forward. forward_map. exch 0.  simpl. apply AndL.  exch 1. exch 0. do 2 backward_map.
            backward2. backward2. apply IHHp. ms.
  - apply OrR1. apply IHHp. ms.
  - apply OrR2. apply IHHp. ms.
  - forward. forward_map. exch 0. simpl. apply OrL. exch 0. backward_map. backward2. apply IHHp1. ms.
                                                 exch 0. backward_map. backward2. apply IHHp2. ms.
  - apply ImpR. exch 0. backward_map. backward2. apply IHHp. ms.
  - do 2 forward. do 2 forward_map. exch 0. exch 1. simpl.  apply ImpL0. exch 1. exch 0.
    change (Atom i (map (subst_term (S')) xs)) with (subst_form (S') (Atom i xs)).
    do 2 backward_map. do 2 backward2. apply IHHp. ms.                                            
  - forward. forward_map. exch 0. simpl. apply ImpLAnd. exch 0.
    change (φ1 〔 (S') 〕 → φ2 〔 (S') 〕 → φ3 〔 (S') 〕) with (subst_form (S') (φ1 → φ2 → φ3)).
    backward_map. backward2. apply IHHp. ms.
  - forward. forward_map. exch 0. simpl. apply ImpLOr.
    exch 0.
    change (φ2 〔 S' 〕 → φ3 〔 S' 〕) with (subst_form (S') (φ2 → φ3)).
    change (φ1 〔 S' 〕 → φ3 〔 S' 〕) with (subst_form (S') (φ1 → φ3)).
    exch 0. exch 1. exch 0.
    do 2 backward_map. do 2 backward2. apply IHHp. ms.
  - forward. forward_map. exch 0. simpl. apply ImpLImp. 
    change (φ2 〔 S' 〕 → φ3 〔 S' 〕) with (subst_form (S') (φ2 → φ3)).
    exch 1. exch 0. do 2 backward_map. do 2 backward2. apply IHHp1. ms.
    exch 0. backward_map. backward2. apply IHHp2. ms.
  - apply ForAllR. forward_map.
    apply reorder_ev2.
    unmap_diff_singleton.
    simpl.
    apply IHHp. apply (gmultiset_map_elem_of (subst_form S')) in Hin.
    ms.
  - forward2. repeat forward_map. exch 0. simpl. apply ForAllL with (t := (subst_term S' t)).
    exch 1. change ( ForAll (subst_form (up S') φ)) with (subst_form S' (ForAll φ)).
    backward_map.
    exch 0.
    rewrite subst_form_compose_pt.
    rewrite <- f_bind_var_t_commute.
    rewrite <- subst_form_compose_pt.
    backward_map.
    do 2 backward2.
    apply IHHp.
    ms.
  - apply ExistsR with (t := (subst_term S' t)).
    rewrite subst_form_compose_pt.
    rewrite <- f_bind_var_t_commute.
    rewrite <- subst_form_compose_pt.
    apply IHHp.
    ms.
  - case (decide (φ = φ0)); intros.
    + subst. rewrite env_add_remove. easy.
    + assert ((Exists φ0) ∈ Γ) as Hin2 by ms.
      apply (gmultiset_map_elem_of (subst_form S')) in Hin2 as Hin2'.
      unmap_diff_singleton. forward_map. forward. simpl. apply ExistsL.
      forward_map.
      change ((Exists (subst_form (up S') φ0))) with (subst_form S' (Exists φ0)).
      map_diff_singleton.
      apply reorder_ev.
      exch 0.
      backward_map.
      unmap_diff_singleton.
      backward2.
      apply IHHp.
      ms.
  - unmap_diff_singleton. forward_map. forward. simpl. exch 0. apply ImpLForAll.
    change ((ForAll (subst_form (up S') φ1)) → (subst_form S' φ2)) with (subst_form S' (ForAll φ1 → φ2)).
    exch 0.
    backward.
    backward_map.
    change (ForAll (subst_form (up S') φ1)) with (subst_form S' (ForAll φ1)).
    change (Exists (subst_form (up S') φ)) with (subst_form S' (Exists φ)).
    map_diff_singleton.
    apply IHHp1.
    ms.
    apply (gmultiset_map_elem_of (subst_form S')) in Hin as Hin'.
    simpl in Hin.
    backward.
    backward_map.
    change (Exists (subst_form (up S') φ)) with (subst_form S' (Exists φ)).
    map_diff_singleton.
    apply IHHp2.
    ms.
  - forward2. forward_map. exch 0. simpl. apply ImpLExists.
    rewrite subst_form_compose_pt.
    change (S' ☉ S') with (up S' ☉ S').
    rewrite <- subst_form_compose_pt.
    change (ForAll (subst_form (up S') φ1 → (subst_form (up S') (subst_form S' φ2))))
      with (subst_form S' (ForAll (φ1 → (subst_form S' φ2)))).
    exch 0.
    unmap_diff_singleton.
    apply (gmultiset_map_elem_of (subst_form S')) in Hin0 as Hin1.
    backward2.
    backward_map.
    map_diff_singleton.
    apply IHHp.
    ms.
Qed.

Lemma ForAllR_rev_specialised Γ φ t : Γ ⊢ (ForAll φ) -> Γ ⊢ (subst_form (bind_var t) φ).
Proof.
  intros.
  apply specialise_evar2 with (n := 0).
  simpl.
  clear t.
  remember (ForAll φ) as φ'.
  revert φ Heqφ'.
  induction H; intros; try discriminate; try repeat forward_map; simpl.
  - apply ExFalso.
  - apply AndL; do 2 backward_map; auto with proof.
  - apply OrL; backward_map; auto with proof.
  - apply ImpL0.
    change (Atom i (map (subst_term S') xs)) with
      (subst_form S' (Atom i xs)).
    do 2 backward_map.
    auto with proof.
  - apply ImpLAnd.
    change  (φ1 〔 S' 〕 → φ2 〔 S' 〕 → φ3 〔 S' 〕) with
      (subst_form S' (φ1 → φ2 → φ3)).
    backward_map.
    auto with proof.
  - apply ImpLOr.
    change (φ1 〔 S' 〕 → φ3 〔 S' 〕) with (subst_form S' (φ1 → φ3)).
    change (φ2 〔 S' 〕 → φ3 〔 S' 〕) with (subst_form S' (φ2 → φ3)).
    repeat backward_map.
    auto with proof.
  - apply ImpLImp.
    change (φ2 〔 S' 〕 → φ3 〔 S' 〕) with
      (subst_form S' (φ2 → φ3)).
    repeat backward_map.
    apply relabelling_lemma.
    easy.
    backward_map; auto with proof.
  - inversion Heqφ'; subst; easy.
  - apply ForAllL with (t := (subst_term S' t)).
    rewrite subst_form_compose_pt,  <- f_bind_var_t_commute, <- subst_form_compose_pt.
    change (ForAll (subst_form (up S') φ)) with (subst_form S' (ForAll φ)).
    repeat backward_map.
    auto with proof.
  - apply ExistsL.
    specialize IHProvable with (φ := (subst_form (up S') φ0)).
    subst.
    simpl in IHProvable.
    
    apply relabelling_lemma with (f := swap) in IHProvable.
    rewrite !gmultiset_map_compose, !subst_form_compose in IHProvable.

    rewrite gmultiset_map_compose, subst_form_compose.
    rewrite swap_up_succ at 2.
    change (S' ☉ S') with ((swap ☉ S') ☉ S').
    change (up S') with (swap ☉ S') at 1.
    rewrite <- subst_form_compose, <- gmultiset_map_compose at 1.
    backward_map.
    rewrite <- !subst_form_compose_pt.
    apply IHProvable.
    easy.
  - apply ImpLForAll.
    change  ((ForAll φ1 〔 ⇑ S' 〕) → φ2 〔 S' 〕) with
       (subst_form S' ((ForAll φ1) → φ2)).
    backward_map.
    change (ForAll (subst_form (up S') φ1)) with (subst_form S' (ForAll φ1)).
    apply relabelling_lemma.
    easy.
    backward_map.
    auto with proof.
  - apply ImpLExists.
    specialize (IHProvable φ Heqφ').
    rewrite subst_form_compose_pt.
    change (S' ☉ S') with (up S' ☉  S').
    rewrite <- subst_form_compose_pt.
    change  (ForAll (φ1 〔 ⇑ S' 〕 → φ2 〔 S' 〕 〔 ⇑ S' 〕)) with
      
      (subst_form S' (ForAll (φ1 → (subst_form S' φ2)))).
    backward_map.
    easy.
Qed.
  
(* Partial inverse of ImpLForAll *)
Lemma ImpLForAll_prev Γ φ1 φ2 ψ:
    Γ • (ForAll (φ1) → φ2) ⊢ ψ → (Γ • φ2) ⊢ ψ.
Proof.
  intros Hp.
  remember (Γ • ((ForAll φ1) → φ2)) as Γ'.
  assert (Γ = Γ' ∖ {[ ((ForAll φ1) → φ2) ]}) as HeqΓ by ms.
  rewrite HeqΓ.
  assert (((ForAll φ1) → φ2) ∈ Γ') as Hin by multiset_solver.
  clear HeqΓ HeqΓ' Γ.
  revert φ1 φ2 Hin.
  induction Hp; intros; 
  apply (gmultiset_map_elem_of (subst_form S')) in Hin as Hin'.
  - forward. apply Init.
  - forward. apply ExFalso.
  - apply AndR. apply IHHp1. ms. apply IHHp2. ms.
  - forward. apply AndL. exch 0. do 2 backward. apply IHHp. ms.
  - apply OrR1. apply IHHp. ms.
  - apply OrR2. apply IHHp. ms.
  - forward. apply OrL. backward. apply IHHp1. ms. backward. apply IHHp2. ms.
  - apply ImpR. backward. apply IHHp. ms.
  - do 2 forward. exch 0. apply ImpL0. exch 0. do 2 backward. apply IHHp. ms.
  - forward. apply ImpLAnd. backward. apply IHHp. ms.
  - forward. apply ImpLOr. exch 0. do 2 backward. apply IHHp. ms.
  - forward. apply ImpLImp. exch 0. do 2 backward. apply IHHp1. ms. backward. apply IHHp2. ms.
  - apply ForAllR. forward_map. unmap_diff_singleton. simpl. apply IHHp. ms.
  - forward. apply ForAllL with (t := t). exch 0. do 2 backward. apply IHHp. ms.
  - apply ExistsR with (t := t). apply IHHp. ms.
  - forward. apply ExistsL. forward_map. unmap_diff_singleton. backward. apply IHHp. ms.
  - case (decide (((ForAll φ1) → φ2) = ((ForAll φ0) → φ3))); intros Heq.
    + inversion Heq. subst. rewrite env_add_remove. easy.
    + forward. apply ImpLForAll. backward. apply IHHp1. ms. backward. apply IHHp2. ms.
  - forward. apply ImpLExists. backward. apply IHHp. ms.
Qed.
    
Lemma ImpLExists_rev Γ φ1 φ2 ψ:
  Γ • (Exists (φ1) → φ2) ⊢ ψ →
   Γ • ForAll (φ1 → (subst_form S' φ2)) ⊢ ψ.
Proof.
  intros Hp.
  remember (Γ • ((Exists φ1) → φ2)) as Γ'.
  assert (Γ = Γ' ∖ {[ ((Exists φ1) → φ2) ]}) as HeqΓ by ms.
  rewrite HeqΓ.
  assert (((Exists φ1) → φ2) ∈ Γ') as Hin by multiset_solver.
  clear HeqΓ HeqΓ' Γ.
  revert φ1 φ2 Hin.
  induction Hp; intros; 
  apply (gmultiset_map_elem_of (subst_form S')) in Hin as Hin'.
  - forward. apply Init.
  - forward. apply ExFalso.
  - apply AndR. apply IHHp1. ms. apply IHHp2. ms.
  - forward. apply AndL. exch 0. do 2 backward. apply IHHp. ms.
  - apply OrR1. apply IHHp. ms.
  - apply OrR2. apply IHHp. ms.
  - forward. apply OrL. backward. apply IHHp1. ms. backward. apply IHHp2. ms.
  - apply ImpR. backward. apply IHHp. ms.
  - do 2 forward. exch 0. apply ImpL0. exch 0. do 2 backward. apply IHHp. ms.
  - forward. apply ImpLAnd. backward. apply IHHp. ms.
  - forward. apply ImpLOr. exch 0. do 2 backward. apply IHHp. ms.
  - forward. apply ImpLImp. exch 0. do 2 backward. apply IHHp1. ms. backward. apply IHHp2. ms.
  - apply ForAllR. forward_map. unmap_diff_singleton. simpl.
    rewrite subst_form_compose_pt. change (up S' ☉ S') with (S' ☉ S').
    rewrite <- subst_form_compose_pt. apply IHHp. ms.
  - forward. apply ForAllL with (t := t). exch 0. do 2 backward. apply IHHp. ms.
  - apply ExistsR with (t := t). apply IHHp. ms.
  - forward. apply ExistsL. forward_map. unmap_diff_singleton. backward. simpl.
    rewrite subst_form_compose_pt. change (up S' ☉ S') with (S' ☉ S').
    rewrite <- subst_form_compose_pt.
    apply IHHp. ms.
  - forward. apply ImpLForAll. backward. apply IHHp1. ms. backward. apply IHHp2. ms.
  - case (decide (((Exists φ1) → φ2) = ((Exists φ0) → φ3))); intros Heq.
    + inversion Heq. subst. rewrite env_add_remove. easy.
    + forward. apply ImpLExists. backward. apply IHHp. ms.
Qed.

(** We prove Lemma 4.1 of (Dyckhoff & Negri 2000). This lemma shows that a
    weaker version of the ImpL rule of Gentzen's original calculus LJ is still
    admissible in G4ip. The proof is simple, but requires the inversion lemmas
    proved above.
  *)

Lemma weak_ImpL Γ φ ψ θ :Γ ⊢ φ -> Γ•ψ ⊢ θ -> Γ•(φ → ψ) ⊢ θ.
Proof with (auto with proof).
  intro Hp. revert ψ θ. induction Hp; intros ψ0 θ0 Hp'.
- apply ImpL0, Hp'.
- auto with proof.
- auto with proof.
- exch 0; constructor 4; exch 1; exch 0...
- auto with proof.
- apply ImpLOr. exch 0...
- exch 0; constructor 7; exch 0.
  + apply IHHp1. exch 0. eapply fst, OrL_rev. exch 0. exact Hp'.
  + apply IHHp2. exch 0. eapply snd, OrL_rev. exch 0. exact Hp'.
- auto with proof.
- exch 0; exch 1. constructor 9. exch 1; exch 0...
- exch 0. apply ImpLAnd. exch 0...
- exch 0. apply ImpLOr. exch 1; exch 0...
- exch 0. apply ImpLImp. exch 1; auto with proof. exch 0. apply IHHp2. exch 0.
  eapply ImpLImp_prev. exch 0. eassumption.
- auto with proof.
- exch 0. apply ForAllL with (t := t). exch 1. exch 0. apply IHHp. exch 0...
- apply ImpLExists. apply ForAllL with (t := t). exch 0. apply weakening. simpl.
  rewrite subst_form_compose_pt. simpl. rewrite subst_form_ident_pt. apply IHHp. exact Hp'.
- exch 0. apply ExistsL. forward_map. exch 0. simpl. apply IHHp. exch 0. backward_map.
  apply ExistsL_rev. exch 0. easy.
- exch 0. apply ImpLForAll. exch 0. apply weakening. exact Hp1. exch 0. apply IHHp2. exch 0. apply ImpLForAll_prev with (φ1 := φ1). exch 0. exact Hp'.
- exch 0. apply ImpLExists. exch 0. apply IHHp. exch 0. apply ImpLExists_rev. exch 0. exact Hp'.
Qed.

Global Hint Resolve weak_ImpL : proof.

(** ** Contraction

 The aim of this section is to prove that the contraction rule is admissible in
 G4ip. *)

    
(** Lemma 4.2 in (Dyckhoff & Negri 2000), showing that a "duplication" in the context of the implication-case of the implication-left rule is admissible. *)

Lemma ImpLImp_dup Γ φ1 φ2 φ3 θ:
  Γ•((φ1 → φ2) → φ3) ⊢ θ ->
    Γ•φ1 •(φ2 → φ3) •(φ2 → φ3) ⊢ θ.
Proof.
intro Hp.
remember (Γ•((φ1 → φ2) → φ3)) as Γ0 eqn:Heq0.
assert(HeqΓ : Γ ≡ Γ0 ∖ {[((φ1 → φ2) → φ3)]}) by ms.
rw HeqΓ 3.
assert(Hin : ((φ1 → φ2) → φ3) ∈ Γ0) by (subst Γ0; ms).
clear Γ HeqΓ Heq0.
(* by induction on the height of the derivation *)
remember (height Hp) as h.
assert(Hleh : height Hp ≤ h) by lia. clear Heqh.
revert φ1 φ2 φ3 Γ0 θ Hp Hleh Hin. induction h as [|h]; intros φ1 φ2 φ3 Γ θ Hp Hleh Hin;
  apply (gmultiset_map_elem_of (subst_form S')) in Hin as Hin';
[pose (height_0 Hp); lia|].
destruct Hp; simpl in Hleh.
- forward. auto with proof.
- forward. auto with proof.
- apply AndR.
  + apply IHh with Hp1. lia. ms.
  + apply IHh with Hp2. lia. ms.
- forward. apply AndL. exch 0. do 2 backward. apply IHh with Hp. lia. ms.
- apply OrR1. apply IHh with Hp. lia. ms.
- apply OrR2. apply IHh with Hp. lia. ms.
- forward. apply OrL; backward.
  + apply IHh with Hp1. lia. ms.
  + apply IHh with Hp2. lia. ms.
- apply ImpR. backward. apply IHh with Hp. lia. ms.
- do 2 forward. exch 0. apply ImpL0. exch 0. do 2 backward.
  apply IHh with Hp. lia. ms.
- forward. apply ImpLAnd. backward. apply IHh with Hp. lia. ms.
- forward. apply ImpLOr. exch 0. do 2 backward. apply IHh with Hp. lia. ms.
- case (decide (((φ0 → φ4) → φ5) = ((φ1 → φ2) → φ3))); intro Heq.
  + dependent destruction Heq; subst.
    apply weak_ImpL.
    * exch 0. peapply Hp1.
    * do 2 (exch 0; apply weakening). peapply Hp2.
  + forward. apply ImpLImp; backward.
    * forward. exch 0. backward. backward. apply IHh with Hp1. lia. ms.
    * apply IHh with Hp2. lia. ms.
- apply ForAllR. repeat forward_map.  unmap_diff_singleton. simpl.
  apply IHh with Hp. lia. ms.
- forward. apply ForAllL with (t := t). exch 0. do 2 backward.
  apply IHh with Hp. lia. ms.
- apply ExistsR with (t := t). apply IHh with Hp. lia. ms.
- forward. apply ExistsL. repeat forward_map. unmap_diff_singleton. backward.
  apply IHh with Hp. lia. ms.
- forward. apply ImpLForAll. backward.
  apply IHh with Hp1. lia. ms. backward.
  apply IHh with Hp2. lia. ms.
- forward. apply ImpLExists. backward. apply IHh with Hp. lia. ms.
Qed.

(* technical lemma for contraction *)
Local Lemma p_contr Γ φ θ:
  (Γ•φ•φ) ∖ {[φ]} ⊢ θ ->
  ((Γ•φ) ⊢ θ).
Proof. intros * Hd; peapply Hd. Qed.

(** Admissibility of contraction in G4ip. *)
Lemma contraction Γ ψ θ : Γ • ψ • ψ ⊢ θ -> Γ • ψ ⊢ θ.
Proof.
remember (Γ•ψ•ψ) as Γ0 eqn:Heq0.
assert(HeqΓ : (Γ•ψ) ≡ Γ0 ∖ {[ψ]}) by ms.
intro Hp. rw HeqΓ 0.
assert(Hin : ψ ∈ Γ0) by (subst Γ0; ms).
assert(Hin' : ψ ∈ Γ0 ∖ {[ψ]}) by(rewrite <- HeqΓ; ms).
clear Γ HeqΓ Heq0. revert Hp.
(* by induction on the weight of ψ *)
remember (weight ψ) as w.
assert(Hle : weight ψ ≤ w) by lia.
clear Heqw. revert Γ0 ψ θ Hle Hin Hin'.
induction w; intros Γ ψ θ Hle Hin Hin' Hp; [destruct ψ; simpl in Hle; lia|].
(* by induction on the height of the premise *)
remember (height Hp) as h.
assert(Hleh : height Hp ≤ h) by lia. clear Heqh.
revert Γ θ Hp Hleh Hin Hin'. revert ψ Hle; induction h as [|h]; intros ψ Hle Γ θ Hp Hleh Hin Hin';
[pose (height_0 Hp); lia|].
destruct Hp; simpl in Hleh, Hle.
- case(decide (ψ = Atom i xs)).
  + intro; subst. exhibit Hin' 0. apply Init.
  + intro Hneq. forward. apply Init.
- case(decide (ψ = ⊥)).
  + intro; subst. exhibit Hin' 0. apply ExFalso.
  + intro. forward. apply ExFalso.
- apply AndR.
  + apply (IHh ψ Hle) with Hp1. lia. ms. ms.
  + apply (IHh ψ Hle) with Hp2. lia. ms. ms.
- case (decide (ψ = (φ ∧ ψ0))); intro Heq.
  + subst. exhibit Hin' 0. apply AndL.
    apply p_contr. simpl in Hle. apply IHw. lia. ms. rewrite union_difference_R; ms.
    exch 1. exch 0. apply p_contr. apply IHw. lia. ms. rewrite union_difference_R; ms.
    exch 1. exch 0. apply AndL_rev. exch 0. exch 1. lazy_apply Hp.
    rewrite <- (difference_singleton _ _ Hin'). ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply AndL. exch 0. do 2 backward. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- apply OrR1. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- apply OrR2. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = (φ ∨ ψ0))); intro Heq.
  + subst. exhibit Hin' 0.
    apply OrL.
    * apply p_contr. simpl in Hle. apply IHw. lia. ms. rewrite union_difference_R; ms.
      refine (fst (OrL_rev _ φ ψ0 _ _)). exch 0. lazy_apply Hp1.
      rewrite <- env_replace; ms.
    * apply p_contr. simpl in Hle. apply IHw. lia. ms. rewrite union_difference_R; ms.
      refine (snd (OrL_rev _ φ ψ0 _ _)). exch 0. lazy_apply Hp2.
      rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply OrL; backward.
    * apply (IHh ψ Hle) with Hp1. lia. ms. ms.
    * apply (IHh ψ Hle) with Hp2. lia. ms. ms.
- apply ImpR. backward. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = (Atom i xs → φ))); intro Heq.
  + subst. exhibit Hin' 0. rewrite union_difference_R in Hin' by ms.
    assert(Hcut : (((Γ•Atom i xs) ∖ {[Atom i xs → φ]}•(Atom i xs → φ)) ⊢ ψ0)); [|peapply Hcut].
    forward. exch 0. apply ImpL0, p_contr.
    apply IHw. simpl in Hle; lia. ms.  rewrite union_difference_L; ms.
    exch 1. apply ImpL0_rev. exch 0; exch 1. lazy_apply Hp.
    rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
      forward. case (decide (ψ = Atom i xs)).
      * intro; subst. forward. exch 0. apply ImpL0. exch 0.
         do 2 backward. apply (IHh (Atom i xs) Hle) with Hp. lia. ms. ms.
      * intro. forward. exch 0. apply ImpL0; exch 0; do 2 backward.
         apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = (φ1 ∧ φ2 → φ3))); intro Heq.
  + subst. exhibit Hin' 0. rewrite union_difference_R in Hin' by ms.
    apply ImpLAnd. apply p_contr.
    apply IHw. simpl in *; lia. ms.  rewrite union_difference_L; ms.
    apply ImpLAnd_rev. exch 0. lazy_apply Hp.
    rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply ImpLAnd. backward. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = (φ1 ∨ φ2 → φ3))); intro Heq.
  + subst. exhibit Hin' 0. rewrite union_difference_R in Hin' by ms.
    apply ImpLOr. apply p_contr.
    apply IHw. simpl in *; lia. ms. rewrite union_difference_L; ms.
    exch 1; exch 0. apply p_contr.
    apply IHw. simpl in *. lia. ms. rewrite union_difference_L; ms.
    exch 1; exch 0. apply ImpLOr_rev. exch 0. exch 1. lazy_apply Hp.
    rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply ImpLOr. exch 0. do 2 backward. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = ((φ1 → φ2) → φ3))); intro Heq.
  + subst. exhibit Hin' 0. rewrite union_difference_R in Hin' by ms.
    apply ImpLImp.
    * do 2 (exch 0; apply p_contr; apply IHw; [simpl in *; lia|ms|rewrite union_difference_L; ms|exch 1]).
      apply p_contr; apply IHw; [simpl in *; lia|ms|rewrite union_difference_L; ms|exch 1].
      exch 1. apply ImpLImp_dup. exch 0. exch 1.                            
      lazy_apply Hp1. rewrite <- env_replace; ms.
    * apply p_contr; apply IHw; [simpl in *; lia|ms|rewrite union_difference_L; ms|].
      apply (ImpLImp_prev _ φ1 φ2 φ3). exch 0.
      peapply Hp2. rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply ImpLImp. exch 0.  backward.
    * backward. apply (IHh ψ Hle) with Hp1. lia. ms. ms.
    * backward. apply (IHh ψ Hle) with Hp2. lia. ms. ms.
- apply ForAllR. unmap_diff_singleton.
  rewrite <- (weight_subst_S ψ) in Hle.
  apply (gmultiset_map_elem_of (subst_form S')) in Hin'.
  rewrite (gmultiset_map_distr_singleton_diff
             (subst_form S') Γ ψ (inj_subst_form_S)) in Hin'.
  apply (IHh (subst_form S' ψ) Hle) with Hp. lia. ms. ms. 
- case (decide (ψ = (ForAll φ))); intros Heq.
  + subst. exhibit Hin' 0.
    apply ForAllL with (t := t). rewrite env_add_remove.
    exch 0; do 2 backward. apply (IHh (ForAll φ) Hle) with Hp. lia. ms. ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply ForAllL with (t := t). exch 0. do 2 backward. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- apply ExistsR with (t := t); apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = (Exists φ))); intros Heq.
  + subst. exhibit Hin' 0.
    apply ExistsL.
    rewrite env_add_remove in *.
    apply p_contr.
    apply IHw; try ms.
    
    assert ((subst_form (bind_var (var 0)) (subst_form (up S') φ)) = φ) as Hφ by (
    rewrite subst_form_compose_pt, bind_var_0_upS_ident, subst_form_ident; easy).
    rewrite <- Hφ at 3.
    apply ExistsL_rev_specialised with (t := var 0).
    change (Exists (subst_form (up S') φ)) with (subst_form S' (Exists φ)).
    unmap_diff_singleton.
    apply (gmultiset_map_elem_of (subst_form S')) in Hin'.
    backward.
    rewrite env_add_remove.
    easy.
  + forward.
    apply ExistsL.
    unmap_diff_singleton.
    backward.
    pose (weight_subst_S ψ) as Hw1.
    simpl in Hw1.
    rewrite <- Hw1 in Hle.
    apply (IHh (subst_form S' ψ) Hle) with Hp; [ lia | ms | ].
    assert ( ψ ∈ (Γ ) ∖ {[ψ]}) as Hin'1 by multiset_solver.
    apply (gmultiset_map_elem_of (subst_form S')) in Hin'1.
    pose (gmultiset_map_distr_singleton_diff (subst_form S') Γ ψ inj_subst_form_S).
    replace (gmultiset_map (subst_form S') (Γ ∖ {[ ψ ]})) with
      (gmultiset_map (subst_form S') Γ ∖ {[ (subst_form S' ψ) ]}) in Hin'1 by ms.
    ms.
- case (decide (ψ = (ForAll φ1 → φ2))); intros.
  + subst.
    exhibit Hin' 0.
    apply ImpLForAll; rewrite !env_add_remove in *.
    * apply p_contr.
      replace ((Γ ∖ {[(ForAll φ1) → φ2]} • ((ForAll φ1) → φ2))) with Γ by multiset_solver.
      apply IHh with (Hp := Hp1); try lia; try ms.
    * apply p_contr.
      apply IHw; [ simpl in *; lia | ms | ms | ].
      apply ImpLForAll_prev with (φ1 := φ1).
      exch 0.
      replace ((Γ ∖ {[(ForAll φ1) → φ2]} • ((ForAll φ1) → φ2))) with Γ by multiset_solver.
      easy.
  + forward.
    apply ImpLForAll.
    * backward.
      apply IHh with (Hp := Hp1); [ lia | lia | ms | ms ].
    * backward.
      apply IHh with (Hp := Hp2); [ lia | lia | ms | multiset_solver ].
- case (decide (ψ = (Exists φ1 → φ2))); intros.
  + subst.
    exhibit Hin' 0.
    apply ImpLExists.
    rewrite !env_add_remove in *.
    apply p_contr.
    apply IHw; [ simpl in *; rewrite weight_subst_f; lia|ms|ms|].
    apply ImpLExists_rev.
    backward.
    rewrite env_add_remove.
    easy.
  + forward.
    apply ImpLExists.
    backward.
    apply IHh with (Hp := Hp); [ lia | lia | ms | multiset_solver ].
Qed.

Global Hint Resolve contraction : proof.

Theorem generalised_contraction (Γ Γ' : env) φ:
  Γ' ⊎ Γ' ⊎ Γ ⊢ φ -> Γ' ⊎ Γ ⊢ φ.
Proof.
revert Γ.
induction Γ' as [| x Γ' IHΓ'] using gmultiset_rec; intros Γ Hp.
- peapply Hp.
- peapply (contraction (Γ' ⊎ Γ) x). peapply (IHΓ' (Γ•x•x)). peapply Hp.
Qed.

(** ** Admissibility of LJ's implication left rule *)

(** We show that the general implication left rule of LJ is admissible in G4ip.
  This is Proposition 5.2 in (Dyckhoff Negri 2000). *)

Lemma ImpL Γ φ ψ θ: Γ•(φ → ψ) ⊢ φ -> Γ•ψ  ⊢ θ -> Γ•(φ → ψ) ⊢ θ.
Proof. intros H1 H2. apply contraction, weak_ImpL; auto with proof. Qed.


(* Lemma 5.3 (Dyckhoff Negri 2000) shows that an implication on the left may be
   weakened. *)

Lemma ForAllL_rev Γ φ ψ t :
  Γ • (ForAll φ) ⊢ ψ -> Γ • (ForAll φ) • (subst_form (bind_var t) φ) ⊢ ψ.
Proof.
  intros Hp.
  remember (Γ • (ForAll φ)) as Γ'.
  replace Γ with (Γ' ∖ {[ ForAll φ ]}) by ms.
  assert (ForAll φ ∈ Γ') as Hin by ms.
  clear Γ HeqΓ'.
  revert φ Hin t.
  dependent induction Hp; intros; apply (gmultiset_map_elem_of (subst_form S')) in Hin as Hin'.
  - exch 0. auto with proof.
  - exch 0. auto with proof.
  - apply AndR. apply IHHp1; ms. apply IHHp2; ms.
  - exch 0. apply AndL. exch 1. exch 0. apply IHHp. ms.
  - apply OrR1. apply IHHp. ms.
  - apply OrR2. apply IHHp. ms.
  - exch 0. apply OrL. exch 0. apply IHHp1. ms. exch 0. apply IHHp2. ms.
  - apply ImpR. exch 0. apply IHHp. ms.
  - exch 0. exch 1. apply ImpL0. exch 1. exch 0. apply IHHp. ms.
  - exch 0. apply ImpLAnd. exch 0. apply IHHp. ms.
  - exch 0. apply ImpLOr. exch 1. exch 0. apply IHHp. ms.
  - exch 0. apply ImpLImp. exch 1. exch 0. apply IHHp1. ms. exch 0. apply IHHp2. ms.
  - apply ForAllR. forward_map.
    rewrite subst_form_compose_pt, f_bind_var_t_commute, <- subst_form_compose_pt.
    apply IHHp.
    ms.
  - exch 0. apply ForAllL with (t := t).
    exch 1.
    exch 0.
    apply IHHp.
    ms.
  - apply ExistsR with (t := t). apply IHHp. ms.
  - exch 0. apply ExistsL. repeat forward_map. exch 0.
    rewrite subst_form_compose_pt.
    rewrite f_bind_var_t_commute.
    rewrite <- subst_form_compose_pt.
    apply IHHp.
    ms.
  - exch 0. apply ImpLForAll. exch 0. apply IHHp1. ms. exch 0. apply IHHp2. ms.
  - exch 0. apply ImpLExists. exch 0. apply IHHp. ms.
Qed.

Lemma OrR_idemp Γ ψ : Γ ⊢ ψ ∨ ψ -> Γ ⊢ ψ.
Proof. intro Hp. dependent induction Hp; auto with proof.
       apply ForAllL with (t := t). apply IHHp. reflexivity.
Qed.

(**
  - [var_not_tautology]: A variable cannot be a tautology.
  - [bot_not_tautology]: ⊥ is not a tautology.
  - [box_var_not_tautology]: A boxed variable cannot be a tautology.
  - [box_bot_not_tautology]: A boxed ⊥ cannot be a tautology.
*)

Lemma bot_not_tautology : (∅ ⊢ ⊥) -> False.
Proof.
intro Hf. dependent destruction Hf; simpl in *;
match goal with x : _ ⊎ {[+?φ+]} = _ |- _ =>
exfalso; eapply (gmultiset_elem_of_empty φ); setoid_rewrite <- x; ms end.
Qed.

Lemma var_not_tautology i xs: (∅ ⊢ Atom i xs) -> False.
Proof.
intro Hp.
remember ∅ as Γ.
dependent induction Hp;
match goal with | Heq : (_ • ?f%stdpp) = _ |- _ => symmetry in Heq;
  pose(Heq' := env_equiv_eq _ _ Heq);
  apply (gmultiset_not_elem_of_empty f); rewrite Heq'; ms
  end.
Qed.

(* A tautology is either equal to ⊤ or has a weight of at least 2. *)
Lemma weight_tautology φ: (∅ ⊢ φ) -> {φ = ⊤} + {2 ≤ weight φ}.
Proof.
intro Hp.
destruct φ.
- contradict Hp. apply  var_not_tautology.
- contradict Hp. apply bot_not_tautology.
- right. simpl. pose(weight_pos φ1). pose(weight_pos φ2). lia.
- right. simpl. pose(weight_pos φ1). pose(weight_pos φ2). lia.
- right. simpl. pose(weight_pos φ1). pose(weight_pos φ2). lia.
- right. simpl. pose(weight_pos φ). lia.
- right. simpl. pose(weight_pos φ). lia.
Qed.
