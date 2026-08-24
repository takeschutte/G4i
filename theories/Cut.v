(** * Cut Admissibility *)
Require Import G4i.Formulas G4i.Sequents G4i.Order.
Require Import G4i.SequentProps.
Require Import Stdlib.Program.Equality.

Local Hint Rewrite @elements_env_add : order.

Definition CutHyp (w : nat) :=
  forall (φ : form), weight φ <= w -> 
  forall (ψ : form) (Γ : env), Γ ⊢ φ -> (Γ • φ) ⊢ ψ -> Γ ⊢ ψ.

Definition ImpOrForAll (φ : form) := 
  (exists A B, φ = (Implies A B)) \/ (exists A, φ = (ForAll A)).

Lemma cutM {w : nat} (IHw : CutHyp w) (θ : form) (hθ : weight θ <= w) 
  (Γ1 Γ2 : env) (ψ : form) (d1 : Γ1 ⊢ θ) (d2 : (Γ2 • θ) ⊢ ψ) : (Γ1 ⊎ Γ2) ⊢ ψ.
Proof.
  intros.
  apply (IHw θ).
  - lia.
  - now apply generalised_weakeningR.
  - peapply (generalised_weakeningL _ Γ1 _ d2).
Qed.
        
Lemma hshape (σ : nat -> term) (θ : form) (hθ : ImpOrForAll θ) :
  ImpOrForAll (subst_form σ θ).
Proof.
  destruct hθ.
  - destruct H as [A H]; destruct H as [B Heq]; subst; simpl; left.
    exists (subst_form σ A); exists (subst_form σ B); easy.
  - destruct H as [A Heq]; subst; right.
    exists (subst_form (up σ) A); easy.
Qed.

Lemma cut_principal (w : nat) (IHw : CutHyp w) 
  (Δ : env) (θ : form) (h : Δ ⊢ θ) :
  forall (φ : form) (Γ Γ' : env), 
    Δ = (Γ' • φ) -> 
    weight φ <= w + 1 -> 
    ImpOrForAll φ -> 
    Γ ⊢ φ -> 
    (Γ ⊎ Γ') ⊢ θ.
Proof.
  induction h; intros φ0 Γ0 Γ' HeqΓ Hw HImp Hp.
  - destruct (decide (φ0 = (Atom i xs))) as [Heq | Hneq]. 
    + subst; exfalso; destruct HImp as [[A [B Heq]] | [A Heq']]; discriminate.
    + assert (Hin : Atom i xs ∈ Γ') by multiset_solver.
      apply generalised_weakeningL; exhibit Hin 0; auto with proof.
  - case (decide (Bot = φ0)) as [Heq | Hneq].
    + subst; exfalso; destruct HImp as [[A [B Heq]] | [A Heq']]; discriminate.
    + assert (Hin : ⊥ ∈ Γ') by multiset_solver.
      apply generalised_weakeningL; exhibit Hin 0; auto with proof.
  - apply AndR; [apply IHh1 with (φ := φ0); auto |
                  apply IHh2 with (φ := φ0); auto ].
  - case (decide ((And φ ψ) = φ0)) as [Heq | Hneq].
    + subst; exfalso; destruct HImp as [[A [B Heq]] | [A Heq']]; discriminate.
    + assert (Hin : (And φ ψ) ∈ Γ') by multiset_solver.
      replace (Γ0 ⊎ Γ') with (Γ0 ⊎ (Γ ∖ {[φ0]}) • (φ ∧ ψ)) by multiset_solver.
      apply AndL.
      replace (Γ0 ⊎  (Γ) ∖ {[φ0]} • φ • ψ) with
                                                                                (Γ0 ⊎ (Γ ∖ {[φ0]} • φ • ψ)) by ms.
      apply (IHh φ0 Γ0); multiset_solver; auto.
  - apply OrR1. apply IHh with (φ := φ0); auto.
  - apply OrR2. apply IHh with (φ := φ0); auto.
  - case (decide ((Or φ ψ) = φ0)) as [Heq | Hneq].
    + subst; exfalso; destruct HImp as [[A [B Heq]] | [A Heq']]; discriminate.
    + assert (Hin : (Or φ ψ) ∈ Γ') by multiset_solver.
      replace (Γ0 ⊎ Γ') with (Γ0 ⊎ (Γ ∖ {[φ0]}) • (φ ∨  ψ)) by multiset_solver.
      peapply OrL.
      replace (Γ0 ⊎  (Γ) ∖ {[φ0]} • φ) with                                           (Γ0 ⊎ (Γ ∖ {[φ0]} • φ)) by ms.
      apply IHh1 with (φ := φ0); multiset_solver; auto.
      replace (Γ0 ⊎  (Γ) ∖ {[φ0]} • ψ) with                                           (Γ0 ⊎ (Γ ∖ {[φ0]} • ψ)) by ms.
      apply IHh2 with (φ := φ0); multiset_solver; auto.
  - apply ImpR.
    replace  (Γ0 ⊎ Γ' • φ) with  (Γ0 ⊎ (Γ' • φ)) by ms.
    apply IHh with (φ := φ0); ms.
  - destruct (decide ((Implies (Atom i xs) φ) = φ0)).
    + assert (HeqΓ' : (Γ • (Atom i xs)) = Γ') by ms.
      assert (Hin: (Atom i xs) ∈ (Γ0 ⊎ Γ')) by ms.
      exhibit Hin 0.
      apply contraction.
      backward.
      rewrite env_add_remove.
      replace  (Γ0 ⊎ Γ' • Atom i xs) with ( (Γ0 • Atom i xs) ⊎ Γ').
      subst.
      apply (cutM IHw φ).
      simpl in Hw. lia.
      apply ImpR_rev; easy.
      easy.
      ms.
    + case (decide ((Atom i xs) = φ0)) as [Heq | Hneq].
      * subst; exfalso; destruct HImp as [[A [B Heq]] | [A Heq']]; discriminate.
      * assert (Hin'' : (Implies (Atom i xs) φ) ∈ Γ') by multiset_solver.
        assert (Hin' : (Implies (Atom i xs) φ) ∈ (Γ0 ⊎ Γ')) by multiset_solver.
        exhibit Hin' 0.
        assert (Hin : (Atom i xs) ∈ (Γ0 ⊎ Γ') ∖ {[+ (Implies (Atom i xs) φ) +]}) by multiset_solver.
        
        exhibit Hin 1.
        apply ImpL0.
        exch 0.
        backward.
        rewrite env_add_remove.
        replace ((Γ0 ⊎ Γ') ∖ {[+ Atom i xs → φ +]} • φ) with  (Γ0 ⊎  (Γ' ∖ {[+ Atom i xs → φ +]} • φ)) by multiset_solver.
        
        apply (IHh φ0).
        multiset_solver.
        lia.
        easy.
        easy.
  - case (decide ((Implies (φ1 ∧ φ2) φ3) = φ0)) as [Heq | Hneq].
    + assert (Γ = Γ') by ms.
      subst.
      apply (IHw (φ1 → φ2 → φ3)). simpl in *; lia.
      apply ImpR, ImpR, AndL_rev.
      peapply ImpR_rev.
      apply generalised_weakeningR.
      easy.
      replace ( (Γ0 ⊎ Γ' • (φ1 → φ2 → φ3)) ) with (Γ0 ⊎ (Γ' • (φ1 → φ2 → φ3))) by ms.
      apply generalised_weakeningL.
      easy.
    + assert (Hin: (Implies (φ1 ∧ φ2) φ3) ∈ Γ') by multiset_solver.
      replace (Γ0 ⊎ Γ') with
        ((Γ0 ⊎ (Γ' ∖ {[φ1 ∧ φ2 → φ3]})) • (φ1 ∧ φ2 → φ3)) by multiset_solver.
      apply ImpLAnd.
      peapply (IHh φ0 Γ0 ((Γ'∖ {[φ1 ∧ φ2 → φ3]}) • (φ1 → φ2 → φ3))).
      multiset_solver.
      lia.
      easy.
      easy.      
  - destruct (decide ((φ1 ∨ φ2 → φ3) = φ0)) as [Heq | Hneq].
    + assert (Γ = Γ') by ms. subst.
      clear HeqΓ.
      apply ImpR_rev in Hp.
      apply OrL_rev in Hp.
      destruct Hp.
      apply (IHw (φ1 → φ3)).      
      simpl in *; lia.
      apply generalised_weakeningR.
      apply ImpR; easy.
      apply (IHw (φ2 → φ3)).
      simpl in *; lia.
      replace ( (Γ0 ⊎ Γ') • (φ1 → φ3) ) with (Γ' ⊎ (Γ0 • (φ1 → φ3))) by ms.
      apply generalised_weakeningL.
      apply ImpR. exch 0.
      auto with proof.
      
      replace ( (Γ0 ⊎ Γ') • (φ1 → φ3) • (φ2 → φ3) )
        with (Γ0 ⊎ (Γ' • (φ1 → φ3) • (φ2 → φ3) )) by ms.
      apply generalised_weakeningL.
      easy.
    + assert (Hin : (φ1 ∨ φ2 → φ3) ∈ Γ') by multiset_solver.      
      peapply (ImpLOr (Γ0 ⊎ (Γ' ∖ {[φ1 ∨ φ2 → φ3]})) φ1 φ2 φ3).      
      peapply (IHh φ0 Γ0 (Γ' ∖ {[φ1 ∨ φ2 → φ3]} • (φ1 → φ3) • (φ2 → φ3))).
      multiset_solver.
      lia.
      easy.
      easy.
      multiset_solver.
  - destruct (decide ((Implies (Implies φ1 φ2) φ3) = φ0)) as [Heq | Hneq].
    + assert (Γ = Γ') by ms.
      subst.
      clear HeqΓ.
      apply ImpR_rev in Hp.
      apply (cutM IHw φ3) with (Γ2 := Γ') (ψ := ψ) in Hp as Hp2; [ | simpl in *; lia | easy].
      replace ((Γ0 • (φ1 → φ2)) ⊎ Γ') with ((Γ0 ⊎ Γ')• (φ1 → φ2)) in Hp2 by ms.
      apply (IHw (φ1 → φ2)); [ simpl in *; lia | | easy ].
      apply ImpR.
      apply (IHw (φ2 → φ3)); [ simpl in *; lia | | 
      replace  (Γ0 ⊎ Γ' • φ1 • (φ2 → φ3)) with  (Γ0 ⊎ (Γ' • φ1 • (φ2 → φ3))) by ms; apply generalised_weakeningL; easy].
      apply ImpR.
      apply (IHw (φ1 → φ2)); [ simpl in *; lia | apply ImpR; exch 0; apply generalised_axiom |].
      replace (Γ0 ⊎ Γ' • φ1 • φ2 • (φ1 → φ2))
           with ((Γ0 • (φ1 → φ2)) ⊎ (Γ' • φ1 • φ2)) by ms.
      apply generalised_weakeningR; easy.
    + assert (Hin : ((φ1 → φ2) → φ3) ∈ Γ') by multiset_solver.      
      peapply (ImpLImp (Γ0 ⊎ (Γ' ∖ {[(φ1 → φ2) → φ3]})) φ1 φ2 φ3).
      peapply (IHh1 φ0 Γ0 (Γ' ∖ {[(φ1 → φ2) → φ3]}  • φ1 • (φ2 → φ3) )).
      multiset_solver.
      lia.
      easy.
      easy.
      peapply (IHh2 φ0 Γ0 (Γ' ∖ {[(φ1 → φ2) → φ3]}  • φ3  )).
      multiset_solver.
      lia.
      easy.
      easy.
      multiset_solver.
  - apply ForAllR.
    replace ( gmultiset_map (subst_form S') (Γ0 ⊎ Γ')) with
      ((gmultiset_map (subst_form S') Γ0) ⊎ (gmultiset_map (subst_form S') Γ'))by (symmetry; apply gmultiset_map_disj_union).
    apply IHh with (φ := (subst_form S' φ0)).
    subst.
    apply  gmultiset_map_distr_disj_union_singleton.
    rewrite weight_subst_f.
    lia.
    apply hshape. easy.
    apply relabelling_lemma.
    easy.
  - destruct (decide ((ForAll φ) = φ0)) as [Heq | Hneq].
    + assert (Γ = Γ') by ms.
      subst.

      assert (Hp1 : Γ0 ⊢ (subst_form (bind_var t) φ)).
      apply ForAllR_rev_specialised.
      easy.
      assert (Hp2 : Γ0 ⊎ Γ' ⊢ (subst_form (bind_var t) φ)).
      apply generalised_weakeningR.
      easy.

      apply generalised_contraction.
      replace (Γ0 ⊎ Γ0 ⊎ Γ') with (Γ0 ⊎ (Γ0 ⊎ Γ')) by ms.
      apply (cutM IHw (subst_form (bind_var t) φ))
        with (Γ2 := (Γ0 ⊎ Γ')).
      rewrite weight_subst_f; simpl in Hw; lia.
      easy.

      replace  (Γ0 ⊎ Γ' • φ 〔 bind_var t 〕) with
        (Γ0 ⊎ (Γ' • φ 〔 bind_var t 〕)) by ms.

      apply (IHh (ForAll φ)).
      ms.
      easy.
      easy.
      easy.
    + assert (Hin: ForAll φ ∈ Γ') by multiset_solver.
      peapply (ForAllL (Γ0 ⊎ (Γ' ∖ {[ ForAll φ ]})) φ ψ t).
      peapply (IHh φ0 Γ0
                 (Γ' ∖ {[ForAll φ]} • (ForAll φ) • φ 〔 bind_var t 〕)
              ).
      multiset_solver.
      easy.
      easy.
      easy.
      multiset_solver.
  - apply ExistsR with (t := t).
    apply IHh with (φ := φ0); easy.
  - case (decide ((Exists φ) = φ0)) as [Heq | Hneq].
    + subst; exfalso; destruct HImp as [[A [B Heq]] | [A Heq']]; discriminate.
    + assert (Hin: (Exists φ) ∈ Γ') by multiset_solver.
      peapply (ExistsL (
                   Γ0 ⊎ (Γ' ∖ {[Exists φ]})
                 ) φ).
      assert (HeqΓMap :
          ((gmultiset_map (subst_form S') Γ0) ⊎ (gmultiset_map (subst_form S') (Γ' ∖ {[Exists φ]}))) = 
        (gmultiset_map (subst_form S') (Γ0 ⊎ Γ' ∖ {[Exists φ]}))
             ) by (apply symmetry, gmultiset_map_disj_union).
      replace (gmultiset_map (subst_form S') (Γ0 ⊎ Γ' ∖ {[Exists φ]}) • φ) with
        ((gmultiset_map (subst_form S') Γ0) ⊎
           ((gmultiset_map (subst_form S') (Γ' ∖ {[Exists φ]})) • φ)) by ms.
      pose (gmultiset_map_distr_disj_union_singleton (subst_form S')) as H1.
      pose (gmultiset_map_eq (subst_form S')) as H2.
     
      apply (IHh (subst_form S' φ0)); try easy.
      * unfold_leibniz.
        rewrite env_add_comm.
        apply equiv_disj_union_compat_r.
        rewrite <- H1.
        apply H2.
        multiset_solver.
      * rewrite weight_subst_f; lia.
      * apply hshape; easy.
      * apply relabelling_lemma; easy.
      * multiset_solver.
  - destruct (decide (((ForAll φ1) → φ2) = φ0)) as [Heq | Hneq].
    + assert (Γ' = Γ) by ms.
      subst.
      clear HeqΓ.
      apply ImpR_rev in Hp as Hp'.
      
      assert (Hp2: (Γ0 ⊎ Γ) • (ForAll φ1) ⊢ ψ).
      replace (Γ0 ⊎ Γ • (ForAll φ1)) with ((Γ0 • (ForAll φ1)) ⊎ Γ) by ms.
      apply (cutM IHw φ2); [ simpl in *; lia | easy | easy ].
      apply (IHh1 (Implies (ForAll φ1) φ2) Γ0 Γ) in Hp as Hp''; try easy.
      replace (Γ0 ⊎ Γ) with ((Γ0 ⊎ Γ) ⊎ ∅) by ms.
      apply generalised_contraction with (Γ := ∅) (Γ' := (Γ0 ⊎ Γ)). 
      replace ( Γ0 ⊎ Γ ⊎ (Γ0 ⊎ Γ) ⊎ ∅) with ((Γ0 ⊎ Γ) ⊎ (Γ0 ⊎ Γ)) by ms.
      apply (cutM IHw (ForAll φ1)); [ simpl in *; lia | easy | easy].
    + assert (Hin : ((ForAll φ1) → φ2) ∈ Γ' ) by multiset_solver.
      peapply (ImpLForAll (Γ0 ⊎ (Γ' ∖ {[ (ForAll φ1) → φ2 ]})) φ1 φ2).
      peapply (IHh1 φ0 Γ0 Γ').
      multiset_solver.
      simpl in Hw; lia.
      easy.
      easy.
      multiset_solver.
      peapply (IHh2 φ0 Γ0 ((Γ' ∖ {[ (ForAll φ1) → φ2 ]}) • φ2)).
      multiset_solver.
      lia.
      easy.
      easy.
      multiset_solver.      
  - destruct (decide ((Implies (Exists φ1) φ2) = φ0)) as [Heq | Hneq].
    + assert (Γ' = Γ) by ms.
      subst.
      clear HeqΓ.
      apply ImpR_rev in Hp as Hp'.
      apply ExistsL_rev in Hp'.
      
      apply (IHh (ForAll (Implies φ1 (subst_form S' φ2)))); [
          easy
        | simpl in *; rewrite weight_subst_f; lia
        | right; exists (Implies φ1 (subst_form S' φ2)); easy |].
      apply ForAllR.
      apply ImpR.
      easy.
    + assert (Hin: ((Exists φ1) → φ2) ∈ Γ') by multiset_solver.
      peapply (ImpLExists (Γ0 ⊎ (Γ' ∖ {[ (Exists φ1) → φ2 ]})) φ1 φ2).

      peapply (IHh φ0 Γ0 (Γ' ∖ {[ (Exists φ1) → φ2 ]} • (ForAll (φ1 → φ2〔 S' 〕 ) ))).
      multiset_solver.
      lia.
      easy.
      easy.
      multiset_solver.
Qed.
      
Lemma cut_principal_add (w : nat) (IHw : CutHyp w) (φ : form) (Γ : env)
  (hφ : weight φ <= w + 1) (hk : ImpOrForAll φ) (hd : Γ ⊢ φ) (ψ : form)
  (h2 : (Γ • φ) ⊢ ψ) : Γ ⊢ ψ.
Proof.
  replace Γ with (Γ ⊎ ∅) by ms.
  apply generalised_contraction.
  replace ((Γ ⊎ Γ) ⊎ ∅) with (Γ ⊎ Γ).
  apply cut_principal with  (φ := φ) (Δ :=  (Γ • φ)) (w := w); try easy.
  - ms.
Qed.

(* From "A New Calculus for Intuitionistic Strong Löb Logic" *)
Theorem additive_cut  Γ φ ψ :
  Γ ⊢ φ  -> Γ • φ ⊢ ψ ->
  Γ ⊢ ψ.
Proof.
  remember (weight φ) as w. assert(Hw : weight φ ≤ w) by lia. clear Heqw.
  revert φ Hw ψ Γ.
  induction w; intros φ Hw; [pose (weight_pos φ); lia|].

  intros ψ Γ HPφ HPψ.
  revert ψ HPψ.
  induction HPφ; simpl in Hw; intros.
- now apply contraction.
- apply ExFalso.
- apply AndL_rev in HPψ. do 2 apply IHw in HPψ; trivial; try lia; apply weakening; assumption.
- apply AndL. apply IHHPφ; auto with proof.
- apply OrL_rev in HPψ. apply IHHPφ. lia. destruct HPψ; easy.
- apply OrL_rev in HPψ; apply IHHPφ. lia. destruct HPψ; easy.
- apply OrL; [ apply IHHPφ1; auto | apply IHHPφ2; auto ].
  + exch 0. eapply (OrL_rev _ φ ψ). exch 0. exact HPψ.
  + exch 0. eapply (OrL_rev _ φ ψ). exch 0. exact HPψ.
- apply cut_principal_add with (w := w) (φ := (Implies φ ψ));
    try easy; simpl in *; try lia.
  left.
  exists φ, ψ. easy.
  apply ImpR.
  easy.
- apply ImpL0. eapply IHHPφ; eauto.
  exch 0; exch 1; apply (ImpL0_rev (Γ • ψ) i xs φ ψ0).
  exch 1. exch 0; easy.
- apply ImpLAnd. eapply IHHPφ; eauto.
  exch 0. apply ImpLAnd_rev. exch 0. exact HPψ.
- apply ImpLOr. eapply IHHPφ; eauto.
  exch 0. exch 1. apply ImpLOr_rev. exch 0. exact HPψ.
- apply ImpLImp; [assumption|].
  apply IHHPφ2. lia.
  exch 0. eapply ImpLImp_prev. exch 0. exact HPψ.
- apply cut_principal_add with (w := w) (φ := (ForAll φ));
    try easy; simpl in *; try lia.
  right.
  exists φ. easy.
  apply ForAllR.
  easy.
- apply ForAllL with (t := t). eapply IHHPφ; eauto.
  exch 0. exch 1. apply ForAllL_rev. exch 0. exact HPψ.
- apply IHw with (φ := (subst_form (bind_var t) φ)).
  rewrite weight_subst_f. 
  lia.
  easy.
  apply ExistsL_rev_specialised.
  easy.
- apply ExistsL. apply IHHPφ. rewrite weight_subst_f. lia.
  exch 0. backward_map. apply ExistsL_rev. exch 0. exact HPψ.
- apply ImpLForAll.  assumption.
  apply IHHPφ2. lia.
  exch 0. apply ImpLForAll_prev with (φ1 := φ1). exch 0. easy.
- apply ImpLExists. eapply IHHPφ; eauto.
  exch 0. apply ImpLExists_rev. exch 0. exact HPψ.
Qed.

(* Multiplicative cut rule *)
Theorem cut Γ Γ' φ ψ :
  Γ ⊢ φ  -> Γ' • φ ⊢ ψ ->
  Γ ⊎ Γ' ⊢ ψ.
Proof.
intros π1 π2. apply additive_cut with φ.
- apply generalised_weakeningR, π1.
- replace (Γ ⊎ Γ' • φ) with (Γ ⊎ (Γ' • φ)) by ms. apply generalised_weakeningL, π2.
Qed.
