(** * Cut Admissibility *)
Require Import G4i.Formulas G4i.Sequents G4i.Order.
Require Import G4i.SequentProps.
Require Import Stdlib.Program.Equality.

Local Hint Rewrite @elements_env_add : order.

(* From "A New Calculus for Intuitionistic Strong Löb Logic" *)
Theorem additive_cut  Γ φ ψ :
  Γ ⊢ φ  -> Γ • φ ⊢ ψ ->
  Γ ⊢ ψ.
Proof.
  (* Get induction on weight *)
remember (weight φ) as w. assert(Hw : weight φ ≤ w) by lia. clear Heqw.
revert φ Hw ψ Γ.
induction w; intros φ Hw; [pose (weight_pos φ); lia|].
intros ψ Γ.
(*
remember (Γ, ψ) as pe.
replace Γ with pe.1 by now subst.
replace ψ with pe.2 by now subst. clear Heqpe Γ ψ. revert pe φ Hw.
refine  (@well_founded_induction _ _ wf_pointed_env_ms_order _ _).
intros (Γ &ψ). simpl. intro IHW'. assert (IHW := fun Γ0 => fun ψ0 => IHW' (Γ0, ψ0)).
simpl in IHW. clear IHW'. intros φ Hw HPφ HPψ.
Ltac otac Heq := subst; repeat rewrite env_replace in Heq by trivial; repeat rewrite env_add_remove by trivial; order_tac; rewrite Heq; order_tac.
 *)
intros HPφ HPψ.
remember (height HPφ + height HPψ) as h.
assert(Hleh : height HPφ + height HPψ ≤ h) by lia. clear Heqh.
revert Γ ψ HPφ HPψ Hleh.
induction h; intros; [ pose (height_0 HPφ); lia |].


destruct HPφ; simpl in Hw.
- now apply contraction.
- apply ExFalso.
- apply AndL_rev in HPψ. do 2 apply IHw in HPψ; trivial; try lia; apply weakening; assumption.
- apply AndL. apply IHW with (φ := θ); auto with proof. order_tac.
- apply OrL_rev in HPψ; apply (IHw φ); [lia| |]; tauto.
- apply OrL_rev in HPψ; apply (IHw ψ0); [lia| |]; tauto.
- apply OrL; apply IHW with (φ := θ); auto with proof.
  + otac Heq.
  + exch 0. eapply (OrL_rev _ φ ψ0). exch 0. exact HPψ.
  + order_tac.
  + exch 0. eapply (OrL_rev _ φ ψ0). exch 0. exact HPψ.
- (* (V) *) (* hard:  *)
  (* START *)
  remember (Γ • (φ → ψ0)) as Γ' eqn:HH.
  assert (Heq: Γ ≡ Γ' ∖ {[ φ → ψ0]}) by ms.
  assert (Hin : (φ → ψ0) ∈ Γ')by ms.
  rw Heq 0. destruct HPψ.
  + forward. auto with proof.
  + forward. auto with proof.
  + apply AndR.
     * rw (symmetry Heq) 0. apply IHW with (φ := (φ → ψ0)).
       -- order_tac.
       -- simpl. lia.
       -- now apply ImpR.
       -- peapply HPψ1.
     * rw (symmetry Heq) 0. apply IHW with (φ := (φ → ψ0)).
       -- order_tac.
       -- simpl. lia.
       -- apply ImpR. peapply HPφ.
       -- peapply HPψ2.
  + forward. apply AndL. apply IHW with (φ := (φ → ψ0)).
    * unfold pointed_env_ms_order. otac Heq.
    * simpl. lia.
    * apply AndL_rev. backward. rw (symmetry Heq) 0. apply ImpR, HPφ.
    * backward. peapply HPψ.
  + apply OrR1, IHW with (φ := (φ → ψ0)).
    * rewrite HH, env_add_remove. order_tac.
    * simpl. lia.
    * rw (symmetry Heq) 0. apply ImpR, HPφ.
    * peapply HPψ.
  + apply OrR2, IHW with (φ := (φ → ψ0)).
    * rewrite HH, env_add_remove. order_tac.
    * simpl. lia.
    * rw (symmetry Heq) 0. apply ImpR, HPφ.
    * peapply HPψ.
  + clear Hleh; forward. apply ImpR in HPφ.
       assert(Hin' : (φ0 ∨ ψ) ∈ ((Γ0 • φ0 ∨ ψ) ∖ {[φ→ ψ0]}))
            by (apply in_difference; [discriminate|ms]).
       assert(HPφ' : (((Γ0 • φ0 ∨ ψ) ∖ {[φ→ ψ0]}) ∖ {[φ0 ∨ ψ]} • φ0 ∨ ψ) ⊢ (φ → ψ0))
            by (rw (symmetry (difference_singleton _ (φ0 ∨ψ) Hin')) 0; peapply HPφ).
       assert (HP := (OrL_rev  _ φ0 ψ (φ → ψ0) HPφ')).
       apply OrL.
      * apply IHW with (φ := (φ → ψ0)).
        -- rewrite env_replace in Heq by trivial. order_tac. rewrite Heq. order_tac.
        -- simpl. lia.
        -- peapply HP.1.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ1.
      * apply IHW with (φ := (φ → ψ0)).
        -- rewrite env_replace in Heq by trivial. order_tac. rewrite Heq. order_tac.
        -- simpl. lia.
        -- peapply HP.2.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + rw (symmetry Heq) 0. apply ImpR, IHW with (φ := (φ → ψ0)).
    -- order_tac.
    -- simpl. lia.
    -- apply weakening, ImpR,  HPφ.
    -- exch 0.  rewrite <- HH. exact HPψ.
  + case (decide ((Atom i xs → φ0) = (φ → ψ0))).
    * intro Heq'; dependent destruction Heq'.
      replace ((Γ0 • Atom i xs • (Atom i xs → ψ0)) ∖ {[Atom i xs → ψ0]}) with (Γ0 • Atom i xs) by ms.
      apply (IHw ψ0).
      -- lia.
      -- apply contraction. peapply HPφ.
      -- assumption.
    * intro Hneq. do 2 forward. exch 0. apply ImpL0, IHW with (φ := (φ → ψ0)).
      -- repeat rewrite env_replace in Heq by trivial. order_tac. rewrite Heq. order_tac.
      -- simpl. lia.
      -- apply ImpL0_rev. exch 0. do 2 backward.
            rw (symmetry Heq) 0. apply ImpR, HPφ.
        -- exch 0; exch 1. rw (symmetry (difference_singleton _ _ Hin1)) 2. exact HPψ.
  + case (decide (((φ1 ∧ φ2) → φ3)= (φ → ψ0))).
      * intro Heq'; dependent destruction Heq'. rw (symmetry Heq) 0.
         apply (IHw (φ1 → φ2 → ψ0)).
        -- simpl in *. lia.
        -- apply ImpR, ImpR, AndL_rev, HPφ.
        -- peapply HPψ.
      * intro Hneq. forward. apply ImpLAnd, IHW with (φ := (φ → ψ0)).
        -- rewrite env_replace in Heq by trivial. order_tac. rewrite Heq. order_tac.
        -- simpl. lia.
        -- apply ImpLAnd_rev. backward. rw (symmetry Heq) 0. apply ImpR, HPφ.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ.
  + clear Hleh; case (decide (((φ1 ∨ φ2) → φ3)= (φ → ψ0))).
      * intro Heq'; dependent destruction Heq'. rw (symmetry Heq) 0. apply OrL_rev in HPφ.
         apply (IHw (φ1 → ψ0)).
        -- simpl in *. lia.
        -- apply (IHw (φ2 → ψ0)).
           ++ simpl in *; lia.
           ++ apply ImpR, HPφ.
           ++ apply weakening, ImpR, HPφ.
        -- apply (IHw (φ2 → ψ0)).
           ++ simpl in *; lia.
           ++ apply weakening, ImpR, HPφ.
           ++ peapply HPψ.
      * intro Hneq. forward. apply ImpLOr, IHW with (φ := (φ → ψ0)).
        -- rewrite env_replace in Heq by trivial. order_tac. rewrite Heq. order_tac.
        -- simpl. lia.
        -- apply ImpLOr_rev. backward. rw (symmetry Heq) 0. apply ImpR, HPφ.
        -- exch 0. exch 1. rw (symmetry (difference_singleton _ _ Hin0)) 2. exact HPψ.
  + case (decide (((φ1 → φ2) → φ3) = (φ → ψ0))).
    * intro Heq'. dependent destruction Heq'. rw (symmetry Heq) 0. apply (IHw ψ0).
      -- lia.
      -- apply (IHw(φ1 → φ2)).
        ++ lia.
        ++ apply (IHw (φ2 → ψ0)).
            ** simpl in *. lia.
            ** apply ImpR.
               apply (IHw (φ1 → φ2)).
               --- lia.
               --- apply ImpR. exch 0. apply generalised_axiom.
               --- exch 0. apply weakening. peapply HPφ.
            ** apply ImpR. exch 0. peapply HPψ1.
        ++ exact HPφ.
    -- peapply HPψ2.
   *  (* (V-d) *)
       intro Hneq. forward. apply ImpLImp.
      -- apply IHW with (φ := (φ → ψ0)).
         ++ (* otac Heq. *)
            rewrite env_replace in Heq by trivial.
            order_tac.
            rewrite Heq.
            order_tac.
         ++ simpl. lia.
        ++ apply contraction. apply ImpLImp_dup. backward. rw (symmetry Heq) 0.
                apply ImpR, HPφ.
        ++ exch 0. apply ImpR_rev. exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. apply ImpR.
                exact HPψ1.
      -- apply IHW with (φ := (φ → ψ0)).
         ++ otac Heq.
         ++ simpl. lia.
         ++ apply ImpLImp_prev with (φ1 := φ1) (φ2 := φ2).
            backward.
            rw (symmetry Heq) 0.
            apply ImpR, HPφ.
        ++ exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + (* QUANTIFIER CASE *)
    clear Hleh; apply ForAllR. replace (Γ0 ∖ {[φ → ψ0]}) with (Γ) by (unfold_leibniz; exact Heq).
    apply IHW with (φ := (subst_form S' (φ → ψ0))).
    -- order_tac.
       unfold env_order, ltof.
       rewrite !env_weight_add.
       rewrite !env_weight_elements_subst.
       assert (weight φ0 < weight (ForAll φ0)) as Hlt1 by (simpl; lia).
       apply pow5_a_lt_b in Hlt1.
       lia.
    -- simpl.
       pose (subst_weight_general φ S' 0) as H1.
       pose (subst_weight_general ψ0 S' 0) as H2.
       simpl in H1, H2.
       lia.
    -- simpl. apply ImpR. backward_map.
       apply relabelling_lemma with (f := S') in HPφ.
       exact HPφ.
       apply (inj_upN_S 0).
    -- backward_map.
       rewrite <- HH.
       exact HPψ.
  + (* TODO Currently trying to do a proof  by induction on the height of the premise *)
    forward.
    apply ForAllL with (t := t).
    apply IHW with (φ := (φ → ψ0)).
    -- rewrite env_replace in Heq by trivial.
       order_tac.
       rewrite Heq.
       order_tac.
      order_tac.
       admit.  (* Definitely false *)
    -- simpl. lia.
    -- exch 0. backward. rw (symmetry Heq) 1. apply ImpR. exch 0. apply weakening. exact HPφ.
    -- backward. rewrite env_add_remove. assumption.
  + rw (symmetry Heq) 0. apply ExistsR with (t := t), IHW with (φ := (φ → ψ0)).
    -- assert ( (subst_form (bind_var t) φ0) ≺f (Exists φ0) ) as H1.
       unfold form_order.
       pose (subst_weight_general φ0 (bind_var t) 0) as H2.
       simpl in H2.
       simpl.
       rewrite H2.
       lia.
       order_tac.
    -- simpl. lia.
    -- apply ImpR. exact HPφ.
    -- rw (Heq) 1. backward. rewrite env_add_remove. exact HPψ.
  + forward. apply ExistsL. apply IHW with (φ := ((subst_form S' (φ → ψ0)))).
    -- otac Heq.
       unfold env_order, ltof.
       rewrite !env_weight_add.
       rewrite !env_weight_elements_subst.
       pose (subst_weight_general ψ S' 0) as Hw1.
       simpl in Hw1.
       rewrite Hw1.
       assert (weight φ0 < weight (Exists φ0)) as Hlt1 by (simpl; lia).
       apply pow5_a_lt_b in Hlt1.
       lia.
    -- pose (subst_weight_general (φ → ψ0) S' 0) as H1.
       simpl. simpl in H1.
       rewrite H1.
       lia.
    -- simpl. 
       apply ImpR.
       exch 0.
       backward_map.
       apply ExistsL_rev.
       backward.
       rw (symmetry Heq) 1.
       exact HPφ.
    -- exch 0. backward_map.
       backward2.
       rewrite env_add_remove.
       exact HPψ.
  + case (decide (((ForAll φ1) → φ2) = (φ → ψ0))).
    * intro Heq'. dependent destruction Heq'. rw (symmetry Heq) 0.
      apply (IHw(  ψ0 )  ).
      -- lia.
      -- apply (IHw( ForAll φ1 )).
         ++ lia.
         ++ assert (Γ = Γ0) by ms.
            subst.
            pose (ImpR Γ0 (ForAll φ1) ψ0 HPφ) as HP1.  
            apply (IHh Γ0 (ForAll φ1) HP1 HPψ1).
            simpl in Hleh.
            simpl.
            lia.
            (* PROVING IHW WTF!*)

            apply IHW.
            apply (H (S(height HPφ + height HPψ1)) Γ (ForAll φ1) HP1 HPψ1).
            simpl.
            lia.
           
             apply IHW with (φ := (ForAll φ1) → ψ0).
            ** order_tac. admit. (* Definitely false *)
            ** simpl.
               simpl in Hw.
               lia.
            ** apply ImpR. exact HPφ.
            ** rewrite <- HH. exact HPψ1.
         ++ exact HPφ.
      -- rw (Heq) 1. rewrite env_add_remove. exact HPψ2.
    * intros.
      apply IHW with (φ := (φ → ψ0)).
      -- order_tac. admit. (* Definitely false *)
      -- simpl. lia.
      -- rw (symmetry Heq) 0. apply ImpR. assumption.
      -- forward. exch 0. backward. rewrite env_add_remove.
         apply ImpLForAll; assumption.
  + case (decide (((Exists φ1) → φ2) = (φ → ψ0))).
    * intro Heq'. dependent destruction Heq'. rw (symmetry Heq) 0.
      apply (IHw( ForAll (φ1 → (subst_form S' ψ0)) )  ).   
      -- simpl. simpl in Hw.
         pose (subst_weight_general ψ0 S' 0) as H1.
         simpl in H1.
         lia.
      -- apply ForAllR, ImpR, ExistsL_rev, HPφ.
      -- peapply HPψ.
    * intros. forward. apply ImpLExists. apply IHW with (φ := φ → ψ0).
      -- assert ( (ForAll (φ1 → φ2 〔 S' 〕)) ≺f  ((Exists φ1) → φ2) ).
         unfold form_order.
         simpl.
         pose (subst_weight_general φ2 S' 0) as H1.
         simpl in H1.
         rewrite H1.
         lia.
         otac Heq.
      -- simpl. lia.
      -- apply ImpLExists_rev. backward.
         rw (symmetry Heq) 0.
         apply ImpR, HPφ.
      -- exch 0. apply contraction.  apply ImpLExists_rev. backward.
         rw (symmetry Heq) 2.
         rewrite <- HH.
         exch 0.
         apply weakening.
         exact HPψ.
- apply ImpL0. eapply IHW; eauto.
  + otac Heq.
  + exch 0. exch 1.  apply ImpL0_rev. exch 1. exch 0. exact HPψ.
- apply ImpLAnd. eapply IHW; eauto.
  + otac Heq.
  + exch 0. apply ImpLAnd_rev. exch 0. exact HPψ.
- apply ImpLOr. eapply IHW; eauto.
  + order_tac.
  + exch 0. exch 1. apply ImpLOr_rev. exch 0. exact HPψ.
- apply ImpLImp; [assumption|].
  apply IHW with (φ := ψ0).
  + otac Heq.
  + lia.
  + assumption.
  + exch 0. eapply ImpLImp_prev. exch 0. exact HPψ.
- (* Copy of (V) but with ForAll *)
  revert HPψ.
  remember ( (Γ • (ForAll φ)) ) as Γ' eqn:HH.
  replace (Γ • (ForAll φ)) with Γ'.
  intros.
  assert (Heq: Γ ≡ Γ' ∖ {[ ForAll φ]}) by ms.
  assert (Hin : (ForAll φ) ∈ Γ')by ms.
  (* DUPLICATE CASE WITH (V) EXCEPT FORALL NOT IMP *)
  rw Heq 0. destruct HPψ; admit.
  (* YOU WILL NEED THESE
  + forward. apply Init.
  + forward. auto with proof.
  + apply AndR.
     * rw (symmetry Heq) 0. apply IHW with (φ := (ForAll φ)).
       -- order_tac.
       -- simpl. lia.
       -- now apply ForAllR.
       -- peapply HPψ1.
     * rw (symmetry Heq) 0. apply IHW with (φ := (ForAll φ)).
       -- order_tac.
       -- simpl. lia.
       -- apply ForAllR. peapply HPφ.
       -- peapply HPψ2.
  ...
  + apply ForAllR. replace (Γ0 ∖ {[ForAll φ]}) with (Γ) by (unfold_leibniz; exact Heq).
    apply IHW with (φ := (subst_form S' (ForAll φ))).
    -- order_tac.
       unfold env_order, ltof.
       rewrite !env_weight_add.
       rewrite !env_weight_elements_subst.
       assert (weight φ0 < weight (ForAll φ0)) as Hlt1 by (simpl; lia).
       apply pow5_a_lt_b in Hlt1.
       lia.
    -- simpl.
       pose (subst_weight_general φ (up S') 0) as H1.
       simpl in H1.
       lia.
    -- simpl. apply ForAllR.
       apply relabelling_lemma with (f := (up S')) in HPφ.
       rewrite gmultiset_map_compose, subst_form_compose.
       change (S' ☉ S') with (up S' ☉ S').
       rewrite <- subst_form_compose, <- gmultiset_map_compose.
       exact HPφ.
       apply (inj_upN_S 1).
    -- backward_map.
       rewrite <- HH.
       exact HPψ. *)
- apply ForAllL with (t := t). eapply IHW; eauto.
  + order_tac.

    admit. (* Definitely false *)
  + exch 0. exch 1. apply ForAllL_rev. exch 0. exact HPψ.
- admit. (* Copy of previous case *)
- apply ExistsL. apply IHW with (φ := subst_form S' (ψ0)).
  + order_tac.
    unfold env_order, ltof.
    rewrite !env_weight_add.
    rewrite !env_weight_elements_subst.
    pose (subst_weight_general ψ S' 0) as Hw1.
    simpl in Hw1.
    rewrite Hw1.
    assert (weight φ < weight (Exists φ)) as Hlt1 by (simpl; lia).
    apply pow5_a_lt_b in Hlt1.
    lia.
  + pose (subst_weight_general ψ0 S' 0) as H1.
    simpl in H1.
    lia.
  + exact HPφ.
  + exch 0. backward_map. apply ExistsL_rev. exch 0. exact HPψ.
- apply ImpLForAll.
  + apply IHW with (φ := ψ0).
    * order_tac.
      admit. (* Definately not true *)
    * lia.
    * apply ImpLForAll; assumption.
    * apply weakening; assumption.
  + eapply IHW; eauto.
    * order_tac.
    * exch 0. apply ImpLForAll_prev with (φ1 := φ1). exch 0. exact HPψ.
- apply ImpLExists. eapply IHW; eauto.
  + assert ( (ForAll (φ1 → φ2 〔 S' 〕)) ≺f  ((Exists φ1) → φ2) ).
    unfold form_order.
    simpl.
    pose (subst_weight_general φ2 S' 0) as H1.
    simpl in H1.
    rewrite H1.
    lia.
    order_tac.
  + exch 0. apply ImpLExists_rev. exch 0. exact HPψ.
Admitted.

(* Multiplicative cut rule *)
Theorem cut Γ Γ' φ ψ :
  Γ ⊢ φ  -> Γ' • φ ⊢ ψ ->
  Γ ⊎ Γ' ⊢ ψ.
Proof.
intros π1 π2. apply additive_cut with φ.
- apply generalised_weakeningR, π1.
- replace (Γ ⊎ Γ' • φ) with (Γ ⊎ (Γ' • φ)) by ms. apply generalised_weakeningL, π2.
Qed.
