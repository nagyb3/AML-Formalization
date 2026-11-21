From MatchingLogic.ProofMode Require Import FixPoint Misc.
From MatchingLogic Require Import ContextualImplication.
From MatchingLogic Require Export Definedness_ProofSystem.
From MatchingLogic.ProofMode Require Import FixpointRules.

Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

(* Wrap and Unwrap based on Matching μ-logic paper's lemma 91 *)
(* source: https://www.ideals.illinois.edu/items/109286 *)
(* wrap is the "only if" way, unwrap is the "if" way *)

(* Note: Γ ⊢ ϕ = ∃x.(x ∧ (x ∈ ϕ)) from lemma 91 : set_builder_full_iff *)

Section WrapUnwrap.

  Context {Σ : Signature} {definedness_syntax : Definedness_Syntax.Syntax}.

  (* (∃x. C[x] and x ∈ φ) -> ψ
     -------------------------
        x ∈ φ -> C[x] -> ψ      *)
  Lemma unwrap_step_FOL (Γ : Theory) (C : StructureContext) φ ψ (x : evar):
    well_formed φ ->
    well_formed ψ ->
    well_formed (sc_pred C) ->
    Γ ⊢ exists_quantify x ((sc_plug C (patt_free_evar x)) and (patt_free_evar x ∈ml φ)) ---> ψ ->
    Γ ⊢ (patt_free_evar x) ∈ml φ ---> (sc_plug C (patt_free_evar x) ---> ψ).
  Proof.
    intros wfphi wfpsi wfscpred H.
    toMLGoal; simpl in *.
    - wf_auto2.
    - mlIntro "Hx".
      mlIntro "HC".
      remember ((sc_plug C (patt_free_evar x)) and (patt_free_evar x ∈ml φ)) as Hbody.

      pose proof (Ex_quan Γ (evar_quantify x 0 Hbody) x) as Hex.
      unfold instantiate in Hex.

      rewrite bevar_subst_evar_quantify_free_evar in Hex.
      + subst Hbody. wf_auto2.
      + unfold exists_quantify in H. subst Hbody.
        mlApplyMeta H.
        mlApplyMeta Hex.
        mlSplitAnd.
        * mlExact "HC".
        * mlExact "Hx".
  Qed.
  
  (* Γ ⊢ C[φ] ∧ P -> C[φ ∧ P] *)
  Lemma AC_predicate_propagate_impl (Γ : Theory) C φ P :
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed φ ->
    well_formed P ->
    Γ ⊢ is_predicate_pattern P ->
    Γ ⊢ (subst_ctx C φ and P) ---> (subst_ctx C (φ and P)).
  Proof.
    intros Ht wfphi wfP Hpredpat.

    induction C as [| C IH p wfp | p C IH wfp]; simpl.
      + mlIntro "H".
        mlExact "H".
      + pose proof (predicate_propagate_left_2_meta Γ p P (subst_ctx C φ)
          Ht wfp wfP ltac:(wf_auto2) Hpredpat) as HProp.
        apply pf_iff_proj1 in HProp.
        - assert (Hin : Γ ⊢ (P and subst_ctx C φ) ---> subst_ctx C (φ and P)).
          * mlIntro "H".
            mlDestructAnd "H" as "H0" "H1".
            mlApplyMeta IH.
            mlSplitAnd; [mlExact "H1" | mlExact "H0" ].
          * pose proof (Framing_left Γ (P and subst_ctx C φ) (subst_ctx C (φ and P)) p
            AnyReasoning wfp (pile := pile_any _) Hin) as HFrame.
            mlIntro "H".
            mlDestructAnd "H" as "H0" "H1".
            mlApplyMeta HFrame. mlApplyMeta HProp.
            mlSplitAnd; [mlExact "H1" | mlExact "H0"].
       - wf_auto2.
       - wf_auto2.
     + pose proof (predicate_propagate_right_2_meta Γ (subst_ctx C φ) P p
        Ht ltac:(wf_auto2) wfP wfp Hpredpat) as HProp.
        apply pf_iff_proj1 in HProp.
      - assert (Hin : Γ ⊢ (P and subst_ctx C φ) ---> subst_ctx C (φ and P)).
        * mlIntro "H".
          mlDestructAnd "H" as "H0" "H1".
          mlApplyMeta IH.
          mlSplitAnd; [mlExact "H1" | mlExact "H0"].
        * pose proof (Framing_right Γ (P and (subst_ctx C φ)) (subst_ctx C (φ and P)) p
          AnyReasoning (pile := pile_any _) wfp Hin) as HFrame.
          mlIntro "H".
          mlDestructAnd "H" as "H0" "H1".
          mlApplyMeta HFrame.
          mlApplyMeta HProp.
          mlSplitAnd; [mlExact "H1" | mlExact "H0"].
      - wf_auto2.
      - wf_auto2.
  Qed.

  (* Γ ⊢ C[∃x. x ∧ x ∈ φ]
     --------------------
     Γ ⊢ ∃x. C[x ∧ x ∈ φ]  *)
  Lemma unwrap_step_C_property (Γ : Theory) (C : StructureContext) φ ψ (x: evar):
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed φ ->
    well_formed ψ ->
    well_formed (sc_pred C) ->
    x ∉ AC_free_evars (sc_ac C) ->
    evar_is_fresh_in x (sc_pred C) ->
    Γ ⊢ (sc_plug C (exists_quantify x (patt_free_evar x and patt_free_evar x ∈ml φ)) ---> ψ) ->
    Γ ⊢ (exists_quantify x (sc_plug C (patt_free_evar x) and patt_free_evar x ∈ml φ) ---> ψ).
  Proof.
    intros Ht wfphi wfpsi wfscpred Hxacfresh Hxscpredfresh H.
    (* ∃x. C[x ∧ x ∈ φ] *)
    eapply (syllogism_meta (B := exists_quantify x (sc_plug C (patt_free_evar x and patt_free_evar x ∈ml φ)))).
    + apply evar_quantify_well_formed. wf_auto2.
    + apply evar_quantify_well_formed. wf_auto2.
    + wf_auto2.
    + pose proof (ex_quan_monotone Γ x ((sc_plug C (patt_free_evar x)) and patt_free_evar x ∈ml φ)
      (sc_plug C (patt_free_evar x and patt_free_evar x ∈ml φ)) AnyReasoning (pile_any _)) as Hac.
      apply Hac.
      clear Hac.
        
      assert (Hpred : Γ ⊢ is_predicate_pattern (patt_free_evar x ∈ml φ)).
      { unfold patt_in. apply ceil_is_predicate. { exact Ht. } { wf_auto2. } }
      
      pose proof (AC_predicate_propagate_impl Γ (sc_ac C) (patt_free_evar x) (patt_free_evar x ∈ml φ)
        Ht ltac:(wf_auto2) ltac:(wf_auto2) Hpred) as Hacpredprop.
        
      unfold sc_plug.
      toMLGoal.
      { wf_auto2. }
      mlIntro "H".
      mlDestructAnd "H" as "H0" "H1".
      mlDestructAnd "H0" as "H00" "H01".
      mlSplitAnd.
      - mlApplyMeta Hacpredprop. mlSplitAnd. { mlExact "H00". } { mlExact "H1". }
      - mlExact "H01".
    + remember (patt_free_evar x and patt_free_evar x ∈ml φ) as θ eqn:H0.
      eapply (syllogism_meta (B := sc_plug C (exists_quantify x θ))).
      - eapply evar_quantify_well_formed. unfold sc_plug. wf_auto2.
      - unfold sc_plug. wf_auto2.
      - wf_auto2.
      - apply (Ex_gen Γ (sc_plug C θ) (sc_plug C (exists_quantify x θ)) x AnyReasoning (pile := pile_any _)).
        * unfold evar_is_fresh_in in Hxscpredfresh.
          unfold sc_plug.
          unfold exists_quantify.
          simpl.
          rewrite free_evars_subst_ctx. simpl.
          rewrite free_evars_evar_quantify.
          set_solver.
        * apply (Framing_StructureContext Γ C θ (exists_quantify x θ) AnyReasoning).
          assert (wfθ : well_formed θ).
          ++ subst θ. wf_auto2.
          ++ wf_auto2.
          ++ assert (wfexθ : well_formed (patt_exists (evar_quantify x 0 θ))).
            -- apply evar_quantify_well_formed. wf_auto2.
            -- pose proof (Ex_quan Γ (evar_quantify x 0 θ) x wfexθ) as Hex.
                unfold instantiate in Hex.
                rewrite bevar_subst_evar_quantify_free_evar in Hex.
                { wf_auto2. }
                { exact (useBasicReasoning AnyReasoning Hex). }
      - exact H.
  Qed.

  (* helper between quantifiers (b0 and x forms) *)
  Lemma exists_quantify_set_builder (Γ : Theory) (C : StructureContext) φ (x : evar):
  evar_is_fresh_in x φ ->
  exists_quantify x (patt_free_evar x and patt_free_evar x ∈ml φ) =
   (ex , b0 and b0 ∈ml φ).
  Proof.
    intros freshx.
    unfold exists_quantify in *.
    f_equal.
    simpl.
    rewrite (evar_quantify_fresh x 0 φ freshx).
    destruct (decide (x = x)).
    + cbv. reflexivity.
    + cbv. congruence.
  Qed.

  (* Γ ⊢ C[φ] -> ψ
    ---------------
     Γ ⊢ x ∈ φ -> C[x] -> ψ  *)
  Lemma unwrap_membership (Γ : Theory) (C : StructureContext) φ ψ (x : evar):
    Definedness_Syntax.theory ⊆ Γ ->
    evar_is_fresh_in x φ ->
    well_formed φ ->
    x ∉ AC_free_evars (sc_ac C) ->
    evar_is_fresh_in x (sc_pred C) ->
    Γ ⊢ sc_plug C φ ---> ψ ->
    Γ ⊢ (patt_free_evar x) ∈ml φ ---> (sc_plug C (patt_free_evar x) ---> ψ).
  Proof.
    intros hft freshx wfphi Hxacfree Hevarifx H.

    apply (unwrap_step_FOL Γ C φ ψ x); [wf_auto2 | wf_auto2 | wf_auto2 |].
  
    apply (unwrap_step_C_property Γ C φ ψ x); [exact hft | wf_auto2 | wf_auto2 | wf_auto2 | exact Hxacfree | exact Hevarifx |].

    pose proof (exists_quantify_set_builder Γ C φ x freshx).

    rewrite H0.

    Check set_builder_full_iff.
    pose proof set_builder_full_iff as base_eq.
    specialize (base_eq Γ φ hft wfphi). unfold patt_set_builder in base_eq.
    
    eapply (syllogism_meta (B := sc_plug C φ)); [wf_auto2 | wf_auto2 | wf_auto2 | |].
    + apply (Framing_StructureContext Γ C _ φ AnyReasoning); [wf_auto2 |].
      apply (pf_iff_proj2 Γ φ (ex , b0 and b0 ∈ml φ)).
      { wf_auto2. }
      { wf_auto2. }
      exact base_eq.
    + exact H.
  Qed.
  
  (*  Γ ⊢ x ∈ φ -> (C[x] -> ψ)
      ------------------------
      Γ ⊢ x ∈ φ -> ⌊ C[x] -> ψ ⌋  *)
  Lemma unwrap_step_total (Γ : Theory) (C : StructureContext) φ ψ (x : evar):
  Definedness_Syntax.theory ⊆ Γ ->
  well_formed φ ->
  well_formed ψ ->
  Γ ⊢ (patt_free_evar x) ∈ml φ ---> (sc_plug C (patt_free_evar x) ---> ψ) ->
  Γ ⊢ (patt_free_evar x) ∈ml φ ---> patt_total (sc_plug C (patt_free_evar x) ---> ψ).
  Proof.
    intros Ht wfphi wfpsi H.
    pose proof (wfH := proved_impl_wf _ _ (proj1_sig H)).
    pose proof (wfCPsi := well_formed_imp_proj2 _ _ wfH).
    
    remember (free_evars (patt_free_evar x and φ)) as S.
    remember (evar_fresh_s S) as a.
    remember (evar_fresh_s (S ∪ {[a]})) as b.
    remember (evar_fresh_s (S ∪ {[a;b]})) as c.
    
    assert (Ha : a ∉ S).
    { subst a. apply set_evar_fresh_is_fresh'. }
    
    assert (Hb : b ∉ S ∪ {[a]}).
    { subst b. apply set_evar_fresh_is_fresh'. }
    
    assert (Hc : c ∉ S ∪ {[a;b]}).
    { subst c. apply set_evar_fresh_is_fresh'. }

    subst S.

    pose proof (def_phi_impl_tot_def_phi Γ (patt_free_evar x and φ) AnyReasoning a b c
      Ht ltac:(wf_auto2) Ha Hb Hc ltac:(try_solve_pile)) as Hdef.
    
    pose proof (floor_monotonic Γ (patt_free_evar x ∈ml φ) (sc_plug C (patt_free_evar x) ---> ψ)
      AnyReasoning Ht ltac:(wf_auto2) ltac:(wf_auto2) H) as HFloor.
    
    eapply (syllogism_meta (B := patt_total (patt_free_evar x ∈ml φ))).
    + wf_auto2.
    + wf_auto2.
    + wf_auto2.
    + unfold patt_in. exact Hdef.
    + exact HFloor. 
  Qed.

  (* Γ ⊢ x ∈ φ -> ⌊ C[x] -> ψ ⌋
    ---------------------------
    ∃x. x ∧ ⌊ C[x] -> ψ ⌋
   *)
  Lemma unwrap_FOL_step (Γ : Theory) (C : StructureContext) φ ψ (x : evar):
  Definedness_Syntax.theory ⊆ Γ ->
  well_formed φ ->
  well_formed ψ ->
  well_formed (sc_pred C) ->
  Γ ⊢ (patt_free_evar x) ∈ml φ ---> patt_total (sc_plug C (patt_free_evar x) ---> ψ) ->
  Γ ⊢ (exists_quantify x (patt_free_evar x and patt_free_evar x ∈ml φ)) --->
    exists_quantify x (patt_free_evar x and patt_total ((sc_plug C (patt_free_evar x)) ---> ψ)).
  Proof.
    intros Ht wfphi wfpsi wfscpred H.
    apply ex_quan_monotone.
    + try_solve_pile.
    + mlIntro "H".
      mlDestructAnd "H" as "Hpatx" "Helem".
      mlSplitAnd.
      - mlExact "Hpatx".
      - mlApplyMeta H.
        mlExact "Helem".
  Qed.

  (*   ∃x. x ∧ ⌊ C[x] -> ψ ⌋  =  C ⊸ ψ   *)
  Lemma exists_quantify_contextual_implication (C: StructureContext) ψ x:
    x ∉ AC_free_evars (sc_ac C) ->
    evar_is_fresh_in x (sc_pred C) ->
    evar_is_fresh_in x ψ ->
    exists_quantify x (patt_free_evar x and patt_total (sc_plug C (patt_free_evar x) ---> ψ))
    = contextual_implication C ψ.
  Proof.
    intros HAC Hpred Hpsi.
    unfold exists_quantify, contextual_implication, patt_set_builder, patt_subseteq, sc_plug.
    f_equal.
    simpl.
    rewrite evar_quantify_subst_ctx.
    + exact HAC.
    + rewrite (evar_quantify_fresh x 0 (sc_pred C) Hpred).
      rewrite (evar_quantify_fresh x 0 ψ Hpsi).
      simpl.
      destruct (decide (x = x)).
      - simpl. reflexivity.
      - simpl. congruence.
  Qed.

  (*
    Γ ⊢ φ -> (C ⊸ ψ)
    ----------------
    Γ ⊢ φ -> ∃x. (x ∧ ⌊ C[x] -> ψ ⌋)
  *)
  Lemma contextual_implication_exists_quantify (Γ : Theory)
    (C : StructureContext) φ ψ x:
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed φ ->
    well_formed ψ ->
    x ∉ AC_free_evars (sc_ac C) ->
    evar_is_fresh_in x (sc_pred C) ->
    evar_is_fresh_in x ψ ->
    Γ ⊢ φ ---> (contextual_implication C ψ) ->
    Γ ⊢ φ ---> exists_quantify x (patt_free_evar x
      and patt_total (sc_plug C (patt_free_evar x) ---> ψ)).
   Proof.
    intros Ht wfphi wfpsi Hxnotfreescac Hxnotfreescpred Hxfreshpsi H.
    
    rewrite (exists_quantify_contextual_implication C ψ x Hxnotfreescac Hxnotfreescpred Hxfreshpsi).
    
    exact H.
   Qed.

  Lemma wrap_membership_introduction_step (Γ : Theory) (C: StructureContext) φ ψ x y:
    Γ ⊢ φ ---> exists_quantify x (patt_free_evar x and ⌊ sc_plug C (patt_free_evar x) ---> ψ ⌋) ->
    Γ ⊢ patt_free_evar y ∈ml φ ---> exists_quantify x ((patt_free_evar y ∈ml patt_free_evar x) and ⌊ sc_plug C (patt_free_evar x) ---> ψ ⌋).
  Proof.
    
  Admitted.

  Lemma wrap_elem_eq_eq (Γ : Theory) x y:
   patt_free_evar y ∈ml patt_free_evar x = patt_free_evar y =ml patt_free_evar x.
  Proof.
    
  Admitted.

  (* Γ ⊢ φ -> (C ⊸ ψ) 
  ---------------
     Γ ⊢ C[φ] -> ψ   *)
  (* layer 1 lemma for wrap *)
  Lemma wrap
    (Γ : Theory)
    (C : StructureContext) φ ψ:
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed φ ->
    well_formed ψ ->
    well_formed (sc_pred C) ->
    Γ ⊢ φ ---> (contextual_implication C ψ) ->
    Γ ⊢ sc_plug C φ ---> ψ.
  Proof.
    intros Ht wfphi wfpsi wfscpred H.

    remember (evar_fresh (elements (free_evars φ ∪ free_evars ψ ∪ free_evars (sc_pred C) ∪ AC_free_evars (sc_ac C)))) as x eqn:Hx.
    apply X_eq_evar_fresh_impl_X_notin_S in Hx.

    remember (evar_fresh (elements (free_evars φ ∪ free_evars ψ ∪
      free_evars (sc_pred C) ∪ free_evars (sc_plug C (patt_free_evar x)) ∪ {[x]}))) as y eqn:Hy.
    apply X_eq_evar_fresh_impl_X_notin_S in Hy.

    pose proof (contextual_implication_exists_quantify Γ C φ ψ x Ht wfphi wfpsi) as H0.

    apply H0 in H.
    2: { set_solver. }
    3: { unfold evar_is_fresh_in. set_solver. }
    2: { unfold evar_is_fresh_in. set_solver. }
    clear H0.

    apply (wrap_membership_introduction_step _ _ _ _ x y) in H.
    
    pose proof (wrap_elem_eq_eq Γ x y) as Hwrap_elem_eq_eq.
    rewrite Hwrap_elem_eq_eq in H; clear Hwrap_elem_eq_eq.
  Admitted.

  (* layer 1 unwrap lemma: *)
  (* Γ ⊢ C[φ] -> ψ
    ---------------
    Γ ⊢ φ -> (C ⊸ ψ)  *)
  Lemma unwrap (Γ : Theory)
    (C : StructureContext) φ ψ :
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed φ ->
    well_formed ψ ->
    well_formed (sc_plug C φ ---> ψ) ->
    well_formed (sc_pred C) ->
    Γ ⊢ sc_plug C φ ---> ψ ->
    Γ ⊢ φ ---> (contextual_implication C ψ).
  Proof.
    intros Ht wfphi wfpsi wfplugimp wfscpred H.
    
    remember (evar_fresh (elements (free_evars φ ∪
      free_evars ψ ∪
      free_evars (sc_pred C) ∪
      AC_free_evars (sc_ac C)))) as x eqn:Hx.
    apply X_eq_evar_fresh_impl_X_notin_S in Hx.

    pose proof set_builder_full_iff as base_eq.
    
    specialize (base_eq Γ φ Ht wfphi).
    unfold patt_set_builder in base_eq.
    
    toMLGoal; simpl in *.
    + wf_auto2.
    + Check unwrap_membership.
      Search evar_fresh.
      assert (Hisxfresh : evar_is_fresh_in x φ).
      - unfold evar_is_fresh_in. set_solver.
      - pose proof (unwrap_membership Γ C φ ψ x Ht ltac:(set_solver) ltac:(wf_auto2)) as Hbase.
        specialize (Hbase ltac:(set_solver) ltac:(unfold evar_is_fresh_in; set_solver)).

        Check unwrap_step_total.
        pose proof (unwrap_step_total Γ C φ ψ x Ht wfphi ltac:(wf_auto2)) as Hstep_total.

        specialize (Hbase H).
        specialize (Hstep_total Hbase).

        pose proof (unwrap_FOL_step Γ C φ ψ x Ht) as Hunwrap_FOL_step.
        specialize (Hunwrap_FOL_step wfphi wfpsi wfscpred Hstep_total).

        (* 'Then by the equality ϕ = ∃x.(x ∧ x ∈ ϕ) we are done' *)
        fromMLGoal.

        rewrite (exists_quantify_set_builder Γ C φ x Hisxfresh) in Hunwrap_FOL_step.
        rewrite (exists_quantify_contextual_implication C ψ x) in Hunwrap_FOL_step.
        * set_solver.
        * unfold evar_is_fresh_in. set_solver.
        * unfold evar_is_fresh_in. set_solver.
        * apply (syllogism_meta (B := ex, b0 and b0 ∈ml φ)).
          ++ wf_auto2.
          ++ wf_auto2.
          ++ wf_auto2.
          ++ apply (pf_iff_proj1 Γ φ (ex, b0 and b0 ∈ml φ)).
            -- wf_auto2.
            -- wf_auto2.
            -- exact base_eq.
          ++ exact Hunwrap_FOL_step.
  Qed.

  (* layer 2 lemmas for wrap and unwrap *)
  Lemma MLGoal_unwrap
     Γ φ ψ (C : StructureContext):
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed φ ->
    well_formed (sc_pred C) ->
    well_formed ψ ->
    of_MLGoal (mkMLGoal Σ Γ [] (sc_plug C φ ---> ψ) AnyReasoning) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> (contextual_implication C ψ)) AnyReasoning).
  Proof.
    intros Ht wfphi wfscpred wfpsi H.
    unfold of_MLGoal in *. simpl in *.

    intros _ wfl.

    specialize (H ltac:(wf_auto2) wfl).

    apply unwrap.
    + exact Ht.
    + wf_auto2
    + wf_auto2
    + wf_auto2 
    + wf_auto2.
    + wf_auto2.
    + wf_auto2.
    + wf_auto2.
    + exact H.
  Qed.
  
  Lemma MLGoal_wrap
     Γ φ ψ (C : StructureContext):
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed φ ->
    well_formed ψ ->
    well_formed (sc_pred C) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> (contextual_implication C ψ)) AnyReasoning) ->
    of_MLGoal (mkMLGoal Σ Γ [] (sc_plug C φ ---> ψ) AnyReasoning).
  Proof.
    intros Ht wfphi wfpsi wfscpred H.
    unfold of_MLGoal in *. simpl in *.

    intros _ wfl.

    apply wrap.
    + exact Ht.
    + wf_auto2.
    + wf_auto2.
    + wf_auto2.
    + specialize (H ltac:(wf_auto2) wfl).
      exact H.
  Qed.

  Print Assumptions MLGoal_unwrap.
  Print Assumptions MLGoal_wrap.

End WrapUnwrap.

Tactic Notation "mlWrap" := _ensureProofMode; apply MLGoal_wrap; [try assumption | wf_auto2 | wf_auto2 | wf_auto2 |].
Tactic Notation "mlUnwrap" := _ensureProofMode; apply MLGoal_unwrap; [try assumption | wf_auto2 | wf_auto2 | wf_auto2 |].

Section WrapUnwrapExamples.

  Lemma example_unwrap1 {Σ : Signature}
     {definedness_syntax : Definedness_Syntax.Syntax}
     Γ a b (C : StructureContext) :
     Definedness_Syntax.theory ⊆ Γ ->
     well_formed a ->
     well_formed b ->
     well_formed (sc_pred C) ->
     Γ ⊢ sc_plug C a ---> b ->
     Γ ⊢ a ---> (contextual_implication C b).
  Proof.
    intros.
    mlUnwrap.
    fromMLGoal.
    exact H3.
  Qed.

  Lemma example_wrap1 {Σ : Signature}
    {definedness_syntax: Definedness_Syntax.Syntax}
    Γ a b (C : StructureContext) :
     well_formed a ->
     well_formed b ->
     well_formed (sc_pred C) ->
     Definedness_Syntax.theory ⊆ Γ ->
    Γ ⊢ a ---> (contextual_implication C b) ->
    Γ ⊢ sc_plug C a ---> b.
  Proof.
    intros.
    mlWrap.
    fromMLGoal.
    assumption.
  Qed.
  
End WrapUnwrapExamples.