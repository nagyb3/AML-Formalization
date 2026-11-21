From MatchingLogic.ProofMode Require Import FixPoint Misc.
From MatchingLogic Require Import ContextualImplication.
From MatchingLogic Require Export Definedness_ProofSystem.

Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

(* TODO: check how we could rephrase the layer 2 lemmas to use arbitiary l instead of [] *)
(* note: this might not be needed for the actual automation but would probably be the proper way to do it *)

(* Reference for `=lfp`: definition 28 in Matching μ-logic *)

Section Frame.

  Context {Σ : Signature} {definedness_syntax : Definedness_Syntax.Syntax}.

  Lemma Framing_StructureContext (Γ : Theory) (C : StructureContext)
    (A B : Pattern) (i : ProofInfo):
    well_formed (sc_pred C) -> 
    Γ ⊢i (A ---> B) using i ->
    Γ ⊢i ((sc_plug C A) ---> (sc_plug C B)) using i.
  Proof.
    intros wfpred H.

    destruct C.
    unfold sc_plug; simpl.
    
    assert (HC: Γ ⊢i sc_ac.[□↦A] ---> sc_ac.[□↦B] using i).
    + apply Framing.
      - try_solve_pile.
      - exact H.

    + toMLGoal; simpl in *.
      - wf_auto2.
      - mlIntro "H0".
        mlDestructAnd "H0" as "Hac" "Hpred".
        mlSplitAnd.
        * mlApplyMeta HC. mlExact "Hac".
        * mlExact "Hpred".
  Qed.
  
  Lemma MLGoal_frame
    Γ i φ ψ (C : StructureContext) :
    well_formed (sc_pred C) ->
    well_formed (φ ---> ψ) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> ψ) i) -> 
    of_MLGoal (mkMLGoal Σ Γ [] (sc_plug C φ ---> sc_plug C ψ) i).
  Proof.
    intros wfc wfimp H.

    unfold of_MLGoal in *. simpl in *.

    intros _ wfl.

    specialize (H wfimp wfl).

    apply Framing_StructureContext.
    - wf_auto2.
    - exact H.
  Qed.

  (* helper lemma for the unfoldr tactic *)
  Lemma MLGoal_unfoldr_derive_impl Γ (C : StructureContext) φ A B i :
    Γ ⊢i φ ---> sc_plug C A using i ->
    well_formed (sc_pred C) ->
    well_formed φ ->
    well_formed A ->
    well_formed B ->
    of_MLGoal (mkMLGoal Σ Γ [] (A ---> B) i) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> sc_plug C B) i).
  Proof.
    intros HscplugA wfscpred wfphi wfA wfB HABimpl.
    
    unfold of_MLGoal in *. simpl in *.
    intros _ wfl.

    specialize (HABimpl ltac:(wf_auto2) wfl).

    pose proof (Framing_StructureContext Γ C A B i wfscpred HABimpl) as HFraming.
    toMLGoal; simpl in *.
    + wf_auto2.
    + mlIntro "H0".
      mlApplyMeta HFraming.
      mlApplyMeta HscplugA.
      mlExact "H0".
  Qed.

End Frame.

Tactic Notation "mlFrame" constr(C) :=
  apply (MLGoal_frame _ _ _ _ C); [ try wf_auto2 | try wf_auto2 |].

(* Note: This implementation of unfoldr is for unparametric sorts, the paper uses recursive parametrics sorts
The `unfold_r` lemma will likely need to be restated when we introduce parametric sorts properly.
This should be treated as an expirements for now on unparametric sorts.
*)
Section UnfoldR.
  Context {Σ : Signature} {definedness_syntax : Definedness_Syntax.Syntax}.

  (*
    prefix point:
    φ [ μ X . φ \ X ] -> μ X . φ
  *)
  
  (* layer 1 lemma *)
  Lemma unfold_r
    Γ ψ φ i:
    well_formed (patt_mu ψ) ->
    well_formed φ ->
    Γ ⊢i φ ---> (instantiate (patt_mu ψ) (patt_mu ψ)) using i ->
    Γ ⊢i φ ---> (patt_mu ψ) using i.
  Proof.
    intros.

    assert (Γ ⊢i (instantiate (patt_mu ψ) (patt_mu ψ)) --->
            (patt_mu ψ) using i).
    + useBasicReasoning.
      pose proof (Pre_fixp Γ ψ ltac:(wf_auto2)).
      exact H2.
    + mlIntro "H".
      mlApplyMeta H2.
      mlApplyMeta H1.
      mlExact "H".
  Qed.

  (* layer 2 lemma *)
  Lemma MLGoal_UnfoldR
    Γ φ ψ i :
    well_formed (patt_mu ψ) ->
    well_formed (φ) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> (instantiate (patt_mu ψ) (patt_mu ψ))) i) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> (patt_mu ψ)) i).
  Proof.
    intros wfmu wfphi H.
    unfold of_MLGoal in *. simpl in *.

    intros _ wfl.
    specialize (H ltac:(wf_auto2) wfl).
    apply unfold_r; [wf_auto2 | wf_auto2 |].
    + exact H.
  Qed.
  
End UnfoldR.

Ltac mlChangeConcl p :=
  lazymatch goal with
  | |- @of_MLGoal ?Sg (@mkMLGoal ?Sg ?G ?l _ ?i) =>
      change (@of_MLGoal Sg (@mkMLGoal Sg G l p i))
  end.

Ltac mlUnfoldR H :=
  _ensureProofMode;
  apply (MLGoal_unfoldr_derive_impl _ _ _ _ _ _ (H ltac:(wf_auto2) ltac:(wf_auto2)));
  [wf_auto2 | wf_auto2 | wf_auto2 | wf_auto2 |];
  lazymatch goal with
  | [ |- @of_MLGoal _ (@mkMLGoal _ ?Γ _ (patt_imp ?a ?b) ?i) ] =>
    let b' := eval hnf in b in 
    lazymatch b' with
      | patt_mu ?ψ =>
          mlChangeConcl (patt_imp a (patt_mu ψ));
          apply (MLGoal_UnfoldR Γ a ψ i);
          [ try wf_auto2 | try wf_auto2 |]
      | _ => fail "mlUnfoldr failed (no patt mu)"
    end
  | _ => fail "mlUnfoldR failed"
  end;
  simpl;
  try (mlIntro "Hz"; first [ mlLeft; mlExact "Hz" | mlRight; mlExact "Hz" ]).

Section UnfoldRExamples.

  Context {Σ : Signature} {definedness_syntax : Definedness_Syntax.Syntax} (zero succ: symbols) (Γ : Theory).
  
  (* nat is a recusively defined symbol: (B0) *)
  Definition NatPattern := patt_mu (patt_sym zero or patt_sym succ ⋅ B0).
  
  Example unfoldr_first
    (C: StructureContext) φ i :
    well_formed φ ->
    well_formed (sc_pred C) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> sc_plug C (patt_sym zero)) i) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> sc_plug C (NatPattern)) i).
  Proof.
    intros wfphi wfscpred H.
    mlUnfoldR H.
  Qed.

  Example unfoldr_second
    (C: StructureContext) φ i :
    well_formed φ ->
    well_formed (sc_pred C) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> sc_plug C (patt_sym succ ⋅ NatPattern)) i) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> sc_plug C (NatPattern)) i).
  Proof.
    intros wfphi wfpsi H.
    mlUnfoldR H.
  Qed.

End UnfoldRExamples.

(*
    φ -> ψ
  -------
  ∃x.φ -> ψ
*)
Section ElimExists.
  (* layer 1 lemma: Ex_gen *)

  (* layer 2 lemma *)
  (* maybe we can tighten the proofinfo we use here? *)
  Lemma MLGoal_elim_exists {Σ : Signature}
    Γ φ ψ x:
    well_formed (φ ---> ψ) ->
    x ∉ free_evars ψ ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> ψ) AnyReasoning) ->
    of_MLGoal (mkMLGoal Σ Γ [] (exists_quantify x φ ---> ψ) AnyReasoning).
  Proof.
    intros wfimp Hx H.
    unfold of_MLGoal in *. simpl in *.

    intros _ wfl.

    apply Ex_gen.
    + try_solve_pile.
    + exact Hx.
    + specialize (H wfimp wfl).
      exact H.
  Qed.

End ElimExists.

Tactic Notation "mlElimExists" constr(x) := _ensureProofMode; apply (MLGoal_elim_exists _ _ _ x).

(*
    φ ->  ψ
  -------
    φ -> ∀y.ψ
*)
Section ElimForall.

  Context {Σ : Signature} {definedness_syntax: Definedness_Syntax.Syntax}.

  (* layer 1 lemma: forall_gen *)

  (* layer 2 lemma for elim-∀ *)
  Lemma MLGoal_Elim_Forall
    ψ φ Γ (C : StructureContext) y:
    well_formed (φ ---> contextual_implication C ψ) ->
    y ∉ free_evars φ ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> (contextual_implication C ψ)) AnyReasoning) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> (forall_quantify y (contextual_implication C ψ))) AnyReasoning).
  Proof.
    intros wfimp Hx H.
    unfold of_MLGoal in *. simpl in *.

    intros _ wfl.

    apply (forall_gen Γ φ (contextual_implication C ψ) _ AnyReasoning).
    + unfold evar_is_fresh_in. exact Hx.
    + try_solve_pile.
    + specialize (H wfimp wfl).
      exact H.
  Qed.

End ElimForall.

Tactic Notation "mlElimForall" constr(x) := _ensureProofMode; apply (MLGoal_Elim_Forall _ _ _ _ x); try assumption.

Lemma example_ml_elim_forall_1 {Σ : Signature} {definedness_syntax: Definedness_Syntax.Syntax}
    a b Γ (C : StructureContext) x:
 well_formed a ->
 well_formed (contextual_implication C b) ->
 well_formed (a ---> contextual_implication C b) ->
 well_formed (all, contextual_implication C b) ->
 x ∉ free_evars a ->
 Γ ⊢ a ---> (contextual_implication C b) ->
 Γ ⊢ a ---> (forall_quantify x (contextual_implication C b)).
Proof.
  intros.
  mlElimForall x.
  fromMLGoal.
  exact H4.
Qed.

(* currently stated in the more general form then the paper's version:
   φ -> ∀x.(C ⊸ ψ)
  -------
   φ -> (C ⊸ ψ)
*)
Section IntroForall.

  Context {Σ : Signature} {definedness_syntax: Definedness_Syntax.Syntax}.

  (* maybe TODO: how to express the recursive structure instead of φ + add the sidecondition *)
  Lemma intro_forall
    φ ψ Γ i (C : StructureContext) x :
  well_formed φ ->
  well_formed (contextual_implication C ψ) ->
  Γ ⊢i φ ---> (forall_quantify x (contextual_implication C ψ)) using i ->
  Γ ⊢i φ ---> contextual_implication C ψ using i.
  Proof.
    intros wfphi wfci H.
    assert (HRhs: Γ ⊢i (forall_quantify x (contextual_implication C ψ) --->
           contextual_implication C ψ) using i).
    + useBasicReasoning.
      unfold forall_quantify.
      Check forall_variable_substitution.
      pose proof (Hs := forall_variable_substitution Γ ((contextual_implication C ψ)^{{evar:x↦0}})
        x ltac:(wf_auto2)).
      assert (Heq : (contextual_implication C ψ)^{{evar:x↦0}}^{evar:0↦x} = contextual_implication C ψ).
      - apply evar_open_evar_quantify.
        wf_auto2.
      - rewrite Heq in Hs.
        exact Hs.
    + mlIntro "H".
      mlApplyMeta HRhs.
      mlApplyMeta H.
      mlExact "H".
  Qed.
  
  (* layer 2 lemma for intro-∀ *)
  Lemma MLGoal_Intro_Forall
    ψ φ Γ (C : StructureContext) i x:
    well_formed (φ ---> forall_quantify x (contextual_implication C ψ)) ->
    well_formed φ ->
    well_formed (contextual_implication C ψ) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> (forall_quantify x (contextual_implication C ψ))) i) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> (contextual_implication C ψ)) i).
  Proof.
    intros wfimp wfphi wfctximpl H.
    unfold of_MLGoal in *. simpl in *.

    intros _ wfl.

    specialize (H wfimp wfl).

    apply (intro_forall _ _ _ _ _ x).
    + wf_auto2.
    + wf_auto2.
    + exact H.
  Qed.
  
End IntroForall.

Tactic Notation "mlIntroForall" constr(x) := _ensureProofMode; apply (MLGoal_Intro_Forall _ _ _ _ _ x).

Lemma intro_forall_example1 {Σ : Signature} {definedness_syntax: Definedness_Syntax.Syntax}
  ψ φ Γ (C : StructureContext) x:
  well_formed φ ->
  well_formed (contextual_implication C ψ) ->
  well_formed (φ ---> forall_quantify x (contextual_implication C ψ)) ->
  Γ ⊢ φ ---> forall_quantify x (contextual_implication C ψ) ->
  Γ ⊢ φ ---> contextual_implication C ψ.
Proof.
  intros wfphi wfctximp wfimp2 H. 
  mlIntroForall x.
  + exact wfimp2.
  + exact wfphi.
  + exact wfctximp.
  + fromMLGoal. exact H.
Qed.

(* TODO: after wrap+unwrap: Introduce recursive paramtetric symbols using product sorts so we can state lfp
  to become an actually recursive parametric lemma*)

(* TODO: lfp *)

(* TODO: kt *)
(* KT: sequential composition of wrap, intro-∀, lfp, elim-∀ and unwrap *)
(* sequential compositon ~= applied after each other, building the 'proof tree' upwards *)
(* paper's examples explicitly write the parts instead of an aggregated kt *)
(* maybe we don't need to create any lemmas / tactics here, we can just use the parts after all *)

(* TODO after kt: match-ctx, pm *)

(* TODO after match-ctx + pm: proof search algo *)

(* TODO: for SMT can we use a plain Rocq tactic instead of an actual SMT solver ? *)
(* this might be dependant on how we encode the SL specifics ... *)
(* Rocq tactic for SMT : maybe mlTauto ? *)
