From MatchingLogic Require Export Sorts_Syntax.
From MatchingLogic Require Nat_Syntax.
Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations
       MatchingLogic.Theories.Sorts_Syntax.Notations.

Set Default Proof Mode "Classic".

Section SeparatonLogic_Syntax.
  Context {Σ : Signature}.

  Inductive Symbols :=
    | sEmp        (* emp *)
    | sPointsTo   (* ↦ *)
    | sSep        (* * *)
    (* TODO 'recursive heap predicate p' ? *)
    .
    
  Global Instance Symbols_eqdec : EqDecision Symbols.
  Proof.
    unfold EqDecision. intros x y. unfold Decision.
    decide equality.
  Defined.
  
  Class Syntax :=
  { sym_inj : Symbols -> symbols;
    imported_sorts : Sorts_Syntax.Syntax;
  }.

  Context {self : Syntax}.
  
  Definition emp : Pattern := patt_sym (sym_inj sEmp).
  Definition pointsTo (x y : Pattern) : Pattern := patt_sym (sym_inj sPointsTo) ⋅ x ⋅ y.
  Definition sep (x y : Pattern) : Pattern := patt_sym (sym_inj sSep) ⋅ x.

End SeparatonLogic_Syntax.

Section SeparatonLogic_Axioms.
  Context
    {Σ : Signature}
    {syntax : Syntax}
     {definedness_syntax : Definedness_Syntax.Syntax}
     {nat_syntax : Nat_Syntax.Syntax}
  .
  
  Inductive AxiomName :=
  | AxSlAssoc               (* h1 * (h2 * h3) = (h1 * h2) * h3 *)
  | AxSlComm                (* h1 * h2 = h2 * h1  *)
  | AxSlEmpty               (* emp * h = h *)
  | AxSlPointsToNonNil      (* x ↦ y → x ≠ nil *)
  | AxSlPointsToDisjoint    (* x₁ ↦ y * x₂ ↦ z -> x₁ ≠ x₂ *)
  (* last axiom ? *)
  .
  
  Definition axiom (name : AxiomName) : Pattern :=
  match name with
  | AxSlAssoc => all, all, all, (sep (b0) (sep (b1) (b2))) =ml (sep (sep (b0) (b1)) (b2))
  | AxSlComm => all, all, (sep b0 b1) =ml (sep b1 b0)
  | AxSlEmpty => all, (sep emp b0) =ml b0
  | AxSlPointsToNonNil => all, all, (pointsTo b0 b1) ---> ! (b0 =ml Nat_Syntax.Zero) (* maybe separate nil symbol instead of Zero? *)
  | AxSlPointsToDisjoint => all, all, all, all, (sep (pointsTo b0 b2) (pointsTo b1 b3)) ---> ! (b0 =ml b1)
  end.
  
  Program Definition named_axioms : NamedAxioms :=
    {|
      NAName := AxiomName;
      NAAxiom := axiom;
    |}.
  Next Obligation.
    destruct name; simpl; wf_auto2.
  Qed.

  Definition theory := Definedness_Syntax.theory ∪ theory_of_NamedAxioms named_axioms.

End SeparatonLogic_Axioms.
