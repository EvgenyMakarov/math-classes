Require Import
  Morphisms RelationClasses Relation_Definitions List
  universal_algebra ua_homomorphisms canonical_names ua_subalgebraT util.
Require ua_products.

Require theory.categories.

(* Remove this *)
Local Hint Transparent Equiv : typeclass_instances.

Section contents.
  Context σ `{@Algebra σ v ve vo}.

  Notation op_type := (op_type (sorts σ)).
  Notation vv := (ua_products.carrier σ bool (λ _: bool, v)).

  Instance hint: Algebra σ vv := @ua_products.product_algebra σ bool (λ _, v) _ _ _.

  (* Given an equivalence on the algebra's carrier that respects its setoid equality... *)

  Instance hint' (a: sorts σ): Equiv (ua_products.carrier σ bool (fun _: bool => v) a).
  Proof. apply setoids.product_equiv. intro. apply _. Defined.

  Context (e: ∀ s, relation (v s)).

  Section for_nice_e.

  Context
    (e_e: ∀ s, Equivalence (e s))
    (e_proper: ∀ s, Proper ((=) ==> (=) ==> iff) (e s)).

  (* We can show that that equivalence lifted to arbitrary operation types still respects the setoid equality: *)

  Let Q s x := e s (x true) (x false).
  Let lifted_e := @op_type_equiv (sorts σ) v e.
  Let lifted_normal := @op_type_equiv (sorts σ) v ve.

  Instance lifted_e_proper o: Proper ((=) ==> (=) ==> iff) (lifted_e o).
  Proof with intuition.
   induction o; simpl. intuition.
   repeat intro.
   unfold respectful.
   split; intros.
    assert (x x1 = y x1). apply H0...
    assert (x0 y1 = y0 y1). apply H1...
    apply (IHo (x x1) (y x1) H4 (x0 y1) (y0 y1) H5)...
   assert (x x1 = y x1). apply H0...
   assert (x0 y1 = y0 y1). apply H1...
   apply (IHo (x x1) (y x1) H4 (x0 y1) (y0 y1) H5)...
  Qed. (* todo: clean up *)

  (* With that out of the way, we show that there are two equivalent ways of stating compatibility with the
   algebra's operations: *)

    (* 1: the direct way with Algebra; *)
  Let eAlgebra := @Algebra σ v e _.

    (* 2: the indirect way of saying that the relation as a set of pairs is a subalgebra in the product algebra: *)
  Let eSub := @ua_subalgebraT.ClosedSubset σ vv _ _ Q.

  Lemma eAlgebra_eSub: eAlgebra → eSub.
  Proof with intuition.
   intros.
   constructor.
    unfold Q.
    repeat intro.
    constructor; intro.
     rewrite <- (H1 true), <- (H1 false)...
    rewrite (H1 true), (H1 false)...
   intro o.
   simpl.
   unfold algebra_op, ua_products.product_ops, algebra_op.
   set (f := λ _: bool, vo o).
   assert (∀ b, Proper (=) (f b)).
    intro.
    unfold f.
    apply algebra_propers.
   assert (lifted_e _ (f true) (f false)). unfold f.
    unfold lifted_e.
    destruct H0.
    apply algebra_propers.
   assert (∀ b, Proper (lifted_e (σ o)) (f b))...
   clearbody f.
   induction (σ o)...
   simpl in *...
   apply IHo0...
   apply H1...
  Qed. (* todo: clean up *)

  Lemma eSub_eAlgebra: eSub → eAlgebra.
  Proof with intuition.
   intros [proper closed].
   constructor. unfold abstract_algebra.Setoid. apply _.
   intro o.
   generalize (closed o). clear closed. (* todo: must be a cleaner way *)
   unfold algebra_op.
   simpl.
   unfold ua_products.product_ops.
   intro.
   change (lifted_e _ (algebra_op o) (algebra_op o)).
   set (f := λ _: bool, algebra_op o) in *.
   assert (∀ b, lifted_normal _ (f b) (f b)). intros.
    subst f. simpl.
    apply algebra_propers...
   change (lifted_e (σ o) (f true) (f false)).
   clearbody f.
   induction (σ o)...
   simpl in *.
   repeat intro.
   unfold respectful in H0.
   apply (IHo0 (λ b, f b (if b then x else y)))...
  Qed. (* todo: clean up *)

  Lemma back_and_forth: iffT eSub eAlgebra.
  Proof. split; intro; [apply eSub_eAlgebra | apply eAlgebra_eSub]; assumption. Qed.

  End for_nice_e.

  (* This justifies the following definition of a congruence: *)

  Class Congruence: Prop :=
    { congruence_proper:> ∀ s: sorts σ, Proper ((=) ==> (=) ==> iff) (e s)
    ; congruence_quotient:> Algebra σ v (e:=e) }.

End contents.

(* A variety for an equational theory none of whose laws have
 premises is closed under quotients generated by congruences: *)

Lemma quotient_variety
  (et: EquationalTheory) `{InVariety et v}
  (e': ∀ s, relation (v s)) `{!Congruence et e'}
  (no_premises: ∀ s, et_laws et s → entailment_premises _ s ≡ nil):
    InVariety et v (e:=e').
      (* Todo: Can this no-premises condition be weakened? Does it occur in this form in the literature? *)
Proof.
 constructor. apply _.
 intros l law vars.
 pose proof (variety_laws l law vars) as E.
 pose proof (no_premises l law).
 destruct l as [prems [conc ?]]. simpl in *. subst. simpl in *.
 unfold equiv. rewrite E.
 pose proof (_: Equivalence (e' conc)).
 reflexivity.
Qed.

Section in_domain.

  Context {A B} {R: Equiv B} (f: A → B).

  Definition in_domain: Equiv A := λ x y, f x = f y. (* todo: use pointwise thingy *)

  Global Instance in_domain_equivalence: Equivalence R → Equivalence in_domain.
  Proof with intuition.
   constructor; repeat intro; unfold equiv, in_domain in *...
   transitivity (f y)...
  Qed.

End in_domain.

Section first_iso.

(* "If A and B are algebras, and f is a homomorphism from A to B, then
 the equivalence relation Φ on A defined by a~b if and only if f(a)=f(b) is
 a congruence on A, and the algebra A/Φ is isomorphic to the image
 of f, which is a subalgebra of B." *)

  Context `{Algebra σ A} `{Algebra σ B} `{!HomoMorphism σ A B f}.

  Notation Φ := (λ s, in_domain (f s)).

  Lemma square o0 x x' y y':
    Preservation σ A B f x x' →
    Preservation σ A B f y y' →
    op_type_equiv (sorts σ) B o0 x' y' →
    @op_type_equiv (sorts σ) A (λ s: sorts σ, @in_domain (A s) (B s) (e0 s) (f s)) o0 x y.
  Proof.
   induction o0.
    simpl.
    intros.
    unfold in_domain.
    rewrite H3, H4.
    assumption.
   simpl in *.
   repeat intro.
   unfold in_domain in H6.
   unfold respectful in H5.
   simpl in *.
   pose proof (H3 x0).
   pose proof (H3 y0). clear H3.
   pose proof (H4 x0).
   pose proof (H4 y0). clear H4.
   apply (IHo0 (x x0) (x' (f _ x0)) (y y0) (y' (f _ y0)) H7 H9).
   apply H5.
   assumption.
  Qed.

  Instance co: Congruence σ Φ.
  Proof with intuition.
   constructor.
    repeat intro.
    unfold in_domain.
    rewrite H3, H4...
   constructor; intro.
    unfold abstract_algebra.Setoid. apply _.
   unfold algebra_op.
   generalize (preserves σ A B f o).
   generalize (@algebra_propers σ B _ _ _ o).
   unfold algebra_op.
   generalize (H o), (H1 o).
   induction (σ o); simpl in *; repeat intro.
    apply _.
   apply (square _ _ _ _ _ (H4 x) (H4 y))...
  Qed.

  Definition image s (b: B s): Type := sigT (λ a, f s a = b).

  Lemma image_proper: ∀ s (x0 x' : B s), x0 = x' → iffT (image s x0) (image s x').
  Proof. intros ??? E. split; intros [v ?]; exists v; rewrite E in *; assumption. Qed.

  Instance: ClosedSubset image.
  Proof with intuition.
   constructor; repeat intro.
    split; intros [q p]; exists q; rewrite p...
   generalize (preserves σ A B f o).
   generalize (@algebra_propers σ B _ _ _ o).
   unfold algebra_op.
   generalize (H1 o), (H o).
   induction (σ o); simpl; intros.
    exists o1...
   destruct X.
   apply (@op_closed_proper σ B _ _ _ image image_proper _ (o1 z) (o1 (f _ x))).
    apply H3...
   apply IHo0 with (o2 x)...
   apply _.
  Qed.

  Definition quot_obj: algebras.Object σ := algebras.object σ A (algebra_equiv:=Φ). (* A/Φ *)
  Definition subobject: algebras.Object σ := algebras.object σ (ua_subalgebraT.carrier image).

  Program Definition back: subobject ⟶ quot_obj := λ _ X, projT1 (projT2 X).

  Next Obligation. Proof with try apply _; intuition.
   repeat constructor...
    intros [x [i E']] [y [j E'']] E.
    change (x = y) in E.
    change (f a i = f a j).
    rewrite E', E''...
   unfold ua_subalgebraT.impl.
   generalize (subset_closed image o).
   unfold algebra_op.
   generalize (H o) (H1 o) (preserves σ A B f o)
     (_: Proper (=) (H o)) (_: Proper (=) (H1 o)).
   induction (σ o); simpl; intros ? ? ? ? ?.
    intros [? E]. change (f _ x = f _ o0). rewrite E...
   intros ? [x [? E]]. apply IHo0... simpl in *. rewrite <- E...
  Defined.

  Program Definition forth: quot_obj ⟶ subobject := 
    λ a X, existT _ (f a X) (existT _ X (reflexivity _)).

  Next Obligation. Proof with try apply _; intuition.
   repeat constructor... intro...
   unfold ua_subalgebraT.impl.
   generalize (subset_closed image o).
   unfold algebra_op.
   generalize (H o) (H1 o) (preserves σ A B f o)
     (_: Proper (=) (H o)) (_: Proper (=) (H1 o)).
   induction (σ o); simpl...
   apply IHo0...
  Qed.

  Theorem first_iso: categories.iso_arrows back forth.
  Proof.
   split. intro. reflexivity.
   intros ? [? [? ?]]. assumption.
  Qed.

End first_iso.
