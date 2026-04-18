(*# Formulas, countability and ordering #*)
(*; Here, we define first-order formulae and prove that they are countable.
    We additionally define an ordering over first-order formulae via weight. ;*)

From stdpp Require Export countable strings. (* Countability from stdpp *)

(*## Terms and formulae ##*)

(*; We first define the terms and formulae of our language: ;*)
Inductive term :=                     (*= Terms =*)(*; We define terms inductively as: :*)
| var : nat -> term                   (*: - **Variables:** $x_i$ is a term for $i \in \nat$ :*)
| const : nat -> term                 (*: - **Constants:** $k_i$ is a term for $i \in \nat$ :*)
| func : nat -> term -> term -> term. (*: - **Functions:** $f_i(t_1, t_2)$ is a term for $i \in \nat$ and terms $t_1, t_2$ ;*)

Inductive form :=                 (*= Formula =*)(*; We define formulae inductively as: :*)
| Atom : nat -> list term -> form (*: - **Atomic formulae:** $P_i(t_0, t_1, \dots)$ is a formula for terms $t_j$ :*)
| Bot : form                      (*: - **Bottom formula:** $\bot$ is a formula :*)
| And : form  -> form -> form     (*: - **And:** $A \land B$ is a formula for formulae $A$ and $B$ :*)
| Or : form -> form -> form       (*: - **Or:** $A \lor B$ is a formula for formulae $A$ and $B$ :*)
| Implies : form -> form -> form  (*: - **Implies:** $A \to B$ is a formula for formulae $A$ and $B$ :*)
| ForAll : form -> form           (*: - **For all:** $\forall A$ is a formula for a formula $A$ :*)
| Exists : form -> form.          (*: - **Exists:** $\exists A$ is a formula for a formula $A$ ;*)

(*; We will be using De Bruijn indicies for bound variables. Usually bound variables
    can be relabelled to provide different representations of the same formula. As
    an example while $\forall x \; P(x)$ and $\forall y\; P(y)$ are clearly the same,
    they are represented with different strings. De Bruijn indicies avoids this issue. ;*)

(*! De Bruijn Indicies !*)
(*; De Bruijn indicies refer to bound variables by the scope depth
    (i.e. how many $\forall$'s deep the bound variable is).

    \input{debruijn}

    So our previous $\forall x\; P(x)$ will be written as $\forall P(0)$. However, in
    our formalism, we will write this as $\forall P_0(x_0)$. Thus the above formula would
    be written as: $$\forall (((\forall P_0(x_0)) \lor \forall P_1(x_0)) \land \forall P_2(x_1, x_0))$$ ;*)

(*; As it is cumbersome to write $P_0, P_1, \dots$, we will often mix the notations and
    use ordinary notation (i.e. $P, Q, R, \dots$) for everything but quantifiers and
    variables. Thus we write $\forall x\; P(x)$ as $\forall\; P(x_0)$ (instead of using $P_0$). ;*)

(*< De Bruijn Indicies >*)
(*; We provide some examples for encoding the usual notation (non De Bruijn) to De Bruijn.
    In the following examples we will reserve $a_i$ for unbound variables and $x, y, z$ for the
    bound variables in the usual notation: :*)
(*: - $\forall x\; P(f(x, k))$ is encoded as $\forall P(f(x_0, k))$ :*)
(*: - $\forall x\;(P(x) \lor \forall y\; (Q(a_3) \lor R(y)))$ is encoded as $\forall (P(x_0) \lor \forall (Q(x_3) \lor R(x_0)))$  :*)
(*: - $\forall x\; P(a_1)$ is encoded as $\forall P(x_1)$ and $\forall x\; P(a_2)$ is encoded as $\forall P(x_2)$ ;*)


(** Pretty notations for formulas **)
Notation "¬ φ" := (Implies φ Bot) (at level 75, φ at level 75).
Notation " ⊥ " := Bot.
Notation " ⊤ " := (Implies Bot Bot).
Notation " A ∧ B" := (And A B) (at level 80, B at level 80).
Notation " A ∨ B" := (Or A B) (at level 85, B at level 85).
Notation " A → B" := (Implies A B) (at level 99, B at level 200).
Notation " ∀ A" := (ForAll A) (at level 200, right associativity).
Notation " ∃ A" := (Exists A) (at level 200, right associativity).
Infix " φ ⇔ ψ " := (And (Implies φ ψ) (Implies ψ φ)) (at level 100).

Global Instance formula_bottom : base.Bottom form := ⊥.
Global Instance form_top : base.Top form := ⊤.

Ltac solve_trivial_decision :=
  match goal with
  | |- Decision (?P) => apply _
  | |- sumbool ?P (¬?P) => change (Decision P); apply _
  end.

Ltac solve_decision :=
  unfold EqDecision; intros;
  first [ solve_trivial_decision | unfold Decision; decide equality; solve_trivial_decision ].

(*### Countability of terms and formulae ###*)

(*; We trivially obtain decidable equality for terms and formulae.
    This is from terms and formulae containing naturals which have
    decidabile equality. ;*)

(*{ Terms have decidable equality. }*)
(*; $\forall t, s \in \term \; ( t = s \lor t \neq s)$ ;*)
Global Instance term_eq_dec : EqDecision term.
(*; Trivial from decidable equality of naturals ;*)
Proof. unfold EqDecision. unfold Decision. solve_decision. Defined.

(*{ Formulae have decidable equality. }*)
(*; \\$\forall \varphi, \psi \in \form \; ( \varphi = \psi \lor \varphi \neq \psi$ ;*)
Global Instance form_eq_dec : EqDecision form.
(*; Trivial from decidable equality of terms ;*)
Proof. solve_decision. Defined.

(*## Countability of formulae ##*)
Section CountablyManyFormulas.
  (*; To prove the countability of terms and formulae,
      we convert terns into a tree labelled with natural numbers.
      We will assume that labelled trees are countable (i.e. Prüfer sequences).  ;*)

  (*; We use the following encoding for terms: ;*)
  (*= Term to labelled tree =*)
  Local Fixpoint term_to_gen_tree (t : term) : gen_tree nat :=
    (*; Given a term $t$ we encode it into a tree where: :*)
    match t with
    (*: - **Variables:** $x_i$ to nodes labelled 0, with a single leaf labelled $i$ :*)
    | var i => GenNode 0 [GenLeaf i]
    (*: - **Constants:** $k_i$ to nodes labelled 1, with a single leaf labelled $i$ :*)
    | const i => GenNode 1 [GenLeaf i]
    (*: - **Functions:** $f_i(t_1, t_2)$ into a node labelled 2, with three branches: :*)
    | func i t1 t2 => GenNode 2 [              
                          GenLeaf i;           (*:   - One branch has a leaf labelled $i$ :*)
                          term_to_gen_tree t1; (*:   - Another branch is the tree for $t_1$ :*)
                          term_to_gen_tree t2] (*:   - Another branch is the tree for $t_2$ ;*)
    end.

  (*; We can similarly specify a decoding procedure which does the reverse ;*)
  Local Fixpoint gen_tree_to_term (t : gen_tree nat) : option term :=
    match t with
    | GenNode 0 [ GenLeaf k ] => Some (var k)
    | GenNode 1 [ GenLeaf k ] => Some (const k)
    | GenNode 2 [ GenLeaf k ; t1 ; t2 ] =>
        gen_tree_to_term t1 ≫= fun x => gen_tree_to_term t2 ≫= fun y => Some (func k x y)
    | _ => None
    end.

  (*{ Terms are countable }*)
  (*; $\term \xhookrightarrow{} \nat$ ;*)
  Global Instance term_count : Countable term.
  Proof.
    (*; Our encoding and decoding procedure proves an injection to the set of
        labelled trees. We know labelled trees are countable. ;*)
    eapply inj_countable with (f := term_to_gen_tree) (g := gen_tree_to_term); intros.
    induction x; simpl; try (rewrite IHx1, IHx2); easy.
  Defined.

  (*; Since we have defined atoms in the form $P_i(t_0, t_1, \dots, t_n)$ we can
      encode them as the product $\atom = \nat \times \term^n$.
      Thus we only need to prove the latter is countable. ;*)
  
  (*{ Atoms are countable }*)
  (*; $\atom \xhookrightarrow{} \nat$ ;*)
  Global Instance atom_count : Countable (nat * list term).
  Proof.
    (*; Trivial from countability of terms ;*)
    apply prod_countable.
  Defined.
  
  (*; From the countability of terms and atoms, we obtain the function:
      $E_{\atom} : \atom \to \nat$,
      which encodes atoms into naturals.

      There are many  efficient and elegant encodings, however the following suffices: ;*)

  Local Fixpoint form_to_gen_tree (φ : form) : gen_tree nat := (*= Formula to labelled tree =*)
    (*; Given a formula $\varphi$ we encode it into a tree where: :*)
    match φ with
    (*: - Atoms to nodes labelled 0 with a leaf labelled with the $E_{\atom}$ value. :*)
    | Atom i xs => GenNode 0 [ GenLeaf (encode_nat ( i, xs )) ]
    (*: - $\bot$ to nodes labelled 1 without any leaves :*)
    | ⊥ => GenNode 1 []
    (*: - $A \land B$ to nodes labelled 2 with branches to A and B's tree :*) 
    | φ ∧ ψ => GenNode 2 [form_to_gen_tree φ ; form_to_gen_tree ψ]
    (*: - $A \lor B$ to nodes labelled 3 with branches to A and B's tree :*)
    | φ ∨ ψ => GenNode 3 [form_to_gen_tree φ ; form_to_gen_tree ψ]
    (*: - $A \to B$ to nodes labelled 4 with branches to A and B's tree :*)
    | φ →  ψ => GenNode 4 [form_to_gen_tree φ ; form_to_gen_tree ψ]
    (*: - $\forall A$ to nodes labelled 5 with a branch to A's tree :*)
    | ForAll ψ => GenNode 5 [form_to_gen_tree ψ]
    (*: - $\forall A$ to nodes labelled 6 with a branch to A's tree ;*)
    | Exists ψ => GenNode 6 [form_to_gen_tree ψ]
    end.

  (*; Again we can similarly obtain a decoding procedure. ;*)
  Local Fixpoint gen_tree_to_form (t : gen_tree nat) : option form :=
    match t with
    | GenNode 0 [ GenLeaf n ] =>
        decode_nat n ≫= fun arg => Some (Atom (fst arg) (snd arg))
    | GenNode 1 [] => Some ⊥
    | GenNode 2 [t1 ; t2] =>
        gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2≫= fun ψ => Some (φ ∧ ψ)
    | GenNode 3 [t1 ; t2] =>
        gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2 ≫= fun ψ => Some (φ ∨ ψ)
    | GenNode 4 [t1 ; t2] =>
        gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2 ≫= fun ψ => Some (φ →  ψ)
    | GenNode 5 [t1] => 
        gen_tree_to_form t1 ≫= fun φ => Some (ForAll φ)
    | GenNode 6 [t1] => 
        gen_tree_to_form t1 ≫= fun φ => Some (Exists φ)
    | _=> None
    end.

  (*{ Formulae are countable }*)
  (*; $\form \xhookrightarrow{} \nat$ ;*)
  Global Instance form_count : Countable form.
  Proof.
    (*; We again exhibit an injection from formulae to the naturals. :*)
    eapply inj_countable with (f := form_to_gen_tree) (g := gen_tree_to_form).
    (*: This follows from the encoding procedure and decoding procedure. ;*)
    intro φ; induction φ; cbn; trivial;
    now rewrite decode_encode_nat || rewrite IHφ1, IHφ2 || rewrite IHφ.
  Defined.
End CountablyManyFormulas.

(*## Weight of formulae ##*)

(*; Here we define the weight function on formulas, following (Dyckhoff Negri 2000) ;*)
Fixpoint weight (φ : form) : nat := (*= Weight of a formula =*)
  (*; We define the weight of a formula $w(\varphi)$ as: :*)
  match φ with
  | Atom _ _ => 1                     (*: - $w(P_i(t_1, \dots)) = 1$ :*)
  | ⊥ => 1                           (*: - $w(\bot) = 1$ :*)
  | φ → ψ => 1 + weight φ + weight ψ (*: - $w(\varphi \to \psi) = 1 + w(\varphi) + w(\psi)$ :*)
  | φ ∧ ψ => 2 + weight φ + weight ψ (*: - $w(\varphi \land \psi) = 2 + w(\varphi) + w(\psi)$ :*)
  | φ ∨ ψ => 3 + weight φ + weight ψ (*: - $w(\varphi \lor \psi) = 3 + w(\varphi) + w(\psi)$ :*)
  | ForAll φ => 1 + weight φ          (*: - $w(\forall \varphi) = 1 + w(\varphi)$ :*)
  | Exists φ => 2 + weight φ          (*: - $w(\exists \varphi) = 2 + w(\varphi)$ ;*)
  end.

Lemma weight_pos φ : weight φ > 0. (*{ Positivity of weight }*)(*; $w(\varphi) > 0$ ;*)
Proof. induction φ; simpl; lia. Qed. (*; Trivial by definition ;*)

(*; We can obtain a transitive and irreflexive order over formulae. ;*)
Definition form_order φ ψ := weight φ > weight ψ.

Global Instance transitive_form_order : Transitive form_order.
Proof. unfold form_order. auto with *. Qed.

Global Instance irreflexive_form_order : Irreflexive form_order.
Proof. unfold form_order. intros x y. lia. Qed.

Notation "φ ≺f ψ" := (form_order ψ φ) (at level 149).

Fixpoint occurs_in_term i t :=
  match t with
  | var i => i = i
  | const i => False
  | func i x y => or (occurs_in_term i x) (occurs_in_term i y)
  end.

Fixpoint occurs_in_form i φ :=
  match φ with
  | Atom j xs => (fold_left (fun acc t => or (occurs_in_term i t) acc) xs False)
  | Bot => False
  | And φ1 φ2 => or (occurs_in_form i φ1) (occurs_in_form i φ2)
  | Or φ1 φ2 => or (occurs_in_form i φ1) (occurs_in_form i φ2)
  | Implies φ1 φ2 => or (occurs_in_form i φ1) (occurs_in_form i φ2)
  | ForAll φ1 => occurs_in_form i φ1
  | Exists φ1 => occurs_in_form i φ1
  end.

