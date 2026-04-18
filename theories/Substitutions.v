(*# Substitutions #*)
(*; Here we define a theory of substitutions for De Bruijn indices.
    We define substitutions over terms & formulae, and specify several
    properties and identities regarding them. ;*)
From Stdlib Require Import FinFun. (* Injectivity from FinFun *)
From Stdlib Require Import FunctionalExtensionality.
Require Import stdpp.fin_maps. (* map_compose from fin_maps *)
Require Import G4i.Formulas.

(*## Term substitutions ##*)

(*; We restrict our attention to substitutions of variables for terms.
    Since our variables are only indexed by natural numbers, our
    \textbf{substitutions} will be defined as functions $\sigma : \nat \to \term$ ;*)

Fixpoint subst_term (σ : nat -> term) (t : term) := (*= Term substitutions =*)
  (*; We denote a term substitution $t [ \sigma ]$ where: :*)
  match t with
  (*: - **Variables:** $x_i [ \sigma ] = \sigma(i)$ :*) 
  | var i => (σ i)
  (*: - **Constants:** $k_i [ \sigma ] = k_i$ :*)
  | const i => const i
  (*: - **Functions:** $(f_i(t_1, t_2)) [\sigma] = f_i(t_1[\sigma], t_2[\sigma])$ ;*)
  | func i x y => func i (subst_term σ x) (subst_term σ y)
  end.

(*= Term substitution composition notation =*)
(*; We define $(\sigma \odot \tau)(n) = \tau(n)[\sigma]$ as the substitution composition ;*)
Notation "σ ☉ τ" := (λ x, subst_term σ (τ x)) (at level 50, left associativity).

(*= Basic term substitutions =*)
(*; The following term substitutions will be used often: :*)
(*: - *Shifting:* $S'(i) = x_{i + 1}$ (often denoted $\uparrow$). :*)
Definition S' (n : nat) := var (S n).
(*: - *Identity:* $\id(n) = x_i$. ;*)
Notation id' := var.

(*; Additional to these, the following provides a way to extend
    substitutions. Since substitutions are defined as functions $\nat \to \term$.
    We can interpret these as sequences or stream (i.e. $(\sigma(0), \sigma(1), \dots)$).
    A natural operation to apply to such a sequence would be "appending"
    to the beginning. The following substitution is the equivalent to this: ;*)

Definition scons (t : term) (σ : nat -> term) (n : nat) := (*= Stream Constructor =*)
  (*; Given a term $t$ and a variable substitution $\sigma$, we define $\cons(t, \sigma)(n)$ where: :*)
  match n with
  (*: - $\cons(t, \sigma)(0) = t$ :*)
  | 0 => t
  (*: - $\cons(t, \sigma)(n + 1) = \sigma(n)$ ;*)
  | S n => σ n
  end.

(*; We will occasionally use the sequence notation to describe substitutions when
    convinent (e.g. $S' = (x_1, x_2, \dots)$ or $\cons(t, \sigma) = (t, \sigma(0), \sigma(1), \dots)$). ;*)

(*; In the following section we will determine several basic identities.
    Many of these proofs will be rather routine cases of induction.
    As such we will provide the first handful of them, and later only
    provide details for notable cases. ;*)

Lemma subst_term_ident_pt t : (*[ Identity for term substitutions ]*)
  (*; $t[\id] = t$ ;*)
  subst_term var t = t. 
Proof.
  (*; Induction on $t$: :*)
  (*: - **Base case ($t = x_n$):**
        - $x_n[\id] = x_n$ is trivial.
        - $k_n[\id] = k_n$ is trivial.
      - **Assumption:** $t_1[\id] = t_1$ and $t_2[\id] = t_2$
      - **Inductive case:** $f_i(t_1,t_2)[\id] = f_i(t_1[\id],t_2[\id]) = f_i(t_1, t_2)$ ;*)
  induction t; try (simpl; rewrite IHt1, IHt2); try easy.
Qed.

Lemma subst_term_ident : subst_term var = (λ i, i).
Proof. apply functional_extensionality; apply subst_term_ident_pt. Qed.

Lemma subst_term_compose_pt f g t : (*[ Composition for term substitutions ]*)
  (*; $(t[g])[f] = t[f \odot g]$ ;*)
  subst_term f (subst_term g t) = subst_term (f ☉ g) t.
Proof.
  (*; Induction on $t$: :*)
  (*: - **Base case ($t = x_n$):**
        - $x_n[g][f] = x_n[f \odot g]$ is trivial.
        - $k_n[g][f] = k_n[f \odot g]$ is trivial.
      - **Assumption:** $t_1[g][f] = t_1[f \odot g]$ and $t_2[g][f] = t_2[f \odot g]$
      - **Inductive case:** We apply our inductive hypothesis:
        \begin{align*}
          f_i(t_1,t_2)[g][f] &= f_i(t_1[g][f],t_2[g][f]) \\
                             &= f_i(t_1[f \odot g], t_2[f \odot g])
        \end{align*} This provides the equality. ;*)
  induction t; try (simpl; rewrite IHt1, IHt2); try easy.
Qed.

Lemma subst_term_compose f g : f ☉ (subst_term g) = subst_term (f ☉ g).
Proof. apply functional_extensionality; apply subst_term_compose_pt. Qed.

Lemma subst_term_compose' f g : (subst_term f) ∘ (subst_term g) = subst_term (f ☉ g).
Proof. apply functional_extensionality; apply subst_term_compose_pt. Qed.

(*## Formula substitutions ##*)

(*; The majority of this section will devoted to discussing
    the variable binding substitution and proving several properties for it.
    Naturally these properties will be used heavily when dealing with
    quantifiers with bindings. ;*)

(*= Bind variable $x_0$ =*)
(*; We define $B(t) = \cons(t, \id)$ which binds $x_0$ to a term $t$.
    This is because the outermost variable under De Bruijn notation will be $x_0$ ;*)
Definition bind_var t := (scons t var).

(*; This is conventionally written as $(x_0 := t)$ or $t/x_0$. We will use former in some
    sections where this notation is preferable, however, when manipulating the
    substitution itself, we will use $B(t)$. ;*)

(*; It should be noted that this definition $\cons(t, \id)$ decrements variables.
    We can see this when it is expressed as the sequence $( t, x_0, x_1, x_2, x_3, \dots )$.
    It follows that $\cons(x_0, \id)(i)$ is the variable predecessor $\pred'(i) = x_{i - 1}$.
    We see $\cons(t, \id)$ is the left inverse of the variable successor (or shift)
    (i.e. $\cons(t, \id) \odot S' = B(t) \odot S' = \id$). ;*)

(*= Predecessor substitution =*)
(*; We define the predecessor substitution as: $\pred'(n) = x_{n-1}$ ;*)
Notation pred' := (bind_var (var 0)).

(*; Since our formulae involve binders, we must be careful of *variable capture*.
    *Variable capture* is an undesirable substitution that modifies the
    semantics of the original formula. ;*)

(*< Variable capture >*)
(*; Consider the following example with a "naive" substitution:
    $$ (\forall x\; P(x,y)) [y := x] = \forall x\; P(x, x) $$
    Here the semantics of the sentence has been modified by the
    substitution and the variable in the replacement (i.e. $\forall x\; P(x,\mathbf{x})$) has been "captured" by
    the binder ;*)

(*; We avoid this by transforming the substitution in a way that prevents capture.
    This transform is usually referred to as a lifting, denoted with $\up$: ;*)

(*= Lifting =*)
(*; We define lifting as: $\up(\sigma) = \cons(x_0, S' \odot \sigma)$ ;*)
Definition up (σ : nat -> term) :=
  (scons (var 0) (S' ☉ σ)).
Notation "⇑" := up.

(*; This allows us to define a capture-avoiding substitution. ;*)

Fixpoint subst_form (σ : nat -> term) (φ : form) := (*= Formula substitution =*)
  (*; We denote a term substitution $\varphi [ \sigma ]$ where: :*)
  match φ with
  (*: - **Atoms:** $(P_i(t_1, \dots, t_n))[ \sigma ] = P_i(t_1[ \sigma ], \dots, t_n[ \sigma ])$ :*) 
  | Atom i xs => Atom i (map (subst_term σ) xs)
  (*: - **Bottom:** $\bot [ \sigma ] = \bot$ :*) 
  | Bot => Bot
  (*: - **And:** $(\varphi \land \psi)[ \sigma ] = \varphi[\sigma] \land \psi[\sigma]$ :*)
  | And φ ψ => And (subst_form σ φ) (subst_form σ ψ)
  (*: - **Or:** $(\varphi \lor \psi)[ \sigma ] = \varphi[\sigma] \lor \psi[\sigma]$ :*)
  | Or φ ψ  => Or (subst_form σ φ) (subst_form σ ψ)
  (*: - **Implies:** $(\varphi \to \psi)[ \sigma ] = \varphi[\sigma] \to \psi[\sigma]$ :*)
  | Implies φ ψ  => Implies (subst_form σ φ) (subst_form σ ψ)
  (*: - **For all:** $(\forall\;\varphi)[ \sigma ] = \forall\;(\varphi[\up(\sigma)])$ :*)
  | ForAll φ => ForAll (subst_form (up σ) φ)
  (*: - **Exists:** $(\exists\;\varphi)[ \sigma ] = \exists\;(\varphi[\up(\sigma)])$ ;*)
  | Exists φ => Exists (subst_form (up σ) φ)
  end.
Notation "φ 〔 σ 〕" := (subst_form σ φ) (at level 7, left associativity).

(*< Capture-avoiding substitution >*)
(*; Consider the previous example but with the capture-avoiding substitution.
    Firstly suppose our formula is encoded as $\forall P(x_0, x_1)$, and our
    substitution $(y := x)$ may be encoded as $\sigma = (x_1, x_1, x_3, x_4, \dots)$.
    Then the lift of $\sigma$ is: $\up(\sigma) = (x_0, x_2, x_2, x_3, \dots)$,
    so our substition becomes:
    $$ (\forall P(x_0, x_1)) [\sigma] = \forall\; P(x_0[\up(\sigma)], x_1[\up(\sigma)])
                                      = \forall\; P(x_0, x_2)$$  ;*)

(*; One final substitution that should be defined, as it will become
    crucial in a later proof regarding relabelling variables in sequents
    is the following: ;*)

(*= Swap substitution =*) 
(*; We define the swap substitution as $\swap = \cons(x_1, \up(S'))$ ;*)
Definition swap := (scons (var 1) (up S')).

(*; Many of the proofs regarding substitutions will be done by cases or
    induction. As an example consider this basic lemma about $\swap$ ;*)

(*{ Swap and $\up(S')$ is the successor }*)
(*; $S' = \swap \odot \up(S')$ ;*)
Lemma swap_up_succ : S' = swap ☉ (up S').
Proof.
  (*; Cases on $0$ and $n+1$. The base case is trivial.

      For $n+1$, we must show $S'(n+1) = \up(S)(n)[\swap]$ which follows from:
      \begin{align*}
        \up(S')(n+1)[\swap] &= \cons(x_0, S' \odot S')(n+1)[\swap] \\
                                 &= x_{n+2}[\swap] = x_{n+2}
      \end{align*} ;*)
  apply functional_extensionality; intros; destruct x; easy.
Qed.

(*; We now continue with our definition for substitution on formulae ;*)

(*< Capture-avoiding substitution with binding >*)
(*; In our formalism, we will use $B(t)$ for binding. As such a more
    appropriate way to describe our previous example is the following:
    \begin{align*}
      (\forall\; P(x_0, x_1)) [ B(t) ]
         &= \forall\; \left( P(x_0, x_1) [ \up(B(t)) ] \right) \\
         &= \forall\; \left( P(x_0, x_1) [ \cons(x_0, S' \odot B(t)) ] \right) \\
         &= \forall\; \left( P(x_0, t[S'] \right)
    \end{align*}
    Notice, that setting $t = x_0$ gives us the example from the variable
    capture example, however, this time we can see $S'$ makes capture impossible. ;*)

(*; We will need to lift an arbitrary number of times to prove basic properties
    of formulae substitutions. As such we define the $n$-lifting: ;*)
Fixpoint upN (n : nat) (σ : nat -> term):= (*= $n$-lifting =*)
  (*; We define $\up^n(\sigma)$ inductively: :*)
  match n with
  (*: - $\up^0(\sigma) = \sigma$ :*)
  | 0 => σ
  (*: - $\up^{n + 1}(\sigma) = \up( \up^n(\sigma))$ ;*)
  | S n => up (upN n σ)
  end.

(*; As earlier, the two fundamental properties we need are identity and composition: ;*)

Lemma upN_ident_pt i : (*[ Identity for lifting ]*)
  (*; $\forall n\;(\up^n(\id) = \id)$ ;*)
  forall n, upN n var i = var i.
Proof.
  (*; Rewrite as $\forall n\; \up^n(\id)(i) = \id(i)$, then cases on $i$ :*)
  induction i.
  (*: - **Base case ($i = 0$):** We apply cases on $n$:
        - **Case 1:** $\up^0(\id)(0) = \id(0)$ trivially.
        - **Case 2:** $\up^{n + 1}(\id)(0) = \id(0)$ trivially. :*)
  - destruct n; easy.
  (*: - **Assumption:** $\up^n(\id)(i) = \id(i)$ :*)
  (*: - **Inductive case:** We again apply cases on $n$:
        - **Case 1:** $\up^0(\id)(i + 1) = \id(i + 1)$ trivially.
        - **Case 2:** We will need the induction hypothesis:
          \begin{align*}
            \up^{n + 1}(\id)(i + 1) &=\; \up ( \up^{n}(\id)(i + 1)) \\
            \cons(0, S' \odot \up^{n}(\id))(i + 1) &=\; \up^{n}(\id)[S'] \\
            \id(i)[S'] &= \id(i + 1) \quad \text{(by assumption)}
          \end{align*} ;*)
  - destruct n; simpl; try rewrite IHi; easy.
Qed.

Lemma upN_ident n : upN n (var) = (var).
Proof. apply functional_extensionality; intros. apply upN_ident_pt. Qed.

Lemma up_ident_pt i :  up var i = var i.
Proof. apply (upN_ident_pt i 1). Qed.

Lemma up_ident : up (var) = (var).
Proof. apply functional_extensionality; intros. apply up_ident_pt. Qed.

Lemma upN_compose_pt (f g : nat -> term) i : (*[ Composition for lifting ]*)
  (*; $\forall n\;(\up^n(g)(i)[ \up^n(f) ] =\;\up^n(f \odot g)(i)$ ;*)
  forall n, subst_term (upN n f) (upN n g i) = upN n (f ☉ g) i.
Proof.
  (*; We can prove this by induction on $i$: :*)
  induction i.
    (*: - **Base case ($i = 0$):** We prove this with cases on $n$: 
        $$(\up^n(g)(0))[ \up^n(f) ] =\;\up^n(f \odot g)(0)$$ :*)
    (*:   - **Case 1:** Both sides simplify to $g(0)[f]$. :*)
    (*:   - **Case 2:** Since $\up^{n + 1}(\sigma)(0) = x_0$, both sides simplify to $x_0$. :*)
  - destruct n; easy.
    (*: - **Assumption:** $\forall n (\up^n(g)(i))[ \up^n(f) ] =\;\up^n(f \odot g)(i)$ :*)
    (*: - **Inductive case:**
          Similar to the base case, we do cases over $n$:
          $$(\up^n(g)(i+1))[ \up^n(f) ] = \up^n(f \odot g)(i+1)$$ :*)
  - destruct n.
    (*:   - **Case 1:** Both sides simplify to $g(i + 1)[f]$. :*)
    + easy.
    (*:   - **Case 2:** In general for any $h$, we can show:
              \begin{align*}
                \up^{n+1}(h)(i+1) &= \up(\up^{n}(h))(i+1) \\
                                       &= \cons(x_0, S' \odot \up^n(h))(i+1) \\
                                       &= \up^n(h)(i)[S']
              \end{align*}
              Thus we can rewrite our expression:
              \begin{align*}
                \up^{n + 1}(g)(i + 1)[\up^{n + 1}(f)] &=\;\up^{n + 1}(f \odot g)(i + 1)\\
                \up^{n}(g)(i)[S'][ \up^{n + 1}(f) ] &=\;\up^{n}(f \odot g)(i)[S']
              \end{align*} :*)
    + simpl.
      (*:     We use the assumption on the right, then the composition lemma: 
              \begin{align*}
                \up^{n}(g)(i)[S'][ \up^{n + 1}(f) ] &=\;\up^{n}(g)(i)[\up^n(f)][S'] \\
                \up^{n}(g)(i)[\up^{n+1}(f)\odot S'] &=\;\up^{n}(g)(i)[S'\odot\up^n(f)]
              \end{align*} :*)
      rewrite <- IHi, !subst_term_compose_pt.
      (*:     Finally, we notice $\up^{n + 1}(f) \odot S' = S' \odot \up^n(f)$ ;*)
      easy.
Qed.

Lemma upN_compose f g n : (upN n f) ☉ (upN n g) = upN n (f ☉ g).
Proof. apply functional_extensionality; intros; apply upN_compose_pt. Qed.

Lemma up_compose_pt (f g : nat -> term) i :  subst_term (up f) (up g i) = up (f ☉ g) i.
Proof. apply (upN_compose_pt f g i 1). Qed.

Lemma up_compose f g : (up f) ☉ (up g) = up (f ☉ g).
Proof. apply functional_extensionality; intros; apply up_compose_pt. Qed.

(* Shouldn't have to prove this... *)
Lemma map_ident {T} (l: list T) : map (fun x => x) l = l.
Proof. induction l; try (simpl; rewrite IHl); easy. Qed.

Lemma var_eta : (fun x => var x) = var.
Proof. easy. Qed.

Hint Rewrite var_eta.

(*; To prove substitution on formulae, we prove it generally on
    substitutions on $\up^n$. This is useful for the inductive case. ;*)

(*{ Identity for formula substitutions }*)
(*; $\forall n\; \varphi[\up^n(\id)] = \varphi$ ;*)
Lemma subst_form_upN_ident_pt φ : forall n,
    (subst_form (upN n var) φ) = φ.
Proof.
  (*; The proof is similar to the proof for composition. ;*)
  induction φ; intros; simpl;
    try (f_equal; rewrite <- map_ident, <- subst_term_ident, upN_ident);
    try (rewrite IHφ1, IHφ2);
    try (f_equal; apply (IHφ (S n))).
Qed.

Lemma subst_form_ident_pt φ : (subst_form var φ) = φ.
Proof. apply (subst_form_upN_ident_pt φ 0). Qed.

Lemma subst_form_ident : (subst_form var) = (λ i, i).
Proof. apply functional_extensionality; apply subst_form_ident_pt. Qed.

(*[ Composition of formula substitution ]*)
(*; \\$\forall n\; ( \varphi[\up^n(g)][\up^n(f)] = \varphi[\up^n(f \odot g)]$ ;*)
Lemma subst_form_upN_compose_pt (f g : nat -> term) φ: forall n,
    subst_form (upN n f) (subst_form (upN n g) φ) = subst_form (upN n (f ☉ g)) φ.
Proof.
  (*; We prove by induction on $\varphi$. :*)
  induction φ; intros; simpl;
    (*: - **Case for atomic formulae:** We have:
          $$P(t_i)[\up^n(g)][\up^n(f)] = P(t_i)[\up^n(f \odot g)]$$
          We reduce both sides to:
          $t_i[\up^n(g)][\up^n(f)] = t_i[\up^n(f \odot g)]$
          Then by composition for term substitutions and $\up$, we obtain an equality. :*)
    try (f_equal; rewrite map_map, subst_term_compose; rewrite upN_compose);
    (*: - **Case for non-quantifiers**: This is routine :*)
    try (rewrite IHφ1, IHφ2);
    (*: - **Assumption:** $\forall n\; ( \varphi[\up^n(g)][\up^n(f)] =
                                      \varphi[\up^n(f \odot g)])$ :*)
    (*: - **Case for quantifiers:** The definition of capture-avoiding substitution
          introduces an additional lift, so we have:
          $$\forall ( \varphi [ \up(\up^n(g))] [ \up(\up^n(f))] =
           \forall ( \varphi [ \up(\up^n(f \odot g)) ])$$
          However, we can use our assumption with $n + 1$ and obtain an equality. ;*)
    try (f_equal; apply (IHφ (S n))).
Qed.

Lemma subst_form_compose_pt (f g : nat -> term) φ :
  (subst_form f) (subst_form g φ) = subst_form (f ☉ g) φ.
Proof. apply (subst_form_upN_compose_pt f g φ 0). Qed.

Lemma subst_form_compose (f g : nat -> term) :
  (subst_form f) ∘ (subst_form g) = subst_form (f ☉ g).
Proof. apply functional_extensionality. apply subst_form_compose_pt. Qed.

Lemma subst_form_compose' f g : (subst_form f) ∘ (subst_form g) = subst_form (f ☉ g).
Proof. apply functional_extensionality; apply subst_form_compose_pt. Qed.

(*### Properties of lifting and binding ###*)

(*; So far we have seen that in general for any $h$:
    \begin{align*}
        \up^{n+1}(h)(i+1) &= \up(\up^{n}(h))(i+1) \\
                               &= \cons(x_0, S' \odot \up^n(h))(i+1) \\
                               &= \up^n(h)(i)[S']
    \end{align*}
    In this section we will build a small repository of properties of lifting. ;*)

(*{ Right nest lift }*)
(*; $\up^{n + 1}(f)(i) = \up^n(\up(f))(i)$ ;*)
Lemma upN_succ_pt n f i : upN (S n) f i = upN n (up f) i.
Proof.
  (*; Trivial by induction on $i$ and cases on $n$. ;*)
  revert n; induction i; destruct n; try easy; simpl; f_equal; apply IHi.
Qed.

Lemma upN_succ n f : upN (S n) f = upN n (up f).
Proof. apply functional_extensionality; intros; apply upN_succ_pt. Qed.

(*{ Lifted $S'$ evaluation for $i \geq n$ }*)
(*; $\forall n\; i \geq n \implies \up^n(S')(i) = x_{i + 1}$ ;*)
Lemma upN_S_geq i : forall n,  i >= n -> upN n S' i = var (S i).
Proof.
  (*; Trivial by induction on $i$ and cases on $n$. ;*)
  induction i; intros.
  - destruct n. easy. lia.
  - destruct n. easy. intros; simpl; rewrite IHi. easy. lia.
Qed.


(*{ Lifted $f$ evaluation for $i < n$ }*)
(*; $\forall n\; i < n \implies \up^n(f)(i) = x_{i}$ ;*)
Lemma upN_f_lt_ident_pt f i : forall n, i < n -> upN n f i = var i.
Proof.
  (*; Trivial by induction on $i$ and cases on $n$. ;*)
  induction i.
  - destruct n. lia. easy.
  - destruct n. lia. intros; simpl; rewrite IHi. easy. lia.
Qed.

(*; The following theorem describes how $\up^n(f)$ behaves
    when composed with $B(t)$. This is a relatively trivial, but
    will be quite useful. ;*)

(*[ Commutation of arbitrary substitutions and binding ]*)
(*; \\$\up^n(f) \odot B(t) = B(t[\up^n(f)]) \odot \up^{n+1}(f)$ ;*)
Lemma upN_f_bind_var_t_commute_pt n (t : term) f i:
  subst_term (upN n f) (bind_var t i) = subst_term (bind_var (subst_term (upN n f) t)) ((upN (S n) f) i).
Proof.
  (*; Rewrite as $B(t)(i)[\up^n(f)] = \up^{n+1}(f)(i)[B(t[\up^n(f)])]$ and cases for $i$: :*)
  destruct i.
  (*: - **Case 1:** When $i = 0$, this simplifies to:
        $$t[\up^n(f)] = \up^{n+1}(f)(0)[B(\up^n(f))] = x_0[B(t[\up^n(f)])] = t[\up^n(f)]$$ :*)
  - simpl. easy.
  (*: - **Case 2:** For $i + 1$, the left-hand side can be written as:
        $$B(t)(i + 1)[ \up^n(f) ] = x_i[ \up^n(f) ]$$

        The right-hand side follows by composition:
          \begin{align*}
              \up^{n+1}(f)(i + 1)[B(t[\up^n(f)])]
                  &= \up^n(h)(i)[S'][B(t[\up^n(f)])] \\
                  &= \up^n(h)(i)[B(t[\up^n(f)]) \odot S'] \\
                  &= \up^n(h)(i)[\id] = x_i[\up^n(h)]
          \end{align*} ;*)
  - simpl; rewrite !subst_term_compose_pt; simpl; rewrite !subst_term_ident_pt; easy.
Qed.

Lemma upN_f_bind_var_t_commute n (t : term) f :
  (upN n f) ☉ bind_var t = bind_var (subst_term (upN n f) t) ☉ (upN (S n) f).
Proof. intros; apply functional_extensionality. apply upN_f_bind_var_t_commute_pt. Qed.

Lemma f_bind_var_t_commute_pt (t : term) f x:
  subst_term f (bind_var t x) = subst_term (bind_var (subst_term f t)) (⇑ f x).
Proof. apply (upN_f_bind_var_t_commute_pt 0). Qed.
  
Lemma f_bind_var_t_commute (t : term) f :
  f ☉ bind_var t = bind_var (subst_term f t) ☉ (up f).
Proof. intros; apply functional_extensionality. apply f_bind_var_t_commute_pt. Qed.

(*; Recall in our motivation for the predecessor substitution, we
    saw that $B(t) \odot S' = \id$. This theorem covers the case for:
    $$ S' \odot B(t) = B(t[S']) \odot \up(S') $$. Additionally it proves
    cases relating $B(u) \odot B(t)$: ;*)

(*[ Commutation of lifted binding with bindings ]*)
(*; \\$\up^n(B(u)) \odot B(t) = B(t[\up^n(B(u))]) \odot \up^{n + 1}(B(u))$ ;*)
Lemma upN_bind_var_t_bind_var_u_commute_pt n (t u : term) (i : nat) :
  (upN n (bind_var u) ☉ bind_var t) i = (bind_var (subst_term (upN n (bind_var u)) t) ☉ (upN (S n) (bind_var u))) i.
Proof. (*; Special case of commutation of arbitrary substitutions and bindings with $f = B(u)$ ;*)
  apply (upN_f_bind_var_t_commute_pt n t (bind_var u)).
Qed.

Lemma upN_bind_var_t_bind_var_u_commute n t u :
  (upN n (bind_var u) ☉ bind_var t) = (bind_var (subst_term (upN n (bind_var u)) t) ☉ (upN (S n) (bind_var u))).
Proof. apply functional_extensionality. intros. apply upN_bind_var_t_bind_var_u_commute_pt. Qed.

(*[ Commutation of bindings ]*)
(*; $B(u) \odot B(t[S']) = B(t) \odot \up(B(u))$ ;*)
Lemma bind_var_t_bind_var_Su_commute_pt (t : term) (u : term) (i : nat):
  subst_term (bind_var u) (bind_var (subst_term S' t) i) = subst_term (bind_var t) (up (bind_var u) i).
Proof.
  (*; This is again a special case of commutation of arbitrary substitutions and bindings.
      We know that: $B(u) \odot B(t[S']) = B(t[S'][B(u)]) \odot \up(B(u))$.

      We then see that $t[S'][B(u)] = t[B(u) \odot S'] = t[\id] = t$ ;*)
  pose (upN_bind_var_t_bind_var_u_commute_pt 0 (subst_term S' t) u) as H.  
  rewrite subst_term_compose_pt, subst_term_ident_pt in H.
  apply H.
Qed.

Lemma bind_var_t_bind_var_Su_commute t u :
  (bind_var u) ☉ (bind_var (subst_term S' t)) = (bind_var t) ☉ (up (bind_var u)).
Proof. apply functional_extensionality; intros; apply bind_var_t_bind_var_Su_commute_pt. Qed.

(*{ Identity of $B(x_0) \odot \up(S')$ }*)(*; $B(x_0) \odot \up(i[S']) = x_i$ ;*) 
Lemma bind_var_0_upS_ident_pt i : subst_term (bind_var (var 0)) (up S' i) = var i.
Proof.
  (*; Trivial by cases on $i$ ;*)
  destruct i; easy.
Qed.

Lemma bind_var_0_upS_ident : (bind_var (var 0)) ☉ (up S') = var.
Proof. apply functional_extensionality. apply bind_var_0_upS_ident_pt. Qed.

(*## Injectivity ##*)

(*; In this section we will prove that the substitutions we saw are injective. Naturally we start with the injectivity of $S'$ and $\up^n$, then substitution on terms, and so on. ;*)

(*{ Injectivity of term substitution by S' }*)
(*; \\$\forall x, y \in \term( x[S'] = y[S'] \implies x = y$ ;*)
Lemma inj_subst_term_S : Injective (subst_term S').
Proof.
  (*; This is proven by induction on $x$ and $y$. ;*)
  unfold Injective. induction x, y; intros; simpl; inversion H; try easy.
  apply (IHx1 y1) in H2; apply (IHx2 y2) in H3. f_equal. easy. easy.
Qed.

(*{ $x_0$ cannot be a result of shifting }*)(*; $x_0 \neq t[S']$ ;*)
Lemma var_0_neq_subst_term_S t : var 0 ≠ subst_term S' t.
Proof.
  (*; Trivial by cases on $t$ (equivalent to $0 \neq n + 1$) ;*)
  destruct t; simpl in *; discriminate.
Qed.

(*{ Injectivity of $n$-lifted shift }*)
(*; \\$\forall x, y \in \nat( \up^n(S')(x) = \up^n(S')(y) \implies x = y$ ;*)
Lemma inj_upN_S n : Injective (upN n S').
Proof.
  (*; We prove by induction over $n$, using previous lemma. :*)
  unfold Injective. induction n; intros; simpl in *.
  (*: - **Base case:** $S'(x) = S'(y) \implies x = y$, since $S'$ is injective. :*)   
  - inversion H. easy.
  (*: - **Assumption:** $\forall x, y \in \nat (\up^n(S')(x) = \up^n(S')(y) \implies x = y)$
      - **Inductive case:** ($n = m + 1$) We analyse cases on $x, y$ to show
        $$ \up^{n+1}(S')(x) = \up^{n+1}(S')(y) \implies x = y $$  :*)
  - induction x, y; try easy.
    (*:    - **Case 1:** $\up^{n+1}(S')(0) = \up^{n+1}(S')(0) \implies 0 = 0$ is trivial. :*)
    (*:    - **Case 2:** Without loss of generality, when:
                 $$ \up^{n+1}(S')(0) = \up^{n+1}(S')(y+1) \implies x = y $$
             The hypothesis simplifies to $x_0 = (\up^n(S')(y)[S']$, then by our previous
             case this is false, thus $x = y$. :*)
    + simpl in H. apply var_0_neq_subst_term_S in H; easy.
    + simpl in H. apply symmetry, var_0_neq_subst_term_S in H. easy.
    (*:    - **Case 3:** We must now prove that:
                $$ \up^{n+1}(S')(x+1) = \up^{n+1}(S')(y+1) \implies x + 1 = y + 1 $$
             Our hypothesis here simplifies to: $\up^n(S')(x)[S'] = \up^n(S')(y)[S']$
             Again by injectivity, we get $\up^n(S')(x) = \up^n(S')(y)$,
             then our inductive hypothesis we find $x = y$. ;*)
    + simpl in H. apply inj_subst_term_S in H; apply IHn in H. subst. easy.
Qed.

(*; To prove the injectivity of the swap substitution, we need the following lemma: ;*)

(*{ $x_1$ cannot be the result of a lifted shift }*)
(*; $x_1 \neq \up(S')(n)$ ;*)
Lemma var_1_neq_subst_term_up_S n : var 1 ≠ (up S' n).
Proof.
  (*; Trivial by cases on $n$. ;*)
  destruct n; simpl in *; easy; change (id' 1) with (S' 0); discriminate.
Qed.

(*{ Injectivity of the swap substitution }*)
(*; \\$\forall x, y \in \nat( \swap(x) =\swap(y) \implies x = y$ ;*)
Lemma inj_swap : Injective swap.
Proof.
  (*; We will use the observation that:
      $$\swap(z + 1) = \cons(x_1, \up(S'))(z + 1) = \up(S')(z)$$
      We go through cases for $x,y$ and use our previous lemmas.
      The base case will be omitted. :*)
  unfold Injective.
  destruct x, y; intros; simpl in *.
  - easy.
  (*: - **Case 1:** Without loss of generality, when:
          $$\swap(0) = \swap(y + 1) \implies 0 = y + 1$$
      Our hypothesis simplifies to $x_1 = \up(S')(y)$ which
      by our previous lemma is false, proving this case. :*)
  - apply var_1_neq_subst_term_up_S in H; easy.
  - apply symmetry, var_1_neq_subst_term_up_S in H; easy.
  (*: - **Case 2:** To prove: $\swap(x + 1) = \swap(y + 1) \implies x + 1 = y + 1$
        We see the hypothesis simplifies to $\up(S')(x) = \up(S')(y)$.
        By injectivity of $\up(S')$, this follows. ;*)
  - apply inj_upN_S with (n := 1) in H; subst; easy.
Qed.

(*{ Injectivity of $n$-lifted shift substitution }*)
(*; \\$\forall t, s \in \term( s[\up^n(S')] = t[\up^n(S')] \implies s = u$ ;*)
Lemma inj_subst_term_upN_S n : Injective (subst_term (upN n S')).
Proof.
  (*; Induction over $t$ and $s$ using several of our lifting identites.
      This involves several cases for each type of term. The base case
      applies the injectivity of $\up^n(S')$.
      The rest follows by induction and further case analysis. ;*)
  unfold Injective.
  intros x y. revert x y n.
  induction x, y; simpl in *; try easy; intros.
  - apply inj_upN_S in H. subst. easy.
  - case (decide (n < n1)); intros Hle.
    * apply (upN_f_lt_ident_pt S') in Hle. rewrite Hle in H. discriminate.
    * assert (n >= n1) by lia. apply (upN_S_geq) in H0. rewrite H0 in H. discriminate.
  - case (decide (n < n1)); intros Hle.
    * apply (upN_f_lt_ident_pt S') in Hle. rewrite Hle in H. discriminate.
    * assert (n >= n1) by lia. apply (upN_S_geq) in H0. rewrite H0 in H. discriminate.
  - case (decide (n0 < n1)); intros Hle.
    * apply (upN_f_lt_ident_pt S') in Hle. rewrite Hle in H. discriminate.
    * assert (n0 >= n1) by lia. apply (upN_S_geq) in H0. rewrite H0 in H. discriminate.
  - case (decide (n0 < n1)); intros Hle.
    * apply (upN_f_lt_ident_pt S') in Hle. rewrite Hle in H. discriminate.
    * assert (n0 >= n1) by lia. apply (upN_S_geq) in H0. rewrite H0 in H. discriminate.
  - inversion H. apply IHx1 in H2. apply IHx2 in H3. f_equal. easy. easy.
Qed.

(*; This proof follows for formulae substitution. ;*)

(*{ Injectivity of $n$-lifted injective functions }*)
(*; If $f$ is injective, then $\up^n(f)$ is also injective ;*)
Lemma inj_upN_f n f : Injective f -> Injective (upN n f).
Proof.
  (*; Induction over $k$ and $j$, using previous lemmas. ;*)
  induction n.
  - easy.
  - intros.
    unfold Injective.
    induction x, y; simpl; intros H1.
    + easy.
    + apply var_0_neq_subst_term_S in H1; easy.
    + apply symmetry, var_0_neq_subst_term_S in H1; easy.
    + apply inj_subst_term_upN_S with (n := 0) in H1.
      apply (IHn H)  in H1.
      subst.
      easy.
Qed.

Lemma inj_map_subst_term_S : Injective (map (subst_term S')).
Proof.
  unfold Injective.
  induction x, y; intros; try easy.
  inversion H. apply inj_subst_term_S in H1. apply IHx in H2. subst. easy.
Qed.

Lemma inj_map_subst_term_upN_S n : Injective (map (subst_term (upN n S'))).
Proof.
  unfold Injective.
  induction x, y; intros.
  - easy.
  - inversion H.
  - inversion H.
  - inversion H. apply inj_subst_term_upN_S in H1. subst.
    f_equal.
    induction n.
    + simpl in *. apply inj_map_subst_term_S in H2. easy.
    + apply IHx. inversion H. easy.
Qed.

Lemma inj_subst_form_upN_S n : Injective (subst_form (upN n S')).
Proof.
  unfold Injective.
  intros. revert x y n H.
  induction x, y; intros; inversion H;
    try (apply inj_map_subst_term_upN_S in H2; f_equal);
    try (apply IHx1 in H1; apply IHx2 in H2; rewrite H1, H2);
    try (apply (IHx y (S n)) in H1; rewrite H1); try easy.
Qed.

Lemma inj_subst_form_S : Injective (subst_form S').
Proof. apply (inj_subst_form_upN_S 0). Qed.

(*### Substitution on weight ###*)

(*{ Substitutions don't affect weight }*)
(*; $w(\varphi[\up^n(f)]) = w(\varphi)$ ;*)
Lemma weight_subst_upN_f n (f : nat -> term) (A : form):
  weight (subst_form (upN n f) A) = weight A.
Proof.
  (*; Induction on the formula's structure. :*)
  revert n.
  induction A; try easy;
    try (intros n; simpl; rewrite IHA1, IHA2; easy);
    try (intros n;
         simpl;
         f_equal;
         specialize (IHA (S n)) as IHA1;
         simpl in IHA1;
         rewrite IHA1;
         reflexivity).
Qed.

Lemma weight_subst_f (f : nat -> term) (A : form): weight (subst_form f A) = weight A.
Proof. apply (weight_subst_upN_f 0). Qed.

Lemma weight_subst_S (A : form) : weight (subst_form S' A) = weight A.
Proof. apply (weight_subst_upN_f 0 S'). Qed.
