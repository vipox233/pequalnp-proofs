import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_260

private def nextPos {n : ℕ} (hn : 0 < n) (pos : Fin n) : Fin n :=
  ⟨(pos.val + 1) % n, Nat.mod_lt _ hn⟩

private def shift {n : ℕ} (hn : 0 < n) (u : Fin n) (d : ℕ) : Fin n :=
  ⟨(u.val + d) % n, Nat.mod_lt _ hn⟩

private def cycDist {n : ℕ} (a b : Fin n) : ℕ :=
  (b.val + n - a.val) % n

private lemma shift_zero {n : ℕ} (hn : 0 < n) (u : Fin n) : shift hn u 0 = u := by
  apply Fin.ext
  simp [shift, Nat.mod_eq_of_lt u.isLt]

private lemma shift_succ {n : ℕ} (hn : 0 < n) (u : Fin n) (d : ℕ) :
    shift hn u (d + 1) = nextPos hn (shift hn u d) := by
  apply Fin.ext
  simp [shift, nextPos, Nat.add_assoc, Nat.mod_add_mod]

private lemma shift_add {n : ℕ} (hn : 0 < n) (u : Fin n) (a b : ℕ) :
    shift hn (shift hn u a) b = shift hn u (a + b) := by
  apply Fin.ext
  simp [shift, Nat.mod_add_mod, Nat.add_assoc]

private lemma shift_n {n : ℕ} (hn : 0 < n) (u : Fin n) : shift hn u n = u := by
  apply Fin.ext
  simp [shift, Nat.add_mod_right, Nat.mod_eq_of_lt u.isLt]

private lemma cycDist_lt {n : ℕ} (hn : 0 < n) (a b : Fin n) : cycDist a b < n :=
  Nat.mod_lt _ hn

private lemma shift_cycDist {n : ℕ} (hn : 0 < n) (a b : Fin n) :
    shift hn a (cycDist a b) = b := by
  apply Fin.ext
  dsimp only [shift, cycDist]
  rw [Nat.add_mod_mod]
  have h1 : a.val + (b.val + n - a.val) = b.val + n := by
    have := a.isLt
    omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt]

private lemma cycDist_shift {n : ℕ} (hn : 0 < n) (a : Fin n) {d : ℕ} (hd : d < n) :
    cycDist a (shift hn a d) = d := by
  dsimp only [cycDist, shift]
  have hmod : (a.val + d) % n + n - a.val = if a.val + d < n then d + n else d := by
    by_cases hlt : a.val + d < n
    · rw [if_pos hlt, Nat.mod_eq_of_lt hlt]
      omega
    · rw [if_neg hlt]
      have hge : n ≤ a.val + d := by omega
      have hlt2 : a.val + d - n < n := by have := a.isLt; omega
      have hm : (a.val + d) % n = a.val + d - n := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt2]
      rw [hm]
      omega
  rw [hmod]
  split_ifs
  · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hd]
  · exact Nat.mod_eq_of_lt hd

private lemma cycDist_self {n : ℕ} (hn : 0 < n) (u : Fin n) : cycDist u u = 0 := by
  dsimp only [cycDist]
  rw [show u.val + n - u.val = n by omega, Nat.mod_self]

private lemma shift_inj {n : ℕ} (hn : 0 < n) (u : Fin n) {d₁ d₂ : ℕ}
    (h₁ : d₁ < n) (h₂ : d₂ < n) (heq : shift hn u d₁ = shift hn u d₂) : d₁ = d₂ := by
  have := congrArg (cycDist u) heq
  rwa [cycDist_shift hn u h₁, cycDist_shift hn u h₂] at this

private def arcProd {n : ℕ} (hn : 0 < n) {G : Type} [Group G]
    (f : Fin n → G) (u : Fin n) (d : ℕ) : G :=
  ((List.range d).map (fun i => f (shift hn u i))).prod

private lemma arcProd_zero {n : ℕ} (hn : 0 < n) {G : Type} [Group G]
    (f : Fin n → G) (u : Fin n) : arcProd hn f u 0 = 1 := by
  simp [arcProd]

private lemma arcProd_succ {n : ℕ} (hn : 0 < n) {G : Type} [Group G]
    (f : Fin n → G) (u : Fin n) (d : ℕ) :
    arcProd hn f u (d + 1) = arcProd hn f u d * f (shift hn u d) := by
  simp [arcProd, List.range_succ]

private lemma arcProd_add {n : ℕ} (hn : 0 < n) {G : Type} [Group G]
    (f : Fin n → G) (u : Fin n) (a b : ℕ) :
    arcProd hn f u (a + b) = arcProd hn f u a * arcProd hn f (shift hn u a) b := by
  induction b with
  | zero => simp [arcProd]
  | succ b ih =>
    rw [← Nat.add_assoc, arcProd_succ, ih, arcProd_succ, mul_assoc, shift_add]

private lemma arcProd_zero_n {n : ℕ} (hn : 0 < n) {G : Type} [Group G]
    (f : Fin n → G) :
    arcProd hn f ⟨0, hn⟩ n = (List.ofFn f).prod := by
  dsimp only [arcProd]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [shift, Nat.mod_eq_of_lt (by simpa using h2 : i < n)]

private lemma arcProd_full_ne_one {n : ℕ} (hn : 0 < n) {G : Type} [Group G]
    (f : Fin n → G) (hf : (List.ofFn f).prod ≠ 1) (u : Fin n) :
    arcProd hn f u n ≠ 1 := by
  intro heq
  apply hf
  rw [← arcProd_zero_n hn f]
  have h1 : arcProd hn f ⟨0, hn⟩ n =
      arcProd hn f ⟨0, hn⟩ u.val * arcProd hn f u (n - u.val) := by
    have hsplit := arcProd_add hn f ⟨0, hn⟩ u.val (n - u.val)
    have hsum : u.val + (n - u.val) = n := by have := u.isLt; omega
    have hsh : shift hn ⟨0, hn⟩ u.val = u := by
      apply Fin.ext; simp [shift, Nat.mod_eq_of_lt u.isLt]
    rw [hsum, hsh] at hsplit
    exact hsplit
  have h2 : arcProd hn f u n =
      arcProd hn f u (n - u.val) * arcProd hn f ⟨0, hn⟩ u.val := by
    have hsplit := arcProd_add hn f u (n - u.val) u.val
    have hsum : (n - u.val) + u.val = n := by have := u.isLt; omega
    have hsh : shift hn u (n - u.val) = ⟨0, hn⟩ := by
      apply Fin.ext; simp [shift, hsum]
    rw [hsum, hsh] at hsplit
    exact hsplit
  rw [h2] at heq
  rw [h1]
  have hconj : arcProd hn f ⟨0, hn⟩ u.val * (arcProd hn f u (n - u.val) * arcProd hn f ⟨0, hn⟩ u.val) *
      (arcProd hn f ⟨0, hn⟩ u.val)⁻¹ = 1 := by
    rw [heq]; group
  simpa [mul_assoc] using hconj

private def faults {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (assignment : Fin n → G) : Finset (Fin n) :=
  Finset.univ.filter (fun site => assignment (nextPos hn site) ≠ assignment site * f site)

private def privateWords {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (f : Fin n → G) : Finset (Fin n → G) :=
  Finset.univ.filter (fun input : Fin n → G => (faults hn f input).card = 1)

private def mkWord {n : ℕ} (hn : 0 < n) {G : Type} [Group G]
    (f : Fin n → G) (e : Fin n) (g : G) (u : Fin n) : G :=
  g * arcProd hn f (nextPos hn e) (cycDist (nextPos hn e) u)

private lemma faults_mkWord {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (hf : (List.ofFn f).prod ≠ 1) (e : Fin n) (g : G) :
    faults hn f (mkWord hn f e g) = {e} := by
  ext b
  simp only [faults, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  set s := nextPos hn e
  have hs_shift : shift hn s (n - 1) = e := by
    apply Fin.ext
    dsimp only [shift, s, nextPos]
    rw [Nat.mod_add_mod]
    have h1 : e.val + 1 + (n - 1) = e.val + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt e.isLt]
  set k := cycDist s b with hk_def
  have hk_lt : k < n := cycDist_lt hn s b
  have hb_eq : shift hn s k = b := shift_cycDist hn s b
  by_cases hbe : b = e
  · subst hbe
    have hk_last : k = n - 1 := by
      rw [hk_def, ← hs_shift, cycDist_shift hn s (by omega)]
    have hnext_s : nextPos hn b = s := rfl
    have hdist0 : cycDist s s = 0 := cycDist_self hn s
    constructor
    · intro _; rfl
    · intro _
      dsimp only [mkWord]
      change g * arcProd hn f s (cycDist s s) ≠ g * arcProd hn f s k * f b
      rw [hdist0, arcProd_zero, mul_one, hk_last, ← hs_shift, mul_assoc, ← arcProd_succ,
        show n - 1 + 1 = n by omega]
      intro heq
      have h1 : g * 1 = g * arcProd hn f s n := by simpa using heq
      exact arcProd_full_ne_one hn f hf s (mul_left_cancel h1).symm
  · have hk_lt' : k + 1 < n := by
      by_contra hge
      have hkl : k = n - 1 := by omega
      rw [hkl, hs_shift] at hb_eq
      exact hbe hb_eq.symm
    have hnb : nextPos hn b = shift hn s (k + 1) := by
      rw [← hb_eq, ← shift_succ]
    have hdist_nb : cycDist s (nextPos hn b) = k + 1 := by
      rw [hnb, cycDist_shift hn s hk_lt']
    constructor
    · intro hne
      exfalso
      apply hne
      dsimp only [mkWord]
      change g * arcProd hn f s (cycDist s (nextPos hn b)) = g * arcProd hn f s k * f b
      rw [hdist_nb, arcProd_succ, hb_eq, mul_assoc]
    · intro h; exact False.elim (hbe h)

private lemma eq_mkWord_of_faults_singleton {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (x : Fin n → G) (e : Fin n) (hfault : faults hn f x = {e}) :
    x = mkWord hn f e (x (nextPos hn e)) := by
  set s := nextPos hn e
  have hs_shift : shift hn s (n - 1) = e := by
    apply Fin.ext
    dsimp only [shift, s, nextPos]
    rw [Nat.mod_add_mod]
    have h1 : e.val + 1 + (n - 1) = e.val + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt e.isLt]
  have hwalk : ∀ k < n, x (shift hn s k) = x s * arcProd hn f s k := by
    intro k
    induction k with
    | zero => intro _; rw [shift_zero, arcProd_zero, mul_one]
    | succ k ih =>
      intro hk
      have hne : shift hn s k ≠ e := by
        intro heq
        rw [← hs_shift] at heq
        have := shift_inj hn s (by omega) (by omega) heq
        omega
      have hnotin : shift hn s k ∉ faults hn f x := by
        rw [hfault, Finset.mem_singleton]
        exact hne
      simp only [faults, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnotin
      rw [shift_succ, hnotin, ih (by omega), arcProd_succ, mul_assoc]
  funext u
  have hu := hwalk (cycDist s u) (cycDist_lt hn s u)
  rw [shift_cycDist hn s u] at hu
  exact hu

private lemma privateWords_card {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (f : Fin n → G) (hf : (List.ofFn f).prod ≠ 1) :
    (privateWords hn f).card = n * Fintype.card G := by
  have himg : privateWords hn f =
      (Finset.univ : Finset (Fin n × G)).image (fun p => mkWord hn f p.1 p.2) := by
    ext x
    simp only [privateWords, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hcard
      rcases Finset.card_eq_one.mp hcard with ⟨e, he⟩
      exact ⟨(e, x (nextPos hn e)), (eq_mkWord_of_faults_singleton hn f x e he).symm⟩
    · rintro ⟨⟨e, g⟩, rfl⟩
      rw [faults_mkWord hn f hf e g, Finset.card_singleton]
  have hinj : Function.Injective (fun p : Fin n × G => mkWord hn f p.1 p.2) := by
    rintro ⟨e₁, g₁⟩ ⟨e₂, g₂⟩ heq
    dsimp only at heq
    have hf1 := faults_mkWord hn f hf e₁ g₁
    have hf2 := faults_mkWord hn f hf e₂ g₂
    rw [heq] at hf1
    have he : e₁ = e₂ := Finset.singleton_injective (hf1.symm.trans hf2)
    subst he
    have hval := congrFun heq (nextPos hn e₁)
    have hdist0 : cycDist (nextPos hn e₁) (nextPos hn e₁) = 0 := cycDist_self hn (nextPos hn e₁)
    simp only [mkWord, hdist0, arcProd_zero, mul_one] at hval
    exact Prod.ext rfl hval
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

private def wordAt {n : ℕ} (hn : 0 < n) {G : Type} [Group G]
    (f : Fin n → G) (u₀ : Fin n) (g₀ : G) (e : Fin n) : Fin n → G :=
  mkWord hn f e (g₀ * (arcProd hn f (nextPos hn e) (cycDist (nextPos hn e) u₀))⁻¹)

private lemma faults_wordAt {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (hf : (List.ofFn f).prod ≠ 1) (u₀ : Fin n) (g₀ : G) (e : Fin n) :
    faults hn f (wordAt hn f u₀ g₀ e) = {e} :=
  faults_mkWord hn f hf e _

private lemma wordAt_self {n : ℕ} (hn : 0 < n) {G : Type} [Group G]
    (f : Fin n → G) (u₀ : Fin n) (g₀ : G) (e : Fin n) :
    wordAt hn f u₀ g₀ e u₀ = g₀ := by
  simp [wordAt, mkWord]

private lemma wordAt_val_before {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (hf : (List.ofFn f).prod ≠ 1) (u₀ : Fin n) (g₀ : G) (e : Fin n)
    {d : ℕ} (hd : d ≤ cycDist u₀ e) :
    wordAt hn f u₀ g₀ e (shift hn u₀ d) = g₀ * arcProd hn f u₀ d := by
  induction d with
  | zero => rw [shift_zero, arcProd_zero, mul_one, wordAt_self]
  | succ d ih =>
    have hlt : d < cycDist u₀ e := by omega
    have hlt_n : d < n := lt_of_lt_of_le hlt (le_of_lt (cycDist_lt hn u₀ e))
    have hne : shift hn u₀ d ≠ e := by
      intro heq
      have := congrArg (cycDist u₀) heq
      rw [cycDist_shift hn u₀ hlt_n] at this
      omega
    have hnotin : shift hn u₀ d ∉ faults hn f (wordAt hn f u₀ g₀ e) := by
      rw [faults_wordAt hn f hf u₀ g₀ e, Finset.mem_singleton]
      exact hne
    simp only [faults, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnotin
    rw [shift_succ, hnotin, ih (by omega), arcProd_succ, mul_assoc]

private lemma wordAt_val_after {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (hf : (List.ofFn f).prod ≠ 1) (u₀ : Fin n) (g₀ : G) (e : Fin n)
    {d : ℕ} (hgt : cycDist u₀ e < d) (hd : d ≤ n) :
    wordAt hn f u₀ g₀ e (shift hn u₀ d) = g₀ * (arcProd hn f (shift hn u₀ d) (n - d))⁻¹ := by
  have hstep : ∀ k ≤ n - d,
      wordAt hn f u₀ g₀ e (shift hn u₀ (d + k)) =
        wordAt hn f u₀ g₀ e (shift hn u₀ d) * arcProd hn f (shift hn u₀ d) k := by
    intro k
    induction k with
    | zero => intro _; rw [Nat.add_zero, arcProd_zero, mul_one]
    | succ k ih =>
      intro hk
      have hlt_n : d + k < n := by omega
      have hne : shift hn u₀ (d + k) ≠ e := by
        intro heq
        have := congrArg (cycDist u₀) heq
        rw [cycDist_shift hn u₀ hlt_n] at this
        omega
      have hnotin : shift hn u₀ (d + k) ∉ faults hn f (wordAt hn f u₀ g₀ e) := by
        rw [faults_wordAt hn f hf u₀ g₀ e, Finset.mem_singleton]
        exact hne
      simp only [faults, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnotin
      rw [← Nat.add_assoc, shift_succ, hnotin, ih (by omega), arcProd_succ, shift_add, mul_assoc]
  have hend := hstep (n - d) le_rfl
  rw [Nat.add_sub_cancel' hd, shift_n, wordAt_self] at hend
  calc wordAt hn f u₀ g₀ e (shift hn u₀ d)
      = wordAt hn f u₀ g₀ e (shift hn u₀ d) * arcProd hn f (shift hn u₀ d) (n - d) *
          (arcProd hn f (shift hn u₀ d) (n - d))⁻¹ := by group
    _ = g₀ * (arcProd hn f (shift hn u₀ d) (n - d))⁻¹ := by rw [← hend]

private lemma wordAt_before_ne_after {n : ℕ} (hn : 0 < n) {G : Type} [Group G]
    (f : Fin n → G) (hf : (List.ofFn f).prod ≠ 1) (u₀ : Fin n) (g₀ : G)
    {d : ℕ} (hd : d ≤ n) :
    g₀ * arcProd hn f u₀ d ≠ g₀ * (arcProd hn f (shift hn u₀ d) (n - d))⁻¹ := by
  intro heq
  have h1 := mul_left_cancel heq
  have hprod : arcProd hn f u₀ n = 1 := by
    have hsplit := arcProd_add hn f u₀ d (n - d)
    rw [Nat.add_sub_cancel' hd] at hsplit
    rw [hsplit, h1, inv_mul_cancel]
  exact arcProd_full_ne_one hn f hf u₀ hprod

private lemma eq_wordAt_of_private {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (hf : (List.ofFn f).prod ≠ 1) (u₀ : Fin n) (x : Fin n → G) (e : Fin n)
    (hfault : faults hn f x = {e}) :
    x = wordAt hn f u₀ (x u₀) e := by
  have hx := eq_mkWord_of_faults_singleton hn f x e hfault
  have hval := congrFun hx u₀
  dsimp only [mkWord] at hval
  have hg : x (nextPos hn e) = x u₀ * (arcProd hn f (nextPos hn e) (cycDist (nextPos hn e) u₀))⁻¹ := by
    rw [hval]; group
  conv_lhs => rw [hx, hg]
  rfl

private abbrev Strategy (n : ℕ) (G : Type) :=
  List (Finset (Fin n × G)) → Finset (Fin n)

private def history {n : ℕ} {G : Type} [DecidableEq G]
    (ask : Strategy n G) (x : Fin n → G) (t : ℕ) : List (Finset (Fin n × G)) :=
  (List.range t).foldl (fun hist _ => hist ++ [(ask hist).image (fun u => (u, x u))]) []

private def batch {n : ℕ} {G : Type} [DecidableEq G]
    (ask : Strategy n G) (x : Fin n → G) (i : ℕ) : Finset (Fin n) :=
  ask (history ask x i)

private def price (bs : List ℕ) : ℕ × ℕ :=
  bs.foldr (fun k (p : ℕ × ℕ) => ((k + 1) * p.1, max (k * p.1) p.2)) (1, 0)

private lemma price_nil : price [] = (1, 0) := rfl

private lemma price_cons (k : ℕ) (rest : List ℕ) :
    price (k :: rest) = ((k + 1) * (price rest).1, max (k * (price rest).1) (price rest).2) := rfl

private lemma price_fst_pos : ∀ bs : List ℕ, 1 ≤ (price bs).1
  | [] => le_rfl
  | k :: rest => by
    rw [price_cons]
    have h := price_fst_pos rest
    nlinarith

private lemma history_zero {n : ℕ} {G : Type} [DecidableEq G]
    (ask : Strategy n G) (x : Fin n → G) : history ask x 0 = [] := rfl

private lemma history_succ {n : ℕ} {G : Type} [DecidableEq G]
    (ask : Strategy n G) (x : Fin n → G) (t : ℕ) :
    history ask x (t + 1) = history ask x t ++ [(batch ask x t).image (fun u => (u, x u))] := by
  simp [history, batch, List.range_succ, List.foldl_append]

private def consStrategy {n : ℕ} {G : Type}
    (B : Finset (Fin n)) (nextAsk : Finset (Fin n × G) → Strategy n G) : Strategy n G
  | [] => B
  | a :: rest => nextAsk a rest

private lemma history_consStrategy_succ {n : ℕ} {G : Type} [DecidableEq G]
    (B : Finset (Fin n)) (nextAsk : Finset (Fin n × G) → Strategy n G) (x : Fin n → G) :
    ∀ t, history (consStrategy B nextAsk) x (t + 1) =
      (B.image (fun u => (u, x u))) ::
        history (nextAsk (B.image (fun u => (u, x u)))) x t := by
  intro t
  induction t with
  | zero =>
    rw [history_succ, history_zero, history_zero]
    simp [batch, history_zero, consStrategy]
  | succ t ih =>
    rw [history_succ, ih]
    have hb : batch (consStrategy B nextAsk) x (t + 1) =
        batch (nextAsk (B.image (fun u => (u, x u)))) x t := by
      simp [batch, ih, consStrategy]
    rw [hb, history_succ]
    rfl

private lemma batch_consStrategy_zero {n : ℕ} {G : Type} [DecidableEq G]
    (B : Finset (Fin n)) (nextAsk : Finset (Fin n × G) → Strategy n G) (x : Fin n → G) :
    batch (consStrategy B nextAsk) x 0 = B := by
  simp [batch, history_zero, consStrategy]

private lemma batch_consStrategy_succ {n : ℕ} {G : Type} [DecidableEq G]
    (B : Finset (Fin n)) (nextAsk : Finset (Fin n × G) → Strategy n G) (x : Fin n → G) (t : ℕ) :
    batch (consStrategy B nextAsk) x (t + 1) =
      batch (nextAsk (B.image (fun u => (u, x u)))) x t := by
  simp [batch, history_consStrategy_succ, consStrategy]

private lemma history_tail_succ {n : ℕ} {G : Type} [DecidableEq G]
    (ask : Strategy n G) (x : Fin n → G) :
    ∀ t, history ask x (t + 1) =
      ((ask []).image (fun u => (u, x u))) ::
        history (fun rest => ask (((ask []).image (fun u => (u, x u))) :: rest)) x t := by
  intro t
  induction t with
  | zero =>
    rw [history_succ, history_zero, history_zero]
    simp [batch, history_zero]
  | succ t ih =>
    rw [history_succ, ih]
    have hb : batch ask x (t + 1) =
        batch (fun rest => ask (((ask []).image (fun u => (u, x u))) :: rest)) x t := by
      simp [batch, ih]
    rw [hb, history_succ]
    rfl

private lemma batch_tail_succ {n : ℕ} {G : Type} [DecidableEq G]
    (ask : Strategy n G) (x : Fin n → G) (t : ℕ) :
    batch ask x (t + 1) =
      batch (fun rest => ask (((ask []).image (fun u => (u, x u))) :: rest)) x t := by
  simp [batch, history_tail_succ]

private def legal {n : ℕ} {G : Type} [DecidableEq G] (bs : List ℕ) (rule : Strategy n G) : Prop :=
  ∀ (word : Fin n → G) (j : Fin bs.length), (batch rule word j.val).card ≤ bs[j.val]'j.isLt

private def seenOf {n : ℕ} {G : Type} [DecidableEq G]
    (bs : List ℕ) (rule : Strategy n G) (x : Fin n → G) : Finset (Fin n) :=
  (Finset.range bs.length).biUnion (batch rule x)

private lemma interval_partition_aux :
    ∀ (m : ℕ) (a b : ℕ) (M : Finset ℕ),
      a < b → (∀ x ∈ M, a < x ∧ x < b) → M.card = m →
      ∃ pts : ℕ → ℕ, pts 0 = a ∧ pts (m + 1) = b ∧
        (∀ r ≤ m, pts r < pts (r + 1)) ∧
        (∀ r ≤ m, ∀ x ∈ M, ¬(pts r < x ∧ x < pts (r + 1))) ∧
        (∀ r ≤ m, r ≠ 0 → pts r ∈ M) := by
  intro m
  induction m with
  | zero =>
    intro a b M hab hM hcard
    have hM0 : M = ∅ := Finset.card_eq_zero.mp hcard
    refine ⟨fun r => if r = 0 then a else b, by simp, by simp, ?_, ?_, ?_⟩
    · intro r hr
      have hr0 : r = 0 := by omega
      subst hr0
      simpa using hab
    · intro r _ x hx; rw [hM0] at hx; exact False.elim (Finset.notMem_empty x hx)
    · intro r hr hne; omega
  | succ m ih =>
    intro a b M hab hM hcard
    have hne : M.Nonempty := Finset.card_pos.mp (by omega)
    set p := M.min' hne
    have hpM : p ∈ M := Finset.min'_mem M hne
    have hp_bounds := hM p hpM
    have hM' : ∀ x ∈ M.erase p, p < x ∧ x < b := by
      intro x hx
      rcases Finset.mem_erase.mp hx with ⟨hxne, hxM⟩
      have hle : p ≤ x := Finset.min'_le M x hxM
      exact ⟨by omega, (hM x hxM).2⟩
    have hcard' : (M.erase p).card = m := by
      rw [Finset.card_erase_of_mem hpM, hcard]; omega
    rcases ih p b (M.erase p) hp_bounds.2 hM' hcard' with
      ⟨pts', h0', hend', hstrict', hno', hmem'⟩
    let pts : ℕ → ℕ := fun r => if r = 0 then a else pts' (r - 1)
    refine ⟨pts, by simp [pts], by simp [pts, hend'], ?_, ?_, ?_⟩
    · intro r hr
      by_cases hr0 : r = 0
      · subst hr0; simp [pts, h0', hp_bounds.1]
      · simp only [pts, hr0, show r + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
        have := hstrict' (r - 1) (by omega)
        rwa [show r - 1 + 1 = r by omega] at this
    · intro r hr x hx
      by_cases hr0 : r = 0
      · subst hr0
        simp only [pts, ite_true, show (1 : ℕ) ≠ 0 by omega, ite_false, Nat.sub_self, h0']
        have hle := Finset.min'_le M x hx
        omega
      · simp only [pts, hr0, show r + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
        by_cases hxp : x = p
        · subst hxp
          have hle : p ≤ pts' (r - 1) := by
            have hmono : ∀ t ≤ m + 1, p ≤ pts' t := by
              intro t
              induction t with
              | zero => intro _; rw [h0']
              | succ t iht => intro ht; have := hstrict' t (by omega); have := iht (by omega); omega
            exact hmono (r - 1) (by omega)
          omega
        · have := hno' (r - 1) (by omega) x (Finset.mem_erase.mpr ⟨hxp, hx⟩)
          rwa [show r - 1 + 1 = r by omega] at this
    · intro r hr hne0
      dsimp only [pts]
      rw [if_neg hne0]
      by_cases hr1 : r = 1
      · subst hr1; simpa [h0'] using hpM
      · exact Finset.erase_subset p M (hmem' (r - 1) (by omega) (by omega))

private lemma interval_sum_len (pts : ℕ → ℕ) (m : ℕ)
    (hmono : ∀ r ≤ m, pts r ≤ pts (r + 1)) :
    ∑ r ∈ Finset.range (m + 1), (pts (r + 1) - pts r) = pts (m + 1) - pts 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (fun r hr => hmono r (by omega))]
    have h0 : pts 0 ≤ pts (m + 1) := by
      clear ih
      induction m with
      | zero => exact hmono 0 (Nat.zero_le _)
      | succ k ihk => exact (ihk (fun r hr => hmono r (by omega))).trans (hmono (k + 1) (by omega))
    have h1 := hmono (m + 1) le_rfl
    omega

private lemma upper_pinned {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (hf : (List.ofFn f).prod ≠ 1) (u₀ : Fin n) (g₀ : G) :
    ∀ (bs : List ℕ) (rule : Strategy n G) (S : Finset (Fin n)) (a b : ℕ),
      a ≤ b → b ≤ n →
      (a < b → shift hn u₀ a ∈ S ∧ shift hn u₀ b ∈ S) →
      (∀ d, a < d → d < b → shift hn u₀ d ∉ S) →
      (∀ j ∈ Finset.Ico a b, ∀ (t : ℕ) (ht : t < bs.length),
        (batch rule (wordAt hn f u₀ g₀ (shift hn u₀ j)) t).card ≤ bs[t]'ht) →
      let hits := (Finset.Ico a b).filter (fun j =>
        let seen := S ∪ seenOf bs rule (wordAt hn f u₀ g₀ (shift hn u₀ j))
        shift hn u₀ j ∈ seen ∧ shift hn u₀ (j + 1) ∈ seen)
      hits.card ≤ (price bs).1 ∧ ((price bs).1 < b - a → hits.card ≤ (price bs).1 - 1) := by
  intro bs
  induction bs with
  | nil =>
    intro rule S a b hab hbn hEnd hNo _
    intro hits
    have hseen : ∀ j, S ∪ seenOf [] rule (wordAt hn f u₀ g₀ (shift hn u₀ j)) = S := by
      intro j; simp [seenOf]
    by_cases hlen : b - a ≤ 1
    · refine ⟨?_, fun h => by simp [price] at h; omega⟩
      calc hits.card ≤ (Finset.Ico a b).card := Finset.card_filter_le _ _
        _ = b - a := Nat.card_Ico a b
        _ ≤ 1 := hlen
    · have h0 : hits = ∅ := by
        ext j
        simp only [hits, Finset.mem_filter, Finset.mem_Ico, hseen, Finset.notMem_empty, iff_false,
          not_and]
        intro hj h1 h2
        by_cases hja : j = a
        · subst hja
          exact hNo (j + 1) (by omega) (by omega) h2
        · exact hNo j (by omega) (by omega) h1
      rw [h0, Finset.card_empty]
      simp [price]
  | cons k rest ih =>
    intro rule S a b hab hbn hEnd hNo hCard
    intro hits
    by_cases hab_eq : a = b
    · subst hab_eq
      have h0 : hits = ∅ := by ext j; simp [hits]
      rw [h0, Finset.card_empty]
      exact ⟨Nat.zero_le _, fun _ => Nat.zero_le _⟩
    · have hab_lt : a < b := by omega
      set Q := rule []
      have hQle : Q.card ≤ k := by
        have h := hCard a (Finset.mem_Ico.mpr ⟨le_rfl, hab_lt⟩) 0 (by simp)
        simpa [batch, history_zero, Q] using h
      set M : Finset ℕ := (Finset.Ioo a b).filter (fun d => shift hn u₀ d ∈ Q)
      have hMle : M.card ≤ Q.card := by
        have hinj : Set.InjOn (shift hn u₀) M := by
          intro d₁ hd₁ d₂ hd₂ heq
          have h1 := Finset.mem_Ioo.mp (Finset.mem_filter.mp hd₁).1
          have h2 := Finset.mem_Ioo.mp (Finset.mem_filter.mp hd₂).1
          exact shift_inj hn u₀ (by omega) (by omega) heq
        have hmaps : Set.MapsTo (shift hn u₀) M Q := by
          intro d hd; exact (Finset.mem_filter.mp hd).2
        exact Finset.card_le_card_of_injOn (shift hn u₀) hmaps hinj
      set m := M.card
      have hm_le_k : m ≤ k := hMle.trans hQle
      have hMbounds : ∀ d ∈ M, a < d ∧ d < b := fun d hd => Finset.mem_Ioo.mp (Finset.mem_filter.mp hd).1
      have hpart : ∃ pts : ℕ → ℕ, pts 0 = a ∧ pts (m + 1) = b ∧
          (∀ r ≤ m, pts r < pts (r + 1)) ∧
          (∀ r ≤ m, ∀ x ∈ M, ¬(pts r < x ∧ x < pts (r + 1))) ∧
          (∀ r ≤ m, r ≠ 0 → pts r ∈ M) := by
        by_cases hm0 : m = 0
        · have hM0 : M = ∅ := Finset.card_eq_zero.mp hm0
          refine ⟨fun r => if r = 0 then a else b, by simp, by simp [hm0], ?_, ?_, ?_⟩
          · intro r hr
            have hr0 : r = 0 := by omega
            subst hr0; simpa using hab_lt
          · intro r _ x hx; rw [hM0] at hx; exact False.elim (Finset.notMem_empty x hx)
          · intro r hr hne; omega
        · exact interval_partition_aux m a b M hab_lt hMbounds rfl
      rcases hpart with ⟨pts, hpts0, hptsm, hstrict, hnoM, hmemM⟩
      have hpts_mono : ∀ r ≤ m, pts r ≤ pts (r + 1) := fun r hr => le_of_lt (hstrict r hr)
      have hpts_le_b : ∀ r ≤ m + 1, pts r ≤ b := by
        intro r hr
        rw [← hptsm]
        have hle : ∀ d, r + d ≤ m + 1 → pts r ≤ pts (r + d) := by
          intro d
          induction d with
          | zero => intro _; exact le_rfl
          | succ d ihd =>
            intro hd
            exact (ihd (by omega)).trans (hpts_mono (r + d) (by omega))
        have := hle (m + 1 - r) (by omega)
        rwa [Nat.add_sub_cancel' hr] at this
      have ha_le_pts : ∀ r ≤ m + 1, a ≤ pts r := by
        intro r hr
        rw [← hpts0]
        induction r with
        | zero => exact le_rfl
        | succ r ihr => exact (ihr (by omega)).trans (hpts_mono r (by omega))
      have hsub_hit : ∀ r ≤ m,
          let H_r := (Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
            let seen := S ∪ seenOf (k :: rest) rule (wordAt hn f u₀ g₀ (shift hn u₀ j))
            shift hn u₀ j ∈ seen ∧ shift hn u₀ (j + 1) ∈ seen)
          H_r.card ≤ (price rest).1 ∧ ((price rest).1 < pts (r + 1) - pts r → H_r.card ≤ (price rest).1 - 1) := by
        intro r hr
        have hlt_r : pts r < pts (r + 1) := hstrict r hr
        have hle_b : pts (r + 1) ≤ b := hpts_le_b (r + 1) (by omega)
        have hge_a : a ≤ pts r := ha_le_pts r (by omega)
        set j₀ := pts r
        set ans_r := Q.image (fun v => (v, wordAt hn f u₀ g₀ (shift hn u₀ j₀) v))
        let rule_r : Strategy n G := fun hist => rule (ans_r :: hist)
        have hans_same : ∀ j ∈ Finset.Ico (pts r) (pts (r + 1)),
            Q.image (fun v => (v, wordAt hn f u₀ g₀ (shift hn u₀ j) v)) = ans_r := by
          intro j hj
          rcases Finset.mem_Ico.mp hj with ⟨hj1, hj2⟩
          apply Finset.image_congr
          intro v hvQ
          congr 1
          set dv := cycDist u₀ v
          have hdv_lt : dv < n := cycDist_lt hn u₀ v
          have hv_eq : shift hn u₀ dv = v := shift_cycDist hn u₀ v
          have hdv_not : ¬(pts r < dv ∧ dv < pts (r + 1)) := by
            intro hbet
            have hdvM : dv ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, hv_eq.symm ▸ hvQ⟩
            exact hnoM r hr dv hdvM hbet
          have hdj : cycDist u₀ (shift hn u₀ j) = j := cycDist_shift hn u₀ (by omega)
          have hdj0 : cycDist u₀ (shift hn u₀ j₀) = j₀ := cycDist_shift hn u₀ (by omega)
          rw [← hv_eq]
          dsimp only
          by_cases hle_v : dv ≤ pts r
          · rw [wordAt_val_before hn f hf u₀ g₀ _ (by rw [hdj]; omega),
              wordAt_val_before hn f hf u₀ g₀ _ (by rw [hdj0]; omega)]
          · have hge_v : pts (r + 1) ≤ dv := by omega
            rw [wordAt_val_after hn f hf u₀ g₀ _ (by rw [hdj]; omega) (le_of_lt hdv_lt),
              wordAt_val_after hn f hf u₀ g₀ _ (by rw [hdj0]; omega) (le_of_lt hdv_lt)]
        have hseen_eq : ∀ j ∈ Finset.Ico (pts r) (pts (r + 1)),
            S ∪ seenOf (k :: rest) rule (wordAt hn f u₀ g₀ (shift hn u₀ j)) =
            (S ∪ Q) ∪ seenOf rest rule_r (wordAt hn f u₀ g₀ (shift hn u₀ j)) := by
          intro j hj
          have hans_j := hans_same j hj
          have hbt : ∀ t, batch rule (wordAt hn f u₀ g₀ (shift hn u₀ j)) (t + 1) =
              batch rule_r (wordAt hn f u₀ g₀ (shift hn u₀ j)) t := by
            intro t
            rw [batch_tail_succ]
            simp only [rule_r, ← hans_j, Q]
          ext w
          simp only [seenOf, List.length_cons, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
          constructor
          · rintro (hS | ⟨i, hi, hw⟩)
            · exact Or.inl (Or.inl hS)
            · cases i with
              | zero =>
                simp only [batch, history_zero] at hw
                exact Or.inl (Or.inr hw)
              | succ i =>
                rw [hbt i] at hw
                exact Or.inr ⟨i, by omega, hw⟩
          · rintro ((hS | hQ) | ⟨i, hi, hw⟩)
            · exact Or.inl hS
            · exact Or.inr ⟨0, by omega, by simpa [batch, history_zero] using hQ⟩
            · exact Or.inr ⟨i + 1, by omega, by rwa [hbt i]⟩
        have hEnd' : pts r < pts (r + 1) → shift hn u₀ (pts r) ∈ S ∪ Q ∧ shift hn u₀ (pts (r + 1)) ∈ S ∪ Q := by
          intro _
          constructor
          · by_cases hr0 : r = 0
            · subst hr0; rw [hpts0]; exact Finset.mem_union_left _ (hEnd hab_lt).1
            · exact Finset.mem_union_right _ (Finset.mem_filter.mp (hmemM r hr hr0)).2
          · by_cases hrlast : r = m
            · subst hrlast; rw [hptsm]; exact Finset.mem_union_left _ (hEnd hab_lt).2
            · exact Finset.mem_union_right _ (Finset.mem_filter.mp (hmemM (r + 1) (by omega) (by omega))).2
        have hNo' : ∀ d, pts r < d → d < pts (r + 1) → shift hn u₀ d ∉ S ∪ Q := by
          intro d hd1 hd2 hmem
          rcases Finset.mem_union.mp hmem with hS | hQ
          · exact hNo d (by omega) (by omega) hS
          · exact hnoM r hr d (Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, hQ⟩) ⟨hd1, hd2⟩
        have hCard' : ∀ j ∈ Finset.Ico (pts r) (pts (r + 1)), ∀ (t : ℕ) (ht : t < rest.length),
            (batch rule_r (wordAt hn f u₀ g₀ (shift hn u₀ j)) t).card ≤ rest[t]'ht := by
          intro j hj t ht
          have hans_j := hans_same j hj
          have h1 := hCard j (Finset.mem_Ico.mpr ⟨by have := (Finset.mem_Ico.mp hj).1; omega,
            by have := (Finset.mem_Ico.mp hj).2; omega⟩) (t + 1) (by simp [List.length_cons]; omega)
          rw [batch_tail_succ] at h1
          simpa [rule_r, ← hans_j, Q] using h1
        have hih := ih rule_r (S ∪ Q) (pts r) (pts (r + 1)) (le_of_lt hlt_r) (by omega) hEnd' hNo' hCard'
        have hfilt_eq : (Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
              let seen := S ∪ seenOf (k :: rest) rule (wordAt hn f u₀ g₀ (shift hn u₀ j))
              shift hn u₀ j ∈ seen ∧ shift hn u₀ (j + 1) ∈ seen) =
            (Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
              let seen := (S ∪ Q) ∪ seenOf rest rule_r (wordAt hn f u₀ g₀ (shift hn u₀ j))
              shift hn u₀ j ∈ seen ∧ shift hn u₀ (j + 1) ∈ seen) := by
          apply Finset.filter_congr
          intro j hj
          rw [hseen_eq j hj]
        dsimp only
        rw [hfilt_eq]
        exact hih
      have hdecomp : Finset.Ico a b = (Finset.range (m + 1)).biUnion (fun r => Finset.Ico (pts r) (pts (r + 1))) := by
        ext j
        simp only [Finset.mem_Ico, Finset.mem_biUnion, Finset.mem_range]
        constructor
        · rintro ⟨hja, hjb⟩
          have hex : ∃ r ≤ m, pts r ≤ j ∧ j < pts (r + 1) := by
            have haux : ∀ t ≤ m + 1, j < pts t → ∃ r < t, pts r ≤ j ∧ j < pts (r + 1) := by
              intro t
              induction t with
              | zero => intro _ hlt; rw [hpts0] at hlt; omega
              | succ t iht =>
                intro ht hlt
                by_cases hle : pts t ≤ j
                · exact ⟨t, by omega, hle, hlt⟩
                · rcases iht (by omega) (by omega) with ⟨r, hr, h1, h2⟩
                  exact ⟨r, by omega, h1, h2⟩
            rcases haux (m + 1) le_rfl (by rwa [hptsm]) with ⟨r, hr, h1, h2⟩
            exact ⟨r, by omega, h1, h2⟩
          rcases hex with ⟨r, hr, h1, h2⟩
          exact ⟨r, by omega, h1, h2⟩
        · rintro ⟨r, hr, h1, h2⟩
          exact ⟨(ha_le_pts r (by omega)).trans h1, lt_of_lt_of_le h2 (hpts_le_b (r + 1) (by omega))⟩
      have hdisj : Set.PairwiseDisjoint (↑(Finset.range (m + 1)))
          (fun r => (Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
            let seen := S ∪ seenOf (k :: rest) rule (wordAt hn f u₀ g₀ (shift hn u₀ j))
            shift hn u₀ j ∈ seen ∧ shift hn u₀ (j + 1) ∈ seen)) := by
        intro r₁ hr₁ r₂ hr₂ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro j h1 h2
        have hb1 := Finset.mem_Ico.mp (Finset.mem_filter.mp h1).1
        have hb2 := Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1
        have hr₁' : r₁ ≤ m := by have := Finset.mem_range.mp hr₁; omega
        have hr₂' : r₂ ≤ m := by have := Finset.mem_range.mp hr₂; omega
        have hstep_le : ∀ x y, x ≤ y → y ≤ m + 1 → pts x ≤ pts y := by
          intro x y hxy hy
          have hadd : ∀ d, x + d ≤ m + 1 → pts x ≤ pts (x + d) := by
            intro d
            induction d with
            | zero => intro _; exact le_rfl
            | succ d ihd => intro hd; exact (ihd (by omega)).trans (hpts_mono (x + d) (by omega))
          have := hadd (y - x) (by omega)
          rwa [Nat.add_sub_cancel' hxy] at this
        by_cases hlt : r₁ < r₂
        · have := hstep_le (r₁ + 1) r₂ (by omega) (by omega)
          omega
        · have := hstep_le (r₂ + 1) r₁ (by omega) (by omega)
          omega
      have hhits_card : hits.card = ∑ r ∈ Finset.range (m + 1),
          ((Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
            let seen := S ∪ seenOf (k :: rest) rule (wordAt hn f u₀ g₀ (shift hn u₀ j))
            shift hn u₀ j ∈ seen ∧ shift hn u₀ (j + 1) ∈ seen)).card := by
        have hfilt_bi : hits = (Finset.range (m + 1)).biUnion (fun r =>
            (Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
              let seen := S ∪ seenOf (k :: rest) rule (wordAt hn f u₀ g₀ (shift hn u₀ j))
              shift hn u₀ j ∈ seen ∧ shift hn u₀ (j + 1) ∈ seen)) := by
          dsimp only [hits]
          rw [hdecomp, Finset.filter_biUnion]
        rw [hfilt_bi, Finset.card_biUnion hdisj]
      rw [hhits_card, price_cons]
      have hPpos := price_fst_pos rest
      constructor
      · calc ∑ r ∈ Finset.range (m + 1),
              ((Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
                let seen := S ∪ seenOf (k :: rest) rule (wordAt hn f u₀ g₀ (shift hn u₀ j))
                shift hn u₀ j ∈ seen ∧ shift hn u₀ (j + 1) ∈ seen)).card
            ≤ ∑ _r ∈ Finset.range (m + 1), (price rest).1 :=
              Finset.sum_le_sum (fun r hr => (hsub_hit r (by have := Finset.mem_range.mp hr; omega)).1)
          _ = (m + 1) * (price rest).1 := by simp
          _ ≤ (k + 1) * (price rest).1 := Nat.mul_le_mul_right _ (by omega)
      · intro hlt_tot
        have hsum_len := interval_sum_len pts m hpts_mono
        rw [hpts0, hptsm] at hsum_len
        have hex_big : ∃ r₀ ∈ Finset.range (m + 1), (price rest).1 < pts (r₀ + 1) - pts r₀ := by
          by_contra hall
          push_neg at hall
          have hle_sum : b - a ≤ (m + 1) * (price rest).1 := by
            rw [← hsum_len]
            calc ∑ r ∈ Finset.range (m + 1), (pts (r + 1) - pts r)
                ≤ ∑ _r ∈ Finset.range (m + 1), (price rest).1 := Finset.sum_le_sum hall
              _ = (m + 1) * (price rest).1 := by simp
          have hmle : (m + 1) * (price rest).1 ≤ (k + 1) * (price rest).1 :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        rcases hex_big with ⟨r₀, hr₀, hbig⟩
        have hr₀_le : r₀ ≤ m := by have := Finset.mem_range.mp hr₀; omega
        have hsplit := Finset.add_sum_erase (Finset.range (m + 1))
          (fun r => ((Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
            let seen := S ∪ seenOf (k :: rest) rule (wordAt hn f u₀ g₀ (shift hn u₀ j))
            shift hn u₀ j ∈ seen ∧ shift hn u₀ (j + 1) ∈ seen)).card) hr₀
        have hr₀_le_sub := (hsub_hit r₀ hr₀_le).2 hbig
        have hrest_le : ∑ r ∈ (Finset.range (m + 1)).erase r₀,
            ((Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
              let seen := S ∪ seenOf (k :: rest) rule (wordAt hn f u₀ g₀ (shift hn u₀ j))
              shift hn u₀ j ∈ seen ∧ shift hn u₀ (j + 1) ∈ seen)).card ≤ m * (price rest).1 := by
          calc ∑ r ∈ (Finset.range (m + 1)).erase r₀,
                ((Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
                  let seen := S ∪ seenOf (k :: rest) rule (wordAt hn f u₀ g₀ (shift hn u₀ j))
                  shift hn u₀ j ∈ seen ∧ shift hn u₀ (j + 1) ∈ seen)).card
              ≤ ∑ _r ∈ (Finset.range (m + 1)).erase r₀, (price rest).1 :=
                Finset.sum_le_sum (fun r hr =>
                  (hsub_hit r (by have := Finset.mem_range.mp (Finset.mem_erase.mp hr).2; omega)).1)
            _ = m * (price rest).1 := by
                rw [Finset.sum_const, Finset.card_erase_of_mem hr₀, Finset.card_range, smul_eq_mul]
                simp
        have hm_mul : (m + 1) * (price rest).1 ≤ (k + 1) * (price rest).1 :=
          Nat.mul_le_mul_right _ (by omega)
        have hm_exp : (m + 1) * (price rest).1 = m * (price rest).1 + (price rest).1 := by ring
        omega

private abbrev successPred {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (bs : List ℕ) (search : Strategy n G) (values : Fin n → G) : Prop :=
  let seen := seenOf bs search values
  ∃ edge ∈ faults hn f values, edge ∈ seen ∧ nextPos hn edge ∈ seen

private lemma upper_unpinned {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n)
    {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (f : Fin n → G) (hf : (List.ofFn f).prod ≠ 1) :
    ∀ (bs : List ℕ) (probe : Strategy n G),
      legal bs probe → (price bs).2 < n →
      ((privateWords hn f).filter (fun cand => decide (successPred hn f bs probe cand))).card ≤
        ((price bs).2 - 1) * Fintype.card G := by
  intro bs
  induction bs with
  | nil =>
    intro probe _ _
    have h0 : (privateWords hn f).filter (fun cand => decide (successPred hn f [] probe cand)) = ∅ := by
      ext x
      simp [successPred, seenOf]
    rw [h0, Finset.card_empty]
    exact Nat.zero_le _
  | cons k rest ih =>
    intro probe hleg hBn
    set Q := probe []
    by_cases hQ0 : Q = ∅
    · let probe' : Strategy n G := fun hist => probe (∅ :: hist)
      have hleg' : legal rest probe' := by
        intro word j
        have h := hleg word ⟨j.val + 1, by simp [j.isLt]⟩
        rw [batch_tail_succ] at h
        have hemp : (probe []).image (fun u => (u, word u)) = ∅ := by simp [← show Q = probe [] from rfl, hQ0]
        simpa [probe', hemp] using h
      have hBrest : (price rest).2 ≤ (price (k :: rest)).2 := by
        rw [price_cons]; exact le_max_right _ _
      have hih := ih probe' hleg' (lt_of_le_of_lt hBrest hBn)
      have hsame_succ : ∀ x, successPred hn f (k :: rest) probe x ↔ successPred hn f rest probe' x := by
        intro x
        have hseen : seenOf (k :: rest) probe x = seenOf rest probe' x := by
          ext w
          simp only [seenOf, List.length_cons, Finset.mem_biUnion, Finset.mem_range]
          constructor
          · rintro ⟨i, hi, hw⟩
            cases i with
            | zero =>
              simp only [batch, history_zero] at hw
              change w ∈ Q at hw
              rw [hQ0] at hw
              exact False.elim (Finset.notMem_empty w hw)
            | succ i =>
              rw [batch_tail_succ] at hw
              have hemp : (probe []).image (fun u => (u, x u)) = ∅ := by simp [← show Q = probe [] from rfl, hQ0]
              exact ⟨i, by omega, by simpa [probe', hemp] using hw⟩
          · rintro ⟨i, hi, hw⟩
            refine ⟨i + 1, by omega, ?_⟩
            rw [batch_tail_succ]
            have hemp : (probe []).image (fun u => (u, x u)) = ∅ := by simp [← show Q = probe [] from rfl, hQ0]
            simpa [probe', hemp] using hw
        simp only [successPred, hseen]
      have hfilt : (privateWords hn f).filter (fun cand => decide (successPred hn f (k :: rest) probe cand)) =
          (privateWords hn f).filter (fun cand => decide (successPred hn f rest probe' cand)) := by
        apply Finset.filter_congr
        intro x _
        simp [hsame_succ x]
      rw [hfilt]
      exact hih.trans (Nat.mul_le_mul_right _ (by omega))
    · have hQne : Q.Nonempty := Finset.nonempty_iff_ne_empty.mpr hQ0
      rcases hQne with ⟨u₀, hu₀Q⟩
      have hQle : Q.card ≤ k := by
        have h := hleg (fun _ => 1) ⟨0, by simp⟩
        simpa [batch, history_zero, Q] using h
      have hpart_fib : (privateWords hn f).filter (fun cand => decide (successPred hn f (k :: rest) probe cand)) =
          (Finset.univ : Finset G).biUnion (fun g₀ =>
            ((Finset.range n).filter (fun j =>
              successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j)))).image
              (fun j => wordAt hn f u₀ g₀ (shift hn u₀ j))) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
          Finset.mem_range, decide_eq_true_eq]
        constructor
        · rintro ⟨hxP, hsucc⟩
          simp only [privateWords, Finset.mem_filter, Finset.mem_univ, true_and] at hxP
          rcases Finset.card_eq_one.mp hxP with ⟨e, he⟩
          have hx_eq := eq_wordAt_of_private hn f hf u₀ x e he
          refine ⟨x u₀, cycDist u₀ e, ⟨cycDist_lt hn u₀ e, ?_⟩, ?_⟩
          · rw [shift_cycDist hn u₀ e, ← hx_eq]; exact hsucc
          · rw [shift_cycDist hn u₀ e]; exact hx_eq.symm
        · rintro ⟨g₀, j, ⟨hj, hsucc⟩, rfl⟩
          refine ⟨?_, hsucc⟩
          simp only [privateWords, Finset.mem_filter, Finset.mem_univ, true_and,
            faults_wordAt hn f hf u₀ g₀ (shift hn u₀ j), Finset.card_singleton]
      have hfiber_le : ∀ g₀ : G,
          ((Finset.range n).filter (fun j =>
            successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j)))).card ≤
          (price (k :: rest)).2 - 1 := by
        intro g₀
        set M : Finset ℕ := (Finset.Ioo 0 n).filter (fun d => shift hn u₀ d ∈ Q)
        have hMle : M.card ≤ Q.card - 1 := by
          have hinj : Set.InjOn (shift hn u₀) M := by
            intro d₁ hd₁ d₂ hd₂ heq
            have h1 := Finset.mem_Ioo.mp (Finset.mem_filter.mp hd₁).1
            have h2 := Finset.mem_Ioo.mp (Finset.mem_filter.mp hd₂).1
            exact shift_inj hn u₀ h1.2 h2.2 heq
          have hmaps : Set.MapsTo (shift hn u₀) M (Q.erase u₀) := by
            intro d hd
            have h1 := Finset.mem_Ioo.mp (Finset.mem_filter.mp hd).1
            have h2 := (Finset.mem_filter.mp hd).2
            refine Finset.mem_erase.mpr ⟨?_, h2⟩
            intro heq
            have := congrArg (cycDist u₀) heq
            rw [cycDist_shift hn u₀ h1.2, cycDist_self hn u₀] at this
            omega
          have hc := Finset.card_le_card_of_injOn (shift hn u₀) hmaps hinj
          rwa [Finset.card_erase_of_mem hu₀Q] at hc
        set m := M.card
        have hm1_le_k : m + 1 ≤ k := by
          have h1 : 1 ≤ Q.card := Finset.one_le_card.mpr ⟨u₀, hu₀Q⟩
          omega
        have hMbounds : ∀ d ∈ M, 0 < d ∧ d < n := fun d hd => Finset.mem_Ioo.mp (Finset.mem_filter.mp hd).1
        have hpart : ∃ pts : ℕ → ℕ, pts 0 = 0 ∧ pts (m + 1) = n ∧
            (∀ r ≤ m, pts r < pts (r + 1)) ∧
            (∀ r ≤ m, ∀ x ∈ M, ¬(pts r < x ∧ x < pts (r + 1))) ∧
            (∀ r ≤ m, r ≠ 0 → pts r ∈ M) := by
          by_cases hm0 : m = 0
          · have hM0 : M = ∅ := Finset.card_eq_zero.mp hm0
            refine ⟨fun r => if r = 0 then 0 else n, by simp, by simp [hm0], ?_, ?_, ?_⟩
            · intro r hr
              have hr0 : r = 0 := by omega
              subst hr0
              simpa using hn
            · intro r _ x hx; rw [hM0] at hx; exact False.elim (Finset.notMem_empty x hx)
            · intro r hr hne; omega
          · exact interval_partition_aux m 0 n M hn hMbounds rfl
        rcases hpart with ⟨pts, hpts0, hptsm, hstrict, hnoM, hmemM⟩
        have hpts_mono : ∀ r ≤ m, pts r ≤ pts (r + 1) := fun r hr => le_of_lt (hstrict r hr)
        have hpts_le_n : ∀ r ≤ m + 1, pts r ≤ n := by
          intro r hr
          rw [← hptsm]
          have hle : ∀ d, r + d ≤ m + 1 → pts r ≤ pts (r + d) := by
            intro d
            induction d with
            | zero => intro _; exact le_rfl
            | succ d ihd => intro hd; exact (ihd (by omega)).trans (hpts_mono (r + d) (by omega))
          have := hle (m + 1 - r) (by omega)
          rwa [Nat.add_sub_cancel' hr] at this
        have hsub_hit : ∀ r ≤ m,
            let H_r := (Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
              successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j)))
            H_r.card ≤ (price rest).1 ∧ ((price rest).1 < pts (r + 1) - pts r → H_r.card ≤ (price rest).1 - 1) := by
          intro r hr
          have hlt_r : pts r < pts (r + 1) := hstrict r hr
          have hle_n : pts (r + 1) ≤ n := hpts_le_n (r + 1) (by omega)
          set j₀ := pts r
          set ans_r := Q.image (fun v => (v, wordAt hn f u₀ g₀ (shift hn u₀ j₀) v))
          let rule_r : Strategy n G := fun hist => probe (ans_r :: hist)
          have hans_same : ∀ j ∈ Finset.Ico (pts r) (pts (r + 1)),
              Q.image (fun v => (v, wordAt hn f u₀ g₀ (shift hn u₀ j) v)) = ans_r := by
            intro j hj
            rcases Finset.mem_Ico.mp hj with ⟨hj1, hj2⟩
            apply Finset.image_congr
            intro v hvQ
            congr 1
            set dv := cycDist u₀ v
            have hdv_lt : dv < n := cycDist_lt hn u₀ v
            have hv_eq : shift hn u₀ dv = v := shift_cycDist hn u₀ v
            have hdv_not : ¬(pts r < dv ∧ dv < pts (r + 1)) := by
              intro hbet
              have hdvM : dv ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by omega, hdv_lt⟩, hv_eq.symm ▸ hvQ⟩
              exact hnoM r hr dv hdvM hbet
            have hdj : cycDist u₀ (shift hn u₀ j) = j := cycDist_shift hn u₀ (by omega)
            have hdj0 : cycDist u₀ (shift hn u₀ j₀) = j₀ := cycDist_shift hn u₀ (by omega)
            rw [← hv_eq]
            dsimp only
            by_cases hle_v : dv ≤ pts r
            · rw [wordAt_val_before hn f hf u₀ g₀ _ (by rw [hdj]; omega),
                wordAt_val_before hn f hf u₀ g₀ _ (by rw [hdj0]; omega)]
            · have hge_v : pts (r + 1) ≤ dv := by omega
              rw [wordAt_val_after hn f hf u₀ g₀ _ (by rw [hdj]; omega) (le_of_lt hdv_lt),
                wordAt_val_after hn f hf u₀ g₀ _ (by rw [hdj0]; omega) (le_of_lt hdv_lt)]
          have hseen_eq : ∀ j ∈ Finset.Ico (pts r) (pts (r + 1)),
              seenOf (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j)) =
              Q ∪ seenOf rest rule_r (wordAt hn f u₀ g₀ (shift hn u₀ j)) := by
            intro j hj
            have hans_j := hans_same j hj
            have hbt : ∀ t, batch probe (wordAt hn f u₀ g₀ (shift hn u₀ j)) (t + 1) =
                batch rule_r (wordAt hn f u₀ g₀ (shift hn u₀ j)) t := by
              intro t
              rw [batch_tail_succ]
              simp only [rule_r, ← hans_j, Q]
            ext w
            simp only [seenOf, List.length_cons, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
            constructor
            · rintro ⟨i, hi, hw⟩
              cases i with
              | zero => simp only [batch, history_zero] at hw; exact Or.inl hw
              | succ i => rw [hbt i] at hw; exact Or.inr ⟨i, by omega, hw⟩
            · rintro (hQ | ⟨i, hi, hw⟩)
              · exact ⟨0, by omega, by simpa [batch, history_zero] using hQ⟩
              · exact ⟨i + 1, by omega, by rwa [hbt i]⟩
          have hEnd' : pts r < pts (r + 1) → shift hn u₀ (pts r) ∈ Q ∧ shift hn u₀ (pts (r + 1)) ∈ Q := by
            intro _
            constructor
            · by_cases hr0 : r = 0
              · subst hr0; rw [hpts0, shift_zero]; exact hu₀Q
              · exact (Finset.mem_filter.mp (hmemM r hr hr0)).2
            · by_cases hrlast : r = m
              · subst hrlast; rw [hptsm, shift_n]; exact hu₀Q
              · exact (Finset.mem_filter.mp (hmemM (r + 1) (by omega) (by omega))).2
          have hNo' : ∀ d, pts r < d → d < pts (r + 1) → shift hn u₀ d ∉ Q := by
            intro d hd1 hd2 hQ
            exact hnoM r hr d (Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, hQ⟩) ⟨hd1, hd2⟩
          have hCard' : ∀ j ∈ Finset.Ico (pts r) (pts (r + 1)), ∀ (t : ℕ) (ht : t < rest.length),
              (batch rule_r (wordAt hn f u₀ g₀ (shift hn u₀ j)) t).card ≤ rest[t]'ht := by
            intro j hj t ht
            have hans_j := hans_same j hj
            have h1 := hleg (wordAt hn f u₀ g₀ (shift hn u₀ j)) ⟨t + 1, by simp [List.length_cons]; omega⟩
            rw [batch_tail_succ] at h1
            simpa [rule_r, ← hans_j, Q] using h1
          have hup := upper_pinned hn f hf u₀ g₀ rest rule_r Q (pts r) (pts (r + 1)) (le_of_lt hlt_r) hle_n hEnd' hNo' hCard'
          have hfilt_eq : (Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
                successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j))) =
              (Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
                let seen := Q ∪ seenOf rest rule_r (wordAt hn f u₀ g₀ (shift hn u₀ j))
                shift hn u₀ j ∈ seen ∧ shift hn u₀ (j + 1) ∈ seen) := by
            apply Finset.filter_congr
            intro j hj
            simp only [successPred, faults_wordAt hn f hf u₀ g₀ (shift hn u₀ j),
              Finset.mem_singleton, exists_eq_left, hseen_eq j hj, shift_succ]
          dsimp only
          rw [hfilt_eq]
          exact hup
        have hdecomp : Finset.range n = (Finset.range (m + 1)).biUnion (fun r => Finset.Ico (pts r) (pts (r + 1))) := by
          ext j
          simp only [Finset.mem_range, Finset.mem_biUnion, Finset.mem_Ico]
          constructor
          · intro hjn
            have haux : ∀ t ≤ m + 1, j < pts t → ∃ r < t, pts r ≤ j ∧ j < pts (r + 1) := by
              intro t
              induction t with
              | zero => intro _ hlt; rw [hpts0] at hlt; omega
              | succ t iht =>
                intro ht hlt
                by_cases hle : pts t ≤ j
                · exact ⟨t, by omega, hle, hlt⟩
                · rcases iht (by omega) (by omega) with ⟨r, hr, h1, h2⟩
                  exact ⟨r, by omega, h1, h2⟩
            rcases haux (m + 1) le_rfl (by rwa [hptsm]) with ⟨r, hr, h1, h2⟩
            exact ⟨r, by omega, h1, h2⟩
          · rintro ⟨r, hr, _, h2⟩
            exact lt_of_lt_of_le h2 (hpts_le_n (r + 1) (by omega))
        have hdisj : Set.PairwiseDisjoint (↑(Finset.range (m + 1)))
            (fun r => (Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
              successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j)))) := by
          intro r₁ hr₁ r₂ hr₂ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro j h1 h2
          have hb1 := Finset.mem_Ico.mp (Finset.mem_filter.mp h1).1
          have hb2 := Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1
          have hr₁' : r₁ ≤ m := by have := Finset.mem_range.mp hr₁; omega
          have hr₂' : r₂ ≤ m := by have := Finset.mem_range.mp hr₂; omega
          have hstep_le : ∀ x y, x ≤ y → y ≤ m + 1 → pts x ≤ pts y := by
            intro x y hxy hy
            have hadd : ∀ d, x + d ≤ m + 1 → pts x ≤ pts (x + d) := by
              intro d
              induction d with
              | zero => intro _; exact le_rfl
              | succ d ihd => intro hd; exact (ihd (by omega)).trans (hpts_mono (x + d) (by omega))
            have := hadd (y - x) (by omega)
            rwa [Nat.add_sub_cancel' hxy] at this
          by_cases hlt : r₁ < r₂
          · have := hstep_le (r₁ + 1) r₂ (by omega) (by omega); omega
          · have := hstep_le (r₂ + 1) r₁ (by omega) (by omega); omega
        have hcard_sum : ((Finset.range n).filter (fun j =>
            successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j)))).card =
            ∑ r ∈ Finset.range (m + 1),
              ((Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
                successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j)))).card := by
          have hfb : (Finset.range n).filter (fun j =>
              successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j))) =
              (Finset.range (m + 1)).biUnion (fun r =>
                (Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
                  successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j)))) := by
            rw [hdecomp, Finset.filter_biUnion]
          rw [hfb, Finset.card_biUnion hdisj]
        rw [hcard_sum]
        have hsum_len := interval_sum_len pts m hpts_mono
        rw [hpts0, hptsm, Nat.sub_zero] at hsum_len
        have hkP_le_B : k * (price rest).1 ≤ (price (k :: rest)).2 := by
          rw [price_cons]; exact le_max_left _ _
        have hmP_lt_n : (m + 1) * (price rest).1 < n := by
          have : (m + 1) * (price rest).1 ≤ k * (price rest).1 :=
            Nat.mul_le_mul_right _ hm1_le_k
          omega
        have hex_big : ∃ r₀ ∈ Finset.range (m + 1), (price rest).1 < pts (r₀ + 1) - pts r₀ := by
          by_contra hall
          push_neg at hall
          have hle_sum : n ≤ (m + 1) * (price rest).1 := by
            rw [← hsum_len]
            calc ∑ r ∈ Finset.range (m + 1), (pts (r + 1) - pts r)
                ≤ ∑ _r ∈ Finset.range (m + 1), (price rest).1 := Finset.sum_le_sum hall
              _ = (m + 1) * (price rest).1 := by simp
          omega
        rcases hex_big with ⟨r₀, hr₀, hbig⟩
        have hr₀_le : r₀ ≤ m := by have := Finset.mem_range.mp hr₀; omega
        have hsplit := Finset.add_sum_erase (Finset.range (m + 1))
          (fun r => ((Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
            successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j)))).card) hr₀
        have hr₀_le_sub := (hsub_hit r₀ hr₀_le).2 hbig
        have hrest_le : ∑ r ∈ (Finset.range (m + 1)).erase r₀,
            ((Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
              successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j)))).card ≤ m * (price rest).1 := by
          calc ∑ r ∈ (Finset.range (m + 1)).erase r₀,
                ((Finset.Ico (pts r) (pts (r + 1))).filter (fun j =>
                  successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j)))).card
              ≤ ∑ _r ∈ (Finset.range (m + 1)).erase r₀, (price rest).1 :=
                Finset.sum_le_sum (fun r hr =>
                  (hsub_hit r (by have := Finset.mem_range.mp (Finset.mem_erase.mp hr).2; omega)).1)
            _ = m * (price rest).1 := by
                rw [Finset.sum_const, Finset.card_erase_of_mem hr₀, Finset.card_range, smul_eq_mul]
                simp
        have hPpos := price_fst_pos rest
        have hm_exp : (m + 1) * (price rest).1 = m * (price rest).1 + (price rest).1 := by ring
        have hm_le_B : (m + 1) * (price rest).1 ≤ (price (k :: rest)).2 :=
          (Nat.mul_le_mul_right _ hm1_le_k).trans hkP_le_B
        omega
      rw [hpart_fib]
      calc ((Finset.univ : Finset G).biUnion (fun g₀ =>
            ((Finset.range n).filter (fun j =>
              successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j)))).image
              (fun j => wordAt hn f u₀ g₀ (shift hn u₀ j)))).card
          ≤ ∑ g₀ : G, (((Finset.range n).filter (fun j =>
              successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j)))).image
              (fun j => wordAt hn f u₀ g₀ (shift hn u₀ j))).card := Finset.card_biUnion_le
        _ ≤ ∑ g₀ : G, ((Finset.range n).filter (fun j =>
              successPred hn f (k :: rest) probe (wordAt hn f u₀ g₀ (shift hn u₀ j)))).card :=
            Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
        _ ≤ ∑ _g₀ : G, ((price (k :: rest)).2 - 1) := Finset.sum_le_sum (fun g₀ _ => hfiber_le g₀)
        _ = ((price (k :: rest)).2 - 1) * Fintype.card G := by simp [mul_comm]

private def coarsePos (n B idx : ℕ) : ℕ :=
  if n ≤ B then min idx n else if idx < B then idx else n

private lemma coarsePos_le_n (n B idx : ℕ) : coarsePos n B idx ≤ n := by
  dsimp only [coarsePos]
  split_ifs <;> omega

private lemma coarsePos_mono (n B : ℕ) {i j : ℕ} (hij : i ≤ j) :
    coarsePos n B i ≤ coarsePos n B j := by
  dsimp only [coarsePos]
  split_ifs <;> omega

private lemma coarsePos_not_in_stretch {n B idx : ℕ} (hBn : B < n) (hidx : idx ≤ B) :
    ¬(B - 1 < coarsePos n B idx ∧ coarsePos n B idx < n) := by
  dsimp only [coarsePos]
  rw [if_neg (by omega : ¬(n ≤ B))]
  split_ifs <;> omega

private lemma coarsePos_unit {n B j : ℕ} (hj : j < if n ≤ B then n else B - 1) :
    coarsePos n B j = j ∧ coarsePos n B (j + 1) = j + 1 := by
  dsimp only [coarsePos]
  split_ifs at hj ⊢ <;> omega

open Classical in
private noncomputable def searchCoarse {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (B : ℕ) (u₀ : Fin n) (g₀ : G) :
    ∀ (rest : List ℕ) (L R : ℕ), Strategy n G
  | [], _, _ => fun _ => ∅
  | k :: tl, L, R =>
      let P := (price tl).1
      let Q : Finset (Fin n) :=
        (Finset.range k).image (fun i => shift hn u₀ (coarsePos n B (min (L + (i + 1) * P) R)))
      consStrategy Q (fun ans =>
        let r := ((Finset.range k).filter (fun i =>
          let d := coarsePos n B (min (L + (i + 1) * P) R)
          (shift hn u₀ d, g₀ * arcProd hn f u₀ d) ∈ ans)).card
        searchCoarse hn f B u₀ g₀ tl (min (L + r * P) R) (min (L + (r + 1) * P) R))

private lemma searchCoarse_legal {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (B : ℕ) (u₀ : Fin n) (g₀ : G) :
    ∀ (rest : List ℕ) (L R : ℕ), legal rest (searchCoarse hn f B u₀ g₀ rest L R) := by
  intro rest
  induction rest with
  | nil => intro L R word j; exact False.elim (Nat.not_lt_zero _ j.isLt)
  | cons k tl ih =>
    intro L R word j
    rcases j with ⟨jv, hjv⟩
    cases jv with
    | zero =>
      simp only [searchCoarse, batch_consStrategy_zero, List.getElem_cons_zero]
      calc ((Finset.range k).image _).card ≤ (Finset.range k).card := Finset.card_image_le
        _ = k := Finset.card_range k
    | succ jv =>
      simp only [searchCoarse, batch_consStrategy_succ, List.getElem_cons_succ]
      exact ih _ _ word ⟨jv, by simpa using hjv⟩

private lemma searchCoarse_only_coarse {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (B : ℕ) (u₀ : Fin n) (g₀ : G) :
    ∀ (rest : List ℕ) (L R : ℕ), R ≤ B → ∀ (x : Fin n → G) (w : Fin n),
      w ∈ seenOf rest (searchCoarse hn f B u₀ g₀ rest L R) x →
      ∃ idx ≤ B, w = shift hn u₀ (coarsePos n B idx) := by
  intro rest
  induction rest with
  | nil => intro L R _ x w hw; simp [seenOf] at hw
  | cons k tl ih =>
    intro L R hRB x w hw
    simp only [seenOf, List.length_cons, Finset.mem_biUnion, Finset.mem_range] at hw
    rcases hw with ⟨i, hi, hwi⟩
    cases i with
    | zero =>
      simp only [searchCoarse, batch_consStrategy_zero, Finset.mem_image, Finset.mem_range] at hwi
      rcases hwi with ⟨j, _, rfl⟩
      exact ⟨min (L + (j + 1) * (price tl).1) R, (Nat.min_le_right _ _).trans hRB, rfl⟩
    | succ i =>
      simp only [searchCoarse, batch_consStrategy_succ] at hwi
      exact ih _ _ ((Nat.min_le_right _ _).trans hRB) x w
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (by omega), hwi⟩)

private lemma searchCoarse_hits {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (hf : (List.ofFn f).prod ≠ 1) (B : ℕ) (u₀ : Fin n) (g₀ : G) :
    ∀ (rest : List ℕ) (L R j : ℕ),
      R ≤ B → R - L ≤ (price rest).1 → L ≤ j → j < R →
      coarsePos n B j < coarsePos n B (j + 1) →
      let x := wordAt hn f u₀ g₀ (shift hn u₀ (coarsePos n B j))
      let S := seenOf rest (searchCoarse hn f B u₀ g₀ rest L R) x ∪
        {shift hn u₀ (coarsePos n B L), shift hn u₀ (coarsePos n B R)}
      shift hn u₀ (coarsePos n B j) ∈ S ∧ shift hn u₀ (coarsePos n B (j + 1)) ∈ S := by
  intro rest
  induction rest with
  | nil =>
    intro L R j _ hlen hLj hjR _
    have hL_eq : L = j := by simp [price] at hlen; omega
    have hR_eq : R = j + 1 := by simp [price] at hlen; omega
    subst hL_eq hR_eq
    simp
  | cons k tl ih =>
    intro L R j hRB hlen hLj hjR hj_strict
    set P := (price tl).1
    have hPpos : 1 ≤ P := price_fst_pos tl
    set x := wordAt hn f u₀ g₀ (shift hn u₀ (coarsePos n B j))
    set Q : Finset (Fin n) :=
      (Finset.range k).image (fun i => shift hn u₀ (coarsePos n B (min (L + (i + 1) * P) R)))
    set ans := Q.image (fun u => (u, x u))
    set r := ((Finset.range k).filter (fun i =>
      let d := coarsePos n B (min (L + (i + 1) * P) R)
      (shift hn u₀ d, g₀ * arcProd hn f u₀ d) ∈ ans)).card
    have hj_lt_n : coarsePos n B j < n :=
      lt_of_lt_of_le hj_strict (coarsePos_le_n n B (j + 1))
    have hdist_j : cycDist u₀ (shift hn u₀ (coarsePos n B j)) = coarsePos n B j :=
      cycDist_shift hn u₀ hj_lt_n
    have hcheck_i : ∀ i < k,
        ((shift hn u₀ (coarsePos n B (min (L + (i + 1) * P) R)),
          g₀ * arcProd hn f u₀ (coarsePos n B (min (L + (i + 1) * P) R))) ∈ ans) ↔
        L + (i + 1) * P ≤ j := by
      intro i hi
      set idx := min (L + (i + 1) * P) R
      set d := coarsePos n B idx
      have hd_le_n : d ≤ n := coarsePos_le_n n B idx
      have hmemQ : shift hn u₀ d ∈ Q := Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
      have hiff_eq : (shift hn u₀ d, g₀ * arcProd hn f u₀ d) ∈ ans ↔
          x (shift hn u₀ d) = g₀ * arcProd hn f u₀ d := by
        simp only [ans, Finset.mem_image]
        constructor
        · rintro ⟨u, _, hu⟩
          have h1 : u = shift hn u₀ d := congrArg Prod.fst hu
          have h2 : x u = g₀ * arcProd hn f u₀ d := congrArg Prod.snd hu
          rwa [← h1]
        · intro heq; exact ⟨shift hn u₀ d, hmemQ, Prod.ext rfl heq⟩
      rw [hiff_eq]
      by_cases hle : L + (i + 1) * P ≤ j
      · have hidx_le : idx ≤ j := (Nat.min_le_left _ _).trans hle
        have hd_le : d ≤ coarsePos n B j := coarsePos_mono n B hidx_le
        have hx_eq := wordAt_val_before hn f hf u₀ g₀ (shift hn u₀ (coarsePos n B j)) (d := d) (by rw [hdist_j]; exact hd_le)
        exact ⟨fun _ => hle, fun _ => hx_eq⟩
      · have hgt : j + 1 ≤ idx := by omega
        have hd_gt : coarsePos n B j < d := lt_of_lt_of_le hj_strict (coarsePos_mono n B hgt)
        have hx_eq := wordAt_val_after hn f hf u₀ g₀ (shift hn u₀ (coarsePos n B j)) (d := d) (by rw [hdist_j]; exact hd_gt) hd_le_n
        have hne := wordAt_before_ne_after hn f hf u₀ g₀ hd_le_n
        exact ⟨fun heq => False.elim (hne (heq.symm.trans hx_eq)), fun h => False.elim (hle h)⟩
    have hr_val : r = (j - L) / P := by
      have hfilt : (Finset.range k).filter (fun i =>
          let d := coarsePos n B (min (L + (i + 1) * P) R)
          (shift hn u₀ d, g₀ * arcProd hn f u₀ d) ∈ ans) = Finset.range ((j - L) / P) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hi, hmem⟩
          have hle := (hcheck_i i hi).mp hmem
          have hsub : (i + 1) * P ≤ j - L := by omega
          have hdiv := Nat.div_le_div_right (c := P) hsub
          rw [Nat.mul_div_cancel _ (by omega)] at hdiv
          omega
        · intro hilt
          have hq_le : (j - L) / P ≤ k := by
            have hlen' : R - L ≤ (k + 1) * P := by simpa [price_cons, P] using hlen
            have h1 : j - L < (k + 1) * P := by omega
            have h2 := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at h1)
            omega
          have hi : i < k := by omega
          refine ⟨hi, (hcheck_i i hi).mpr ?_⟩
          have h1 : i + 1 ≤ (j - L) / P := by omega
          have h2 : (i + 1) * P ≤ ((j - L) / P) * P := Nat.mul_le_mul_right P h1
          have h3 : ((j - L) / P) * P ≤ j - L := by rw [mul_comm]; exact Nat.mul_div_le (j - L) P
          omega
      dsimp only [r]
      rw [hfilt, Finset.card_range]
    have hL' : min (L + r * P) R ≤ j := by
      have h1 : r * P ≤ j - L := by rw [hr_val, mul_comm]; exact Nat.mul_div_le (j - L) P
      exact (Nat.min_le_left _ _).trans (by omega)
    have hjR' : j < min (L + (r + 1) * P) R := by
      have hdm := Nat.div_add_mod (j - L) P
      have hmod := Nat.mod_lt (j - L) (by omega : 0 < P)
      have h1 : j - L < (r + 1) * P := by rw [hr_val]; nlinarith
      exact lt_min (by omega) hjR
    have hlen' : min (L + (r + 1) * P) R - min (L + r * P) R ≤ P := by
      have : L + (r + 1) * P = L + r * P + P := by ring
      rw [this]; omega
    have hih := ih (min (L + r * P) R) (min (L + (r + 1) * P) R) j
      ((Nat.min_le_right _ _).trans hRB) hlen' hL' hjR' hj_strict
    have hsub : seenOf tl (searchCoarse hn f B u₀ g₀ tl (min (L + r * P) R) (min (L + (r + 1) * P) R)) x ∪
          {shift hn u₀ (coarsePos n B (min (L + r * P) R)), shift hn u₀ (coarsePos n B (min (L + (r + 1) * P) R))} ⊆
        seenOf (k :: tl) (searchCoarse hn f B u₀ g₀ (k :: tl) L R) x ∪
          {shift hn u₀ (coarsePos n B L), shift hn u₀ (coarsePos n B R)} := by
      intro w hw
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      rcases hw with htl | rfl | rfl
      · left
        simp only [seenOf, List.length_cons, Finset.mem_biUnion, Finset.mem_range] at htl ⊢
        rcases htl with ⟨i, hi, hwi⟩
        refine ⟨i + 1, by omega, ?_⟩
        simp only [searchCoarse, batch_consStrategy_succ]
        exact hwi
      · by_cases hr0 : r = 0
        · right; left
          have hLle : L ≤ R := by omega
          simp [hr0, min_eq_left hLle]
        · left
          simp only [seenOf, List.length_cons, Finset.mem_biUnion, Finset.mem_range]
          refine ⟨0, by omega, ?_⟩
          simp only [searchCoarse, batch_consStrategy_zero, Finset.mem_image, Finset.mem_range]
          have hr_le_k : r ≤ k := (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
          refine ⟨r - 1, by omega, ?_⟩
          rw [show r - 1 + 1 = r by omega]
      · by_cases hrlast : r < k
        · left
          simp only [seenOf, List.length_cons, Finset.mem_biUnion, Finset.mem_range]
          refine ⟨0, by omega, ?_⟩
          simp only [searchCoarse, batch_consStrategy_zero, Finset.mem_image, Finset.mem_range]
          exact ⟨r, hrlast, rfl⟩
        · right; right
          have hr_eq : r = k := by
            have hle : r ≤ k := (Finset.card_filter_le (Finset.range k) _).trans (by rw [Finset.card_range])
            omega
          have hlen_c : R - L ≤ (k + 1) * P := by simpa [price_cons, P] using hlen
          have hgeR : R ≤ L + (r + 1) * P := by rw [hr_eq]; omega
          rw [min_eq_right hgeR]
    exact ⟨hsub hih.1, hsub hih.2⟩

open Classical in
private noncomputable def buildLower {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (u₀ : Fin n) :
    ∀ (bs : List ℕ), Strategy n G
  | [] => fun _ => ∅
  | k :: rest =>
      let B := (price (k :: rest)).2
      let P := (price rest).1
      if B < 2 then fun _ => ∅
      else if k * P = B then
        let Q : Finset (Fin n) := (Finset.range k).image (fun i => shift hn u₀ (coarsePos n B (i * P)))
        consStrategy Q (fun ans =>
          let g₀ := if h : ∃ g : G, (u₀, g) ∈ ans then Classical.choose h else 1
          let r := ((Finset.range (k - 1)).filter (fun i =>
            let d := coarsePos n B ((i + 1) * P)
            (shift hn u₀ d, g₀ * arcProd hn f u₀ d) ∈ ans)).card
          searchCoarse hn f B u₀ g₀ rest (r * P) ((r + 1) * P))
      else
        consStrategy ∅ (fun _ => buildLower hn f u₀ rest)

private lemma buildLower_legal {n : ℕ} (hn : 0 < n) {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (u₀ : Fin n) :
    ∀ bs : List ℕ, legal bs (buildLower hn f u₀ bs) := by
  intro bs
  induction bs with
  | nil => intro word j; exact False.elim (Nat.not_lt_zero _ j.isLt)
  | cons k rest ih =>
    dsimp only [buildLower]
    split_ifs with h1 h2
    · intro word j; simp [batch]
    · intro word j
      rcases j with ⟨jv, hjv⟩
      cases jv with
      | zero =>
        simp only [batch_consStrategy_zero, List.getElem_cons_zero]
        calc ((Finset.range k).image _).card ≤ (Finset.range k).card := Finset.card_image_le
          _ = k := Finset.card_range k
      | succ jv =>
        simp only [batch_consStrategy_succ, List.getElem_cons_succ]
        exact searchCoarse_legal hn f _ u₀ _ rest _ _ word ⟨jv, by simpa using hjv⟩
    · intro word j
      rcases j with ⟨jv, hjv⟩
      cases jv with
      | zero => simp [batch_consStrategy_zero]
      | succ jv =>
        simp only [batch_consStrategy_succ, List.getElem_cons_succ]
        exact ih word ⟨jv, by simpa using hjv⟩

open Classical in
private lemma buildLower_iff {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n)
    {G : Type} [Group G] [DecidableEq G]
    (f : Fin n → G) (hf : (List.ofFn f).prod ≠ 1) (u₀ : Fin n) :
    ∀ (bs : List ℕ) (x : Fin n → G) (e : Fin n),
      faults hn f x = {e} →
      (successPred hn f bs (buildLower hn f u₀ bs) x ↔
        cycDist u₀ e < if n ≤ (price bs).2 then n else (price bs).2 - 1) := by
  intro bs
  induction bs with
  | nil =>
    intro x e _
    simp [successPred, seenOf, price, Nat.ne_of_gt hn]
  | cons k rest ih =>
    intro x e hfault
    set B := (price (k :: rest)).2
    set P := (price rest).1
    have hPpos : 1 ≤ P := price_fst_pos rest
    have hB_def : B = max (k * P) (price rest).2 := rfl
    by_cases hB2 : B < 2
    · have hgoal : (if n ≤ B then n else B - 1) = 0 := by
        rw [if_neg (by omega)]; omega
      have hstrat : buildLower hn f u₀ (k :: rest) = fun _ => ∅ := by
        dsimp only [buildLower]; rw [if_pos hB2]
      rw [hstrat, hgoal]
      simp [successPred, seenOf, batch]
    · by_cases hkPB : k * P = B
      · have hstrat : buildLower hn f u₀ (k :: rest) =
            consStrategy ((Finset.range k).image (fun i => shift hn u₀ (coarsePos n B (i * P))))
              (fun ans =>
                let g₀ := if h : ∃ g : G, (u₀, g) ∈ ans then Classical.choose h else 1
                let r := ((Finset.range (k - 1)).filter (fun i =>
                  let d := coarsePos n B ((i + 1) * P)
                  (shift hn u₀ d, g₀ * arcProd hn f u₀ d) ∈ ans)).card
                searchCoarse hn f B u₀ g₀ rest (r * P) ((r + 1) * P)) := by
          dsimp only [buildLower]; rw [if_neg hB2, if_pos hkPB]
        rw [hstrat]
        have hk_pos : 1 ≤ k := by
          by_contra h0
          have hk0 : k = 0 := by omega
          have hB0 : B = 0 := by rw [← hkPB, hk0, zero_mul]
          omega
        set Q : Finset (Fin n) := (Finset.range k).image (fun i => shift hn u₀ (coarsePos n B (i * P)))
        set ans := Q.image (fun u => (u, x u))
        have hu₀Q : u₀ ∈ Q := by
          refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
          have hBpos : 0 < B := by omega
          simp [coarsePos, hBpos, shift_zero]
        have hg₀_eq : (if h : ∃ g : G, (u₀, g) ∈ ans then Classical.choose h else 1) = x u₀ := by
          have hex : ∃ g : G, (u₀, g) ∈ ans := ⟨x u₀, Finset.mem_image.mpr ⟨u₀, hu₀Q, rfl⟩⟩
          rw [dif_pos hex]
          rcases Finset.mem_image.mp (Classical.choose_spec hex) with ⟨w, _, hw⟩
          have h1 : w = u₀ := congrArg Prod.fst hw
          have h2 : x w = Classical.choose hex := congrArg Prod.snd hw
          rw [← h2, h1]
        set g₀ := x u₀
        have hx_eq : x = wordAt hn f u₀ g₀ e := eq_wordAt_of_private hn f hf u₀ x e hfault
        set j := cycDist u₀ e
        have hj_lt : j < n := cycDist_lt hn u₀ e
        have he_eq : shift hn u₀ j = e := shift_cycDist hn u₀ e
        set r := ((Finset.range (k - 1)).filter (fun i =>
          let d := coarsePos n B ((i + 1) * P)
          (shift hn u₀ d, g₀ * arcProd hn f u₀ d) ∈ ans)).card
        have hr_le : r ≤ k - 1 := (Finset.card_filter_le _ _).trans (by simp)
        have hr1_le_B : (r + 1) * P ≤ B := by
          rw [← hkPB]; exact Nat.mul_le_mul_right P (by omega)
        have hseen_eq : seenOf (k :: rest) (consStrategy Q (fun a =>
            let g := if h : ∃ g : G, (u₀, g) ∈ a then Classical.choose h else 1
            let r' := ((Finset.range (k - 1)).filter (fun i =>
              let d := coarsePos n B ((i + 1) * P)
              (shift hn u₀ d, g * arcProd hn f u₀ d) ∈ a)).card
            searchCoarse hn f B u₀ g rest (r' * P) ((r' + 1) * P))) x =
            Q ∪ seenOf rest (searchCoarse hn f B u₀ g₀ rest (r * P) ((r + 1) * P)) x := by
          ext w
          simp only [seenOf, List.length_cons, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
          constructor
          · rintro ⟨i, hi, hw⟩
            cases i with
            | zero => simp only [batch_consStrategy_zero] at hw; exact Or.inl hw
            | succ i =>
              simp only [batch_consStrategy_succ] at hw
              change w ∈ batch (searchCoarse hn f B u₀ _ rest _ _) x i at hw
              have hrepl : (if h : ∃ g : G, (u₀, g) ∈ ans then Classical.choose h else 1) = g₀ := hg₀_eq
              simp only [← show ans = Q.image (fun u => (u, x u)) from rfl, hrepl] at hw
              exact Or.inr ⟨i, by omega, hw⟩
          · rintro (hQ | ⟨i, hi, hw⟩)
            · exact ⟨0, by omega, by simpa [batch_consStrategy_zero] using hQ⟩
            · refine ⟨i + 1, by omega, ?_⟩
              simp only [batch_consStrategy_succ]
              have hrepl : (if h : ∃ g : G, (u₀, g) ∈ ans then Classical.choose h else 1) = g₀ := hg₀_eq
              simpa [← show ans = Q.image (fun u => (u, x u)) from rfl, hrepl] using hw
        simp only [successPred, hfault, Finset.mem_singleton, exists_eq_left, hseen_eq]
        constructor
        · rintro ⟨he_in, hne_in⟩
          by_contra hge
          push_neg at hge
          have hBn : B < n := by
            by_contra hle
            rw [if_pos (by omega : n ≤ B)] at hge
            omega
          rw [if_neg (by omega : ¬(n ≤ B))] at hge
          have hnot_stretch : ∀ w ∈ Q ∪ seenOf rest (searchCoarse hn f B u₀ g₀ rest (r * P) ((r + 1) * P)) x,
              ¬(B - 1 < cycDist u₀ w ∧ cycDist u₀ w < n) := by
            intro w hw
            have hex_idx : ∃ idx ≤ B, w = shift hn u₀ (coarsePos n B idx) := by
              rcases Finset.mem_union.mp hw with hQ | hS
              · rcases Finset.mem_image.mp hQ with ⟨i, hi, rfl⟩
                have hi' := Finset.mem_range.mp hi
                exact ⟨i * P, by rw [← hkPB]; exact Nat.mul_le_mul_right P (by omega), rfl⟩
              · exact searchCoarse_only_coarse hn f B u₀ g₀ rest (r * P) ((r + 1) * P) hr1_le_B x w hS
            rcases hex_idx with ⟨idx, hidx, rfl⟩
            have hns := coarsePos_not_in_stretch hBn hidx
            by_cases hlt_n : coarsePos n B idx < n
            · rw [cycDist_shift hn u₀ hlt_n]; exact hns
            · have heqn : coarsePos n B idx = n := le_antisymm (coarsePos_le_n n B idx) (by omega)
              rw [heqn, shift_n, cycDist_self hn u₀]
              omega
          by_cases hjeq : j = B - 1
          · have hnext_dist : cycDist u₀ (nextPos hn e) = B := by
              rw [← he_eq, ← shift_succ, hjeq, show B - 1 + 1 = B by omega, cycDist_shift hn u₀ hBn]
            have := hnot_stretch (nextPos hn e) hne_in
            rw [hnext_dist] at this
            omega
          · have := hnot_stretch e he_in
            omega
        · intro hj_lt_c
          have hunit := coarsePos_unit (n := n) (B := B) hj_lt_c
          have hj_lt_B : j < B := by split_ifs at hj_lt_c <;> omega
          have hcheck_i : ∀ i < k - 1,
              ((shift hn u₀ (coarsePos n B ((i + 1) * P)),
                g₀ * arcProd hn f u₀ (coarsePos n B ((i + 1) * P))) ∈ ans) ↔
              (i + 1) * P ≤ j := by
            intro i hi
            set d := coarsePos n B ((i + 1) * P)
            have hd_le_n : d ≤ n := coarsePos_le_n n B _
            have hmemQ : shift hn u₀ d ∈ Q := Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr (by omega), rfl⟩
            have hiff_eq : (shift hn u₀ d, g₀ * arcProd hn f u₀ d) ∈ ans ↔
                x (shift hn u₀ d) = g₀ * arcProd hn f u₀ d := by
              simp only [ans, Finset.mem_image]
              constructor
              · rintro ⟨u, _, hu⟩
                have h1 : u = shift hn u₀ d := congrArg Prod.fst hu
                have h2 : x u = g₀ * arcProd hn f u₀ d := congrArg Prod.snd hu
                rwa [← h1]
              · intro heq; exact ⟨shift hn u₀ d, hmemQ, Prod.ext rfl heq⟩
            rw [hiff_eq, hx_eq]
            by_cases hle : (i + 1) * P ≤ j
            · have hd_le : d ≤ j := by
                have := coarsePos_mono n B hle
                rwa [hunit.1] at this
              exact ⟨fun _ => hle, fun _ => wordAt_val_before hn f hf u₀ g₀ e hd_le⟩
            · have hgt : j + 1 ≤ (i + 1) * P := by omega
              have hd_gt : j < d := by
                have := coarsePos_mono n B hgt
                rw [hunit.2] at this
                omega
              have hx_a := wordAt_val_after hn f hf u₀ g₀ e hd_gt hd_le_n
              have hne := wordAt_before_ne_after hn f hf u₀ g₀ hd_le_n
              exact ⟨fun heq => False.elim (hne (heq.symm.trans hx_a)), fun h => False.elim (hle h)⟩
          have hr_val : r = j / P := by
            have hfilt : (Finset.range (k - 1)).filter (fun i =>
                let d := coarsePos n B ((i + 1) * P)
                (shift hn u₀ d, g₀ * arcProd hn f u₀ d) ∈ ans) = Finset.range (j / P) := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_range]
              constructor
              · rintro ⟨hi, hmem⟩
                have hle := (hcheck_i i hi).mp hmem
                have hdiv := Nat.div_le_div_right (c := P) hle
                rw [Nat.mul_div_cancel _ (by omega)] at hdiv
                omega
              · intro hilt
                have hdiv_lt : j / P < k := by
                  have h1 : j < k * P := by rw [hkPB]; exact hj_lt_B
                  exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at h1)
                have hi : i < k - 1 := by omega
                refine ⟨hi, (hcheck_i i hi).mpr ?_⟩
                have h1 : i + 1 ≤ j / P := by omega
                have h2 : (i + 1) * P ≤ (j / P) * P := Nat.mul_le_mul_right P h1
                have h3 : (j / P) * P ≤ j := by rw [mul_comm]; exact Nat.mul_div_le j P
                omega
            dsimp only [r]
            rw [hfilt, Finset.card_range]
          have hL : r * P ≤ j := by rw [hr_val, mul_comm]; exact Nat.mul_div_le j P
          have hR : j < (r + 1) * P := by
            have hdm := Nat.div_add_mod j P
            have hmod := Nat.mod_lt j (by omega : 0 < P)
            rw [hr_val]; nlinarith
          have hlen_r : (r + 1) * P - r * P ≤ P := by
            have : (r + 1) * P = r * P + P := by ring
            omega
          have hhit := searchCoarse_hits hn f hf B u₀ g₀ rest (r * P) ((r + 1) * P) j
            hr1_le_B hlen_r hL hR (by rw [hunit.1, hunit.2]; omega)
          rw [hunit.1, he_eq, ← hx_eq] at hhit
          have hsub : seenOf rest (searchCoarse hn f B u₀ g₀ rest (r * P) ((r + 1) * P)) x ∪
                {shift hn u₀ (coarsePos n B (r * P)), shift hn u₀ (coarsePos n B ((r + 1) * P))} ⊆
              Q ∪ seenOf rest (searchCoarse hn f B u₀ g₀ rest (r * P) ((r + 1) * P)) x := by
            intro w hw
            simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
            rcases hw with hS | rfl | rfl
            · exact Or.inr hS
            · left; exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr (by omega), rfl⟩
            · left
              by_cases hrlast : r + 1 < k
              · exact Finset.mem_image.mpr ⟨r + 1, Finset.mem_range.mpr hrlast, rfl⟩
              · have hreq : (r + 1) * P = B := by
                  rw [← hkPB]; congr 1; omega
                rw [hreq]
                have hposB : coarsePos n B B = n := by
                  dsimp only [coarsePos]; split_ifs <;> omega
                rw [hposB, shift_n]
                exact hu₀Q
          have h1 := hsub hhit.1
          have h2 := hsub hhit.2
          rw [hunit.2, shift_succ, he_eq] at h2
          exact ⟨h1, h2⟩
      · have hB_eq_rest : B = (price rest).2 := by
          have := hB_def
          omega
        have hstrat : buildLower hn f u₀ (k :: rest) = consStrategy ∅ (fun _ => buildLower hn f u₀ rest) := by
          dsimp only [buildLower]; rw [if_neg hB2, if_neg hkPB]
        rw [hstrat]
        have hseen_eq : seenOf (k :: rest) (consStrategy ∅ (fun _ => buildLower hn f u₀ rest)) x =
            seenOf rest (buildLower hn f u₀ rest) x := by
          ext w
          simp only [seenOf, List.length_cons, Finset.mem_biUnion, Finset.mem_range]
          constructor
          · rintro ⟨i, hi, hw⟩
            cases i with
            | zero => simp [batch_consStrategy_zero] at hw
            | succ i =>
              simp only [batch_consStrategy_succ] at hw
              exact ⟨i, by omega, hw⟩
          · rintro ⟨i, hi, hw⟩
            refine ⟨i + 1, by omega, ?_⟩
            simpa [batch_consStrategy_succ] using hw
        have hih' := ih x e hfault
        simp only [successPred, hseen_eq] at hih' ⊢
        rwa [← hB_eq_rest] at hih'

private lemma cycDist_count_lt {n : ℕ} (hn : 0 < n) (e : Fin n) (c : ℕ) (hc : c ≤ n) :
    (Finset.univ.filter (fun offset : Fin n => cycDist offset e < c)).card = c := by
  have hbij : Finset.univ.filter (fun offset : Fin n => cycDist offset e < c) =
      (Finset.range c).attach.image (fun d =>
        ⟨(e.val + n - d.val) % n, Nat.mod_lt _ hn⟩) := by
    ext offset
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_attach, Subtype.exists, Finset.mem_range]
    constructor
    · intro hlt
      refine ⟨cycDist offset e, hlt, ?_⟩
      apply Fin.ext
      dsimp only [cycDist]
      have h1 : (e.val + n - offset.val) % n = if offset.val ≤ e.val then e.val - offset.val else e.val + n - offset.val := by
        by_cases hle : offset.val ≤ e.val
        · rw [if_pos hle, show e.val + n - offset.val = (e.val - offset.val) + n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by have := e.isLt; omega)]
        · rw [if_neg hle, Nat.mod_eq_of_lt (by have := e.isLt; have := offset.isLt; omega)]
      rw [h1]
      split_ifs with hle
      · rw [show e.val + n - (e.val - offset.val) = offset.val + n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt offset.isLt]
      · rw [show e.val + n - (e.val + n - offset.val) = offset.val by omega,
          Nat.mod_eq_of_lt offset.isLt]
    · rintro ⟨d, hd, rfl⟩
      have hdn : d < n := lt_of_lt_of_le hd hc
      have h1 : cycDist ⟨(e.val + n - d) % n, Nat.mod_lt _ hn⟩ e = d := by
        dsimp only [cycDist]
        have h2 : (e.val + n - d) % n = if d ≤ e.val then e.val - d else e.val + n - d := by
          by_cases hle : d ≤ e.val
          · rw [if_pos hle, show e.val + n - d = (e.val - d) + n by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by have := e.isLt; omega)]
          · rw [if_neg hle, Nat.mod_eq_of_lt (by have := e.isLt; omega)]
        rw [h2]
        split_ifs with hle
        · rw [show e.val + n - (e.val - d) = d + n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt hdn]
        · rw [show e.val + n - (e.val + n - d) = d by omega,
            Nat.mod_eq_of_lt hdn]
      rw [h1]; exact hd
  rw [hbij, Finset.card_image_of_injective]
  · simp
  · intro d₁ d₂ heq
    have h1 := congrArg (fun off => cycDist off e) heq
    have hc_fn : ∀ d : {x // x ∈ Finset.range c},
        cycDist ⟨(e.val + n - d.val) % n, Nat.mod_lt _ hn⟩ e = d.val := by
      intro d
      have hd : d.val < c := Finset.mem_range.mp d.2
      have hdn : d.val < n := lt_of_lt_of_le hd hc
      dsimp only [cycDist]
      have h2 : (e.val + n - d.val) % n = if d.val ≤ e.val then e.val - d.val else e.val + n - d.val := by
        by_cases hle : d.val ≤ e.val
        · rw [if_pos hle, show e.val + n - d.val = (e.val - d.val) + n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by have := e.isLt; omega)]
        · rw [if_neg hle, Nat.mod_eq_of_lt (by have := e.isLt; omega)]
      rw [h2]
      split_ifs with hle
      · rw [show e.val + n - (e.val - d.val) = d.val + n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hdn]
      · rw [show e.val + n - (e.val + n - d.val) = d.val by omega,
          Nat.mod_eq_of_lt hdn]
    rw [hc_fn d₁, hc_fn d₂] at h1
    exact Subtype.ext h1

end PEqualNP.Outside.L_pcx_260

theorem PEqualNP.Outside.L_pcx_260 :
  ∀ (n : ℕ) (hn : 0 < n), 2 ≤ n →
    ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (f : Fin n → G),
    (List.ofFn f).prod ≠ 1 →
    let next := fun pos : Fin n => (⟨(pos.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n)
    let faults := fun assignment : Fin n → G =>
      Finset.univ.filter (fun site => assignment (next site) ≠ assignment site * f site)
    let Strategy := List (Finset (Fin n × G)) → Finset (Fin n)
    let history := fun (ask : Strategy) (x : Fin n → G) (t : ℕ) =>
      (List.range t).foldl (fun hist _ => hist ++ [(ask hist).image (fun u => (u, x u))]) []
    let batch := fun (ask : Strategy) (x : Fin n → G) (i : ℕ) => ask (history ask x i)
    let price := fun bs : List ℕ => bs.foldr
      (fun k (p : ℕ × ℕ) => ((k+1)*p.1, max (k*p.1) p.2)) (1,0)
    ∀ bs : List ℕ,
      let B := (price bs).2
      let c := if n ≤ B then n else B-1
      let legal := fun rule : Strategy => ∀ (word : Fin n → G) (j : Fin bs.length),
        (batch rule word j.val).card ≤ bs[j.val]'j.isLt
      let success := fun (search : Strategy) (values : Fin n → G) =>
        let seen := (Finset.range bs.length).biUnion (batch search values)
        ∃ edge ∈ faults values, edge ∈ seen ∧ next edge ∈ seen
      let privateWords := Finset.univ.filter (fun input : Fin n → G => (faults input).card = 1)
      privateWords.card = n * Fintype.card G ∧
      (∀ probe, legal probe →
        (privateWords.filter (fun candidate => decide (success probe candidate))).card ≤ c * Fintype.card G) ∧
      ∃ family : Fin n → Strategy, (∀ rotation, legal (family rotation)) ∧
        ∀ privateWord ∈ privateWords,
          (Finset.univ.filter (fun offset => decide (success (family offset) privateWord))).card = c := by
  intro n hn hn2 G _ _ _ f hf next faults Strategy history batch price bs B c legal success privateWords
  have hcard : privateWords.card = n * Fintype.card G :=
    PEqualNP.Outside.L_pcx_260.privateWords_card hn f hf
  refine ⟨hcard, ?_, ?_⟩
  · intro probe hleg
    by_cases hle : n ≤ B
    · have hc : c = n := if_pos hle
      rw [hc, ← hcard]
      exact Finset.card_filter_le _ _
    · have hc : c = B - 1 := if_neg hle
      have hBn : (PEqualNP.Outside.L_pcx_260.price bs).2 < n := by
        change ¬n ≤ (PEqualNP.Outside.L_pcx_260.price bs).2 at hle
        omega
      rw [hc]
      exact PEqualNP.Outside.L_pcx_260.upper_unpinned hn hn2 f hf bs probe hleg hBn
  · refine ⟨fun offset => PEqualNP.Outside.L_pcx_260.buildLower hn f offset bs,
      fun offset => PEqualNP.Outside.L_pcx_260.buildLower_legal hn f offset bs, ?_⟩
    intro pw hpw
    have hcard1 : (PEqualNP.Outside.L_pcx_260.faults hn f pw).card = 1 :=
      (Finset.mem_filter.mp hpw).2
    rcases Finset.card_eq_one.mp hcard1 with ⟨e, he⟩
    have hfilt_eq : Finset.univ.filter (fun offset : Fin n =>
          decide (success (PEqualNP.Outside.L_pcx_260.buildLower hn f offset bs) pw)) =
        Finset.univ.filter (fun offset : Fin n => PEqualNP.Outside.L_pcx_260.cycDist offset e < c) := by
      apply Finset.filter_congr
      intro offset _
      simp only [decide_eq_true_eq]
      exact PEqualNP.Outside.L_pcx_260.buildLower_iff hn hn2 f hf offset bs pw e he
    rw [hfilt_eq]
    have hc_le : c ≤ n := by
      dsimp only [c]
      split_ifs <;> omega
    exact PEqualNP.Outside.L_pcx_260.cycDist_count_lt hn e c hc_le
