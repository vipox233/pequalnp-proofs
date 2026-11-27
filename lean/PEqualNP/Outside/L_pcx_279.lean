import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_481

namespace PEqualNP.Outside.L_pcx_279_aux

abbrev F := ZMod 2

def bit (b : Bool) : F := if b then 1 else 0

def marks {m : ℕ} (D : Finset (Fin m)) (e : Fin m) : F :=
  if e ∈ D then 1 else 0

def support {m : ℕ} (y : Fin m → F) : Finset (Fin m) :=
  Finset.univ.filter fun i => y i = 1

lemma zero_or_one (a : F) : a = 0 ∨ a = 1 := by
  exact (by decide : ∀ x : F, x = 0 ∨ x = 1) a

lemma add_self_zero (a : F) : a + a = 0 := by
  exact (by decide : ∀ x : F, x + x = 0) a

lemma marks_support {m : ℕ} (y : Fin m → F) : marks (support y) = y := by
  funext i
  rcases zero_or_one (y i) with h | h <;> simp [marks, support, h]

def inc {m n : ℕ} (l r : Fin m → Fin n) : Matrix (Fin m) (Fin n) F :=
  fun i v => (if l i = v then 1 else 0) + (if r i = v then 1 else 0)

lemma inc_row {m n : ℕ} (l r : Fin m → Fin n) (x : Fin n → F) (i : Fin m) :
    (inc l r).mulVec x i = x (l i) + x (r i) := by
  simp [inc, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib, ite_mul]

lemma count_marks {m : ℕ} (D : Finset (Fin m)) (p : Fin m → Prop) [DecidablePred p] :
    (∑ e, marks D e * (if p e then 1 else 0)) = ((D.filter p).card : F) := by
  classical
  calc
    _ = ∑ e ∈ D, (if p e then (1 : F) else 0) := by
      simp [marks, ← Finset.sum_filter]
      apply congrArg (fun S : Finset (Fin m) => (S.card : F))
      ext e
      simp [and_comm]
    _ = _ := by simp

lemma inc_col {m n : ℕ} (l r : Fin m → Fin n) (D : Finset (Fin m)) (v : Fin n) :
    (inc l r).vecMul (marks D) v =
      (((D.filter fun e => l e = v).card + (D.filter fun e => r e = v).card : ℕ) : F) := by
  simp only [Matrix.vecMul, dotProduct, inc, mul_add, Finset.sum_add_distrib, Nat.cast_add]
  rw [count_marks, count_marks]

abbrev dep {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) := LinearMap.ker A.vecMulLinear

def form {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (d : Fin m → F) : dep A →+ F where
  toFun y := dotProduct y.val d
  map_zero' := zero_dotProduct _
  map_add' _ _ := add_dotProduct _ _ _

def coord {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (i : Fin m) : dep A →+ F where
  toFun y := y.val i
  map_zero' := rfl
  map_add' _ _ := rfl

lemma attainable {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (b d : Fin m → F) :
    (∃ x, A.mulVec x = b + d) ↔ form A b = form A d := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    ext y
    have hy : A.vecMul y.val = 0 := y.property
    have h : dotProduct y.val b + dotProduct y.val d = 0 := by
      rw [← dotProduct_add, ← hx, Matrix.dotProduct_mulVec, hy, zero_dotProduct]
    exact (by decide : ∀ a b : F, a + b = 0 → a = b) _ _ h
  · intro h
    by_contra hn
    obtain ⟨y, hy, hodd⟩ := (PEqualNP.Outside.L_lib_481 m n A (b+d)).mp hn
    have he := DFunLike.congr_fun h (⟨y, hy⟩ : dep A)
    change dotProduct y b = dotProduct y d at he
    rw [dotProduct_add, he, add_self_zero] at hodd
    exact zero_ne_one hodd

def bad {m n : ℕ} (l r : Fin m → Fin n) (s : Fin m → Bool) (x : Fin n → Bool) :=
  Finset.univ.filter fun i => x (r i) ≠ (x (l i) ^^ s i)

def miss {m n : ℕ} (l r : Fin m → Fin n) (s a : Fin m → Bool) (x : Fin n → Bool) :=
  (bad l r s x).filter fun i => x (l i) = a i

lemma bad_eq_iff {m n : ℕ} (l r : Fin m → Fin n) (s : Fin m → Bool)
    (D : Finset (Fin m)) (x : Fin n → Bool) :
    bad l r s x = D ↔ (inc l r).mulVec (bit ∘ x) = (bit ∘ s) + marks D := by
  have ht : ∀ a b c : Bool, ∀ p : Bool,
      ((b ≠ (a ^^ c)) ↔ p = true) ↔ bit a + bit b = bit c + bit p := by decide
  rw [Finset.ext_iff, funext_iff]
  apply forall_congr'
  intro i
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, inc_row, Function.comp_apply,
    Pi.add_apply]
  simpa [bit, marks] using ht (x (l i)) (x (r i)) (s i) (decide (i ∈ D))

lemma realize {m n : ℕ} (l r : Fin m → Fin n) (s : Fin m → Bool) (D : Finset (Fin m)) :
    (∃ x, bad l r s x = D) ↔ form (inc l r) (bit ∘ s) = form (inc l r) (marks D) := by
  rw [← attainable]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, (bad_eq_iff l r s D x).mp hx⟩
  · rintro ⟨x, hx⟩
    let w := fun v => decide (x v = 1)
    refine ⟨w, (bad_eq_iff l r s D w).mpr ?_⟩
    have hw : bit ∘ w = x := by
      funext v
      rcases zero_or_one (x v) with h | h <;> simp [Function.comp, w, bit, h]
    rwa [hw]

lemma form_one {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (i : Fin m) :
    form A (marks {i}) = coord A i := by
  ext y
  simp [form, coord, marks, dotProduct, mul_ite]

lemma form_pair {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) {i j : Fin m} (h : i ≠ j) :
    form A (marks {i,j}) = coord A i + coord A j := by
  have hm : marks {i,j} = marks {i} + marks {j} := by
    funext k
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all [marks]
  rw [hm, ← form_one A i, ← form_one A j]
  apply AddMonoidHom.ext
  intro y
  exact dotProduct_add y.val (marks {i}) (marks {j})

def oddFamily {m n : ℕ} (l r : Fin m → Fin n) (s : Fin m → Bool) :
    Finset (Finset (Fin m)) :=
  Finset.univ.filter fun D =>
    Odd ((D.filter fun e => s e = true).card) ∧
    ∀ v, Even ((D.filter fun e => l e = v).card + (D.filter fun e => r e = v).card)

lemma in_family {m n : ℕ} (l r : Fin m → Fin n) (s : Fin m → Bool)
    (D : Finset (Fin m)) :
    D ∈ oddFamily l r s ↔
      (inc l r).vecMul (marks D) = 0 ∧ dotProduct (marks D) (bit ∘ s) = 1 := by
  have hs : dotProduct (marks D) (bit ∘ s) = ((D.filter fun e => s e = true).card : F) :=
    count_marks D (fun e => s e = true)
  simp only [oddFamily, Finset.mem_filter, Finset.mem_univ, true_and, hs,
    ZMod.natCast_eq_one_iff_odd, funext_iff, inc_col, Pi.zero_apply, ZMod.natCast_eq_zero_iff_even]
  exact and_comm

lemma flip_bad {m n : ℕ} (l r : Fin m → Fin n) (s : Fin m → Bool) (x : Fin n → Bool) :
    bad l r s (fun v => !(x v)) = bad l r s x := by
  ext e
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  cases x (l e) <;> cases x (r e) <;> cases s e <;> decide

lemma singleton_impossible {m n : ℕ} (l r : Fin m → Fin n) (s a : Fin m → Bool)
    (h : ∀ x, (miss l r s a x).Nonempty) (e : Fin m) :
    ¬ ∃ x, bad l r s x = {e} := by
  rintro ⟨x, hx⟩
  by_cases he : x (l e) = a e
  · have hh := h (fun v => !(x v))
    simp [miss, flip_bad, hx, Finset.filter_singleton, he] at hh
  · simpa [miss, hx, Finset.filter_singleton, he] using h x

lemma private_pair {m n : ℕ} (l r : Fin m → Fin n) (s a : Fin m → Bool)
    (h : ∀ x, (miss l r s a x).Nonempty) {i j : Fin m}
    (hex : ∃ x, bad l r s x = {i,j}) :
    ∃ y, bad l r s y = {i,j} ∧ miss l r s a y = {i} ∧
      miss l r s a (fun v => !(y v)) = {j} := by
  obtain ⟨x, hx⟩ := hex
  by_cases hi : x (l i) = a i <;> by_cases hj : x (l j) = a j
  · have hh := h (fun v => !(x v))
    simp [miss, flip_bad, hx, Finset.filter_insert, Finset.filter_singleton, hi, hj] at hh
  · exact ⟨x, hx, by simp [miss, hx, Finset.filter_insert, Finset.filter_singleton, hi, hj],
      by simp [miss, flip_bad, hx, Finset.filter_insert, Finset.filter_singleton, hi, hj]⟩
  · refine ⟨fun v => !(x v), (flip_bad l r s x).trans hx, ?_, ?_⟩
    · simp [miss, flip_bad, hx, Finset.filter_insert, Finset.filter_singleton, hi, hj]
    · simp [miss, hx, Finset.filter_insert, Finset.filter_singleton, hi, hj]
  · have hh := h x
    simp [miss, hx, Finset.filter_insert, Finset.filter_singleton, hi, hj] at hh

lemma detect_on_odd {H : Type*} [AddGroup H] (s t : H →+ F)
    (hs : s ≠ 0) : s = t ↔ ∀ y, s y = 1 → t y = 1 := by
  classical
  constructor
  · rintro rfl y hy
    exact hy
  · intro h
    obtain ⟨u, hu⟩ : ∃ u, s u = 1 := by
      by_contra! hn
      exact hs (AddMonoidHom.ext (fun y => (zero_or_one (s y)).resolve_right (hn y)))
    apply AddMonoidHom.ext
    intro y
    rcases zero_or_one (s y) with hy | hy
    · have ht := h (y+u) (by rw [map_add, hy, hu, zero_add])
      rw [map_add, h u hu] at ht
      rw [hy]
      exact (by decide : ∀ z : F, z + 1 = 1 → 0 = z) _ ht
    · rw [hy, h y hy]

lemma pair_criterion {m n : ℕ} (l r : Fin m → Fin n) (s : Fin m → Bool)
    (hs : form (inc l r) (bit ∘ s) ≠ 0) {i j : Fin m} (hij : i ≠ j) :
    (∃ x, bad l r s x = {i,j}) ↔ ∀ D ∈ oddFamily l r s, i ∈ D ↔ j ∉ D := by
  rw [realize, form_pair _ hij, detect_on_odd _ _ hs]
  constructor
  · intro h D hD
    obtain ⟨hd, ho⟩ := (in_family l r s D).mp hD
    have hpair := h (⟨marks D, hd⟩ : dep (inc l r)) ho
    change marks D i + marks D j = 1 at hpair
    by_cases hi : i ∈ D <;> by_cases hj : j ∈ D <;> simp_all [marks]
  · intro h y hy
    have hd : support y.val ∈ oddFamily l r s := (in_family l r s _).mpr (by
      rw [marks_support]
      exact ⟨y.property, hy⟩)
    have hz := h _ hd
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    change y.val i + y.val j = 1
    rcases zero_or_one (y.val i) with hi | hi <;>
      rcases zero_or_one (y.val j) with hj | hj <;> simp_all

open Classical

def wave (z : F) : ℤ := if z = 0 then 1 else -1

lemma wave_add (a b : F) : wave (a+b) = wave a * wave b := by
  exact (by decide : ∀ x y : F, wave (x+y) = wave x * wave y) a b

lemma wave_sub (a b : F) : wave a * wave b = wave (a-b) := by
  exact (by decide : ∀ x y : F, wave x * wave y = wave (x-y)) a b

lemma wave_sum {H : Type*} [AddCommGroup H] [Fintype H] (f : H →+ F) :
    ∑ x, wave (f x) = if f = 0 then (Fintype.card H : ℤ) else 0 := by
  classical
  split_ifs with hf
  · subst f
    simp [wave]
  · obtain ⟨u, hu⟩ : ∃ u, f u = 1 := by
      by_contra! hn
      exact hf (AddMonoidHom.ext (fun x => (zero_or_one (f x)).resolve_right (hn x)))
    have ht := Equiv.sum_comp (Equiv.addRight u) (fun x => wave (f x))
    change (∑ x, wave (f (x+u))) = ∑ x, wave (f x) at ht
    simp only [map_add, wave_add, hu, show wave 1 = -1 by decide, mul_neg_one,
      Finset.sum_neg_distrib] at ht
    omega

def score {H E : Type*} [AddCommGroup H] [Fintype E] (c : E → H →+ F) (x : H) : ℤ :=
  ∑ i, wave (c i x)

lemma transform {H E : Type*} [AddCommGroup H] [Fintype H] [Fintype E]
    (c : E → H →+ F) (t : H →+ F) :
    (∑ x, score c x * wave (t x)) =
      (Fintype.card {i // c i = t} : ℤ) * Fintype.card H := by
  classical
  unfold score
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have inner (i : E) : (∑ x, wave (c i x) * wave (t x)) =
      if c i = t then (Fintype.card H : ℤ) else 0 := by
    simp_rw [wave_sub]
    simpa only [AddMonoidHom.sub_apply, sub_eq_zero] using wave_sum (c i - t)
  simp_rw [inner]
  rw [Fintype.card_subtype]
  simp [Finset.sum_ite]

lemma balanced {H E : Type*} [AddCommGroup H] [Fintype H] [Fintype E]
    (c : E → H →+ F) (s : H →+ F) (avoid : ∀ i, c i ≠ s)
    (bound : ∀ x, s x = 1 → score c x ≤ 0) (t : H →+ F) :
    Fintype.card {i // c i = t} = Fintype.card {i // c i = t + s} := by
  classical
  have hz : Fintype.card {i // c i = s} = 0 := by simp [avoid]
  have row_le (x : H) : score c x ≤ score c x * wave (s x) := by
    rcases zero_or_one (s x) with hx | hx
    · simp [hx, wave]
    · have hb := bound x hx
      simp [hx, wave]
      omega
  have lower : 0 ≤ ∑ x, score c x := by
    have ht := transform c 0
    simp only [AddMonoidHom.zero_apply, show wave 0 = 1 by decide, mul_one] at ht
    rw [ht]
    positivity
  have upper : (∑ x, score c x * wave (s x)) = 0 := by rw [transform, hz]; simp
  have eqSum : (∑ x, score c x) = ∑ x, score c x * wave (s x) :=
    le_antisymm (Finset.sum_le_sum fun x _ => row_le x) (upper ▸ lower)
  have same (x : H) : score c x = score c x * wave (s x) :=
    (Finset.sum_eq_sum_iff_of_le (fun i _ => row_le i)).mp eqSum x (Finset.mem_univ _)
  have eqProd : (Fintype.card {i // c i = t} : ℤ) * Fintype.card H =
      (Fintype.card {i // c i = t+s} : ℤ) * Fintype.card H := by
    rw [← transform, ← transform]
    apply Finset.sum_congr rfl
    intro x _
    rw [AddMonoidHom.add_apply, wave_add, mul_comm (wave (t x)), ← mul_assoc, ← same]
  exact_mod_cast (mul_right_cancel₀ (show (Fintype.card H : ℤ) ≠ 0 by positivity) eqProd)

lemma lift_pairs {E T : Type*} [Fintype E] (c : E → T) (shift : T → T)
    (hinv : Function.Involutive shift)
    (hc : ∀ t, Fintype.card {i // c i = t} = Fintype.card {i // c i = shift t}) :
    ∃ mate : E → E, Function.Involutive mate ∧ ∀ i, c (mate i) = shift (c i) := by
  classical
  let N := fun t => Fintype.card {i // c i = t}
  let rank : E ≃ (Σ t, Fin (N t)) := (Equiv.sigmaFiberEquiv c).symm.trans
    (Equiv.sigmaCongrRight fun t => Fintype.equivFin {i // c i = t})
  have proj (i : E) : (rank i).1 = c i := rfl
  let flip : (Σ t, Fin (N t)) → (Σ t, Fin (N t)) :=
    fun p => ⟨shift p.1, Fin.cast (hc p.1) p.2⟩
  have flip_twice : Function.Involutive flip := by
    rintro ⟨t,k⟩
    apply Sigma.ext (hinv t)
    exact (Fin.heq_ext_iff (congrArg N (hinv t))).mpr rfl
  refine ⟨fun i => rank.symm (flip (rank i)), ?_, ?_⟩
  · intro i
    simp [flip_twice _]
  · intro i
    rw [← proj, Equiv.apply_symm_apply]
    exact congrArg shift (proj i)

lemma hom_twice {H : Type*} [AddGroup H] (s : H →+ F) : s+s = 0 := by
  apply AddMonoidHom.ext
  intro x
  exact add_self_zero (s x)

lemma paired_coords {H E : Type*} [AddCommGroup H] [Fintype H] [Fintype E]
    (c : E → H →+ F) (s : H →+ F) (avoid : ∀ i, c i ≠ s)
    (bound : ∀ x, s x = 1 → score c x ≤ 0) :
    ∃ mate : E → E, Function.Involutive mate ∧ ∀ i, c (mate i) = c i + s := by
  apply lift_pairs c (fun t => t+s)
  · intro t
    exact (add_assoc t s s).trans (by rw [hom_twice, add_zero])
  · intro t
    simpa only [← Nat.card_eq_fintype_card] using balanced c s avoid bound t

lemma score_weight {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (y : dep A) :
    score (coord A) y = (m : ℤ) - 2 * (support y.val).card := by
  have h (a : F) : wave a = 1 - 2 * (if a = 1 then 1 else 0) := by
    rcases zero_or_one a with rfl | rfl <;> decide
  simp only [score, coord, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, support]

end PEqualNP.Outside.L_pcx_279_aux

open PEqualNP.Outside.L_pcx_279_aux

theorem PEqualNP.Outside.L_pcx_279 : (∀ (n m : ℕ) (left right : Fin m → Fin n) (sign start : Fin m → Bool),
  let oddSet := fun D : Finset (Fin m) =>
    Odd ((D.filter (fun e => sign e = true)).card) ∧
    ∀ v : Fin n, Even ((D.filter (fun e => left e = v)).card +
      (D.filter (fun e => right e = v)).card)
  let W := Finset.univ.filter oddSet
  let faults := fun x : Fin n → Bool =>
    Finset.univ.filter (fun i => x (right i) ≠ (x (left i) ^^ sign i))
  let missed := fun x : Fin n → Bool =>
    (faults x).filter (fun i => x (left i) = start i)
  (∀ x, (missed x).Nonempty) →
    (∀ (i j : Fin m), i ≠ j →
      ((∃ x, faults x = {i,j}) ↔ (∀ D ∈ W, i ∈ D ↔ j ∉ D)) ∧
      ((∃ x, faults x = {i,j}) → ∃ y, faults y = {i,j} ∧ missed y = {i} ∧
        missed (fun v => !(y v)) = {j})) ∧
    ∀ g : ℕ, m = 2*g → (∀ D ∈ W, g ≤ D.card) →
      ∃ mate : Fin m → Fin m, Function.Involutive mate ∧
        ∀ e, mate e ≠ e ∧ ∃ word, faults word = {e, mate e} ∧
          missed word = {e} ∧ missed (fun v => !(word v)) = {mate e}) := by
  classical
  intro n m l r s a
  dsimp only
  intro h
  have hmiss : ∀ x, (miss l r s a x).Nonempty := h
  let A := inc l r
  let sig := form A (bit ∘ s)
  have hs : sig ≠ 0 := by
    intro hz
    have hempty : form A (marks ∅) = 0 := by
      apply AddMonoidHom.ext
      intro y
      simp [form, dotProduct, marks]
    obtain ⟨x, hx⟩ := (realize l r s ∅).mpr (hz.trans hempty.symm)
    simpa [miss, hx] using hmiss x
  constructor
  · intro i j hij
    exact ⟨pair_criterion l r s hs hij, private_pair l r s a hmiss⟩
  · intro g hm hmin
    have avoid (e : Fin m) : coord A e ≠ sig := by
      intro he
      exact singleton_impossible l r s a hmiss e
        ((realize l r s {e}).mpr (he.symm.trans (form_one A e).symm))
    have bound (y : dep A) (hy : sig y = 1) : score (coord A) y ≤ 0 := by
      have hd : support y.val ∈ oddFamily l r s := (in_family l r s _).mpr (by
        rw [marks_support]
        exact ⟨y.property, hy⟩)
      have hh := hmin _ hd
      rw [score_weight]
      omega
    let _ : Fintype (dep A) := Fintype.ofFinite _
    obtain ⟨mate, inv, pairs⟩ := paired_coords (coord A) sig avoid bound
    refine ⟨mate, inv, fun e => ?_⟩
    have he : sig = coord A e + coord A (mate e) := by
      rw [pairs, ← add_assoc, hom_twice, zero_add]
    have hne : mate e ≠ e := fun hfix => hs (by rwa [hfix, hom_twice] at he)
    refine ⟨hne, private_pair l r s a hmiss ((realize l r s {e, mate e}).mpr ?_)⟩
    exact he.trans (form_pair A hne.symm).symm
