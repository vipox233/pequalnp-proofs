import PEqualNP.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Perm
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.Hall.Basic
namespace PEqualNP.Outside.L_meta_25722

-- The circuit construction (the lookup of a table on selected address bits), the base table (`existsBase`) and the
-- three pool lemmas are copied from the merged PEqualNP.Outside.L_meta_25715 by Aistis Raulinaitis
-- (Apache License 2.0). New in this file: a thick diagonal of the type matrix by Hall's theorem (`thickDiagonal`),
-- the count over all choices of one representative per type (`sum_two_coords`, `lossOfCells`), and the last theorem.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def literalInput {n : ℕ} (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ List.ofFn (fun i => !x i)

def allowed (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem allowed_append {g h : List Gate} (hg : allowed g) (hh : allowed h) :
    allowed (g ++ h) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hg t ht
  · exact hh t ht

def values (gs : List Gate) (input : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires input

theorem values_append (g h : List Gate) (input : List Bool) :
    values (g ++ h) input = values h (values g input) := by
  exact List.foldl_append

theorem values_length (gs : List Gate) (input : List Bool) :
    (values gs input).length = input.length + gs.length := by
  induction gs generalizing input with
  | nil => simp [values, Circuit.wires]
  | cons g gs ih =>
    unfold values Circuit.wires at ih ⊢
    simp only [List.foldl_cons, List.length_cons, ih, List.length_append, List.length_nil]
    omega

theorem values_preserve (gs : List Gate) (input : List Bool) {i : ℕ}
    (hi : i < input.length) : (values gs input).getD i false = input.getD i false := by
  induction gs generalizing input with
  | nil => rfl
  | cons g gs ih =>
    unfold values Circuit.wires at ih ⊢
    simp only [List.foldl_cons]
    rw [ih _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def atWire {n : ℕ} (gs : List Gate) (i : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  i < n + n + gs.length ∧ ∀ x, (values gs (literalInput x)).getD i false = f x

theorem atWire_extend {n : ℕ} {gs : List Gate} (h : List Gate)
    {i : ℕ} {f : (Fin n → Bool) → Bool} (hf : atWire gs i f) : atWire (gs ++ h) i f := by
  refine ⟨by have := hf.1; simp; omega, fun x => ?_⟩
  rw [values_append, values_preserve]
  · exact hf.2 x
  · simpa [values_length, literalInput] using hf.1

theorem atWire_snoc {n : ℕ} (gs : List Gate) (g : Gate) :
    atWire (gs ++ [g]) (n + n + gs.length) (fun x : Fin n → Bool =>
      g.op.eval (g.inputs.map (fun i => (values gs (literalInput x)).getD i false))) := by
  refine ⟨by simp, fun x => ?_⟩
  have hlen : (values gs (literalInput x)).length = n + n + gs.length := by
    simp [values_length, literalInput]
  rw [values_append, ← hlen]
  change (values [g] (values gs (literalInput x))).getD (values gs (literalInput x)).length
    false = g.op.eval (g.inputs.map fun i => (values gs (literalInput x)).getD i false)
  generalize values gs (literalInput x) = l
  simp only [values, Circuit.wires, List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl _)]
  simp

theorem andWire {n : ℕ} {gs : List Gate} {i j : ℕ}
    {f g : (Fin n → Bool) → Bool} (hf : atWire gs i f) (hg : atWire gs j g) :
    atWire (gs ++ [⟨GateOp.and, [i,j]⟩]) (n+n+gs.length) (fun x => f x && g x) := by
  refine ⟨(atWire_snoc (n := n) gs ⟨GateOp.and, [i,j]⟩).1, fun x => ?_⟩
  rw [(atWire_snoc (n := n) gs ⟨GateOp.and, [i,j]⟩).2 x]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
    Bool.and_true, hf.2 x, hg.2 x]

theorem orWire {n : ℕ} {gs : List Gate} {i j : ℕ}
    {f g : (Fin n → Bool) → Bool} (hf : atWire gs i f) (hg : atWire gs j g) :
    atWire (gs ++ [⟨GateOp.or, [i,j]⟩]) (n+n+gs.length) (fun x => f x || g x) := by
  refine ⟨(atWire_snoc (n := n) gs ⟨GateOp.or, [i,j]⟩).1, fun x => ?_⟩
  rw [(atWire_snoc (n := n) gs ⟨GateOp.or, [i,j]⟩).2 x]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false, hf.2 x, hg.2 x]

theorem multiplex {n : ℕ} {gs : List Gate} {i j u v : ℕ}
    {s f g : (Fin n → Bool) → Bool} (hs : atWire gs i s)
    (hn : atWire gs j (fun x => !s x)) (hf : atWire gs u f) (hg : atWire gs v g) :
    ∃ h w, allowed h ∧ h.length = 3 ∧ atWire (gs ++ h) w (fun x => if s x then g x else f x) := by
  let a : Gate := ⟨GateOp.and, [j,u]⟩
  let b : Gate := ⟨GateOp.and, [i,v]⟩
  let c : Gate := ⟨GateOp.or, [n+n+gs.length, n+n+(gs ++ [a]).length]⟩
  have ha := andWire hn hf
  have hb := andWire (atWire_extend [a] hs) (atWire_extend [a] hg)
  have hc := orWire (atWire_extend [b] ha) hb
  refine ⟨[a,b,c], n+n+((gs ++ [a]) ++ [b]).length, ?_, rfl, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp [a,b,c]
  · rw [List.append_assoc, List.append_assoc] at hc
    refine ⟨hc.1, fun x => ?_⟩
    change (values (gs ++ ([a] ++ ([b] ++ [c]))) (literalInput x)).getD
      (n + n + (gs ++ [a] ++ [b]).length) false = _
    rw [hc.2 x]
    cases hsx : s x <;> simp [hsx]

theorem lookupExtension {n : ℕ} (d : ℕ) (sel : Fin d → Fin n)
    (f : (Fin d → Bool) → Bool) (gs : List Gate) (w₀ w₁ : ℕ)
    (h₀ : atWire gs w₀ (fun _ : Fin n → Bool => false))
    (h₁ : atWire gs w₁ (fun _ : Fin n → Bool => true))
    (hp : ∀ i, atWire gs (sel i).val (fun x => x (sel i)))
    (hn : ∀ i, atWire gs (n + (sel i).val) (fun x => !x (sel i))) :
    ∃ h w, allowed h ∧ h.length + 3 ≤ 3 * 2^d ∧
      atWire (gs ++ h) w (fun x => f (fun i => x (sel i))) := by
  induction d generalizing gs with
  | zero =>
    let empty : Fin 0 → Bool := fun i => Fin.elim0 i
    have he (x : Fin n → Bool) : (fun i => x (sel i)) = empty := funext fun i => Fin.elim0 i
    cases h : f empty with
    | false =>
      exact ⟨[], w₀, by simp [allowed], by simp, by simpa [he, h] using h₀⟩
    | true =>
      exact ⟨[], w₁, by simp [allowed], by simp, by simpa [he, h] using h₁⟩
  | succ d ih =>
    obtain ⟨l, u, hl, hls, hlf⟩ := ih (fun i => sel i.succ)
      (fun y => f (Fin.cons false y)) gs h₀ h₁ (fun i => hp i.succ) (fun i => hn i.succ)
    obtain ⟨r, v, hr, hrs, hrf⟩ := ih (fun i => sel i.succ)
      (fun y => f (Fin.cons true y)) (gs ++ l) (atWire_extend l h₀) (atWire_extend l h₁)
      (fun i => atWire_extend l (hp i.succ)) (fun i => atWire_extend l (hn i.succ))
    obtain ⟨t, w, ht, hts, htf⟩ := multiplex
      (atWire_extend r (atWire_extend l (hp 0))) (atWire_extend r (atWire_extend l (hn 0)))
      (atWire_extend r hlf) hrf
    rw [List.append_assoc, List.append_assoc] at htf
    refine ⟨l ++ r ++ t, w, allowed_append (allowed_append hl hr) ht, ?_, ?_⟩
    · simp only [List.length_append, hts, pow_succ]; omega
    · rw [List.append_assoc]
      refine ⟨htf.1, fun x => ?_⟩
      rw [htf.2 x]
      have hx : Fin.cons (x (sel 0)) (fun i : Fin d => x (sel i.succ)) =
          (fun i : Fin (d+1) => x (sel i)) := by
        funext i
        exact Fin.cases (by simp) (fun j => by simp) i
      cases hs : x (sel 0) <;> simpa [hs] using congrArg f hx

theorem lookupSize {n d : ℕ} (sel : Fin d → Fin n) (f : (Fin d → Bool) → Bool) :
    HasLitSize n (fun x => f (fun i => x (sel i))) (3 * 2^d) := by
  let g₀ : Gate := ⟨GateOp.or, []⟩
  let g₁ : Gate := ⟨GateOp.and, []⟩
  let pre := [g₀,g₁]
  have h₀ : atWire pre (n+n) (fun _ : Fin n → Bool => false) := by
    have hh : atWire [g₀] (n+n) (fun _ : Fin n → Bool => false) := by
      simpa [g₀, GateOp.eval] using atWire_snoc (n := n) [] g₀
    exact atWire_extend [g₁] hh
  have h₁ : atWire pre (n+n+1) (fun _ : Fin n → Bool => true) := by
    simpa [pre, g₁, GateOp.eval] using atWire_snoc (n := n) [g₀] g₁
  have hp (i : Fin d) : atWire [] (sel i).val (fun x => x (sel i)) := by
    have hi := (sel i).isLt
    refine ⟨by simp; omega, fun x => ?_⟩
    simp only [values, Circuit.wires, List.foldl_nil, literalInput, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp [hi])]
    simp [hi]
  have hn (i : Fin d) : atWire [] (n + (sel i).val) (fun x => !x (sel i)) := by
    have hi := (sel i).isLt
    refine ⟨by simp, fun x => ?_⟩
    simp only [values, Circuit.wires, List.foldl_nil, literalInput, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp)]
    simp [hi]
  obtain ⟨suf, w, hv, hl, hw⟩ := lookupExtension d sel f pre _ _ h₀ h₁
    (fun i => atWire_extend pre (hp i)) (fun i => atWire_extend pre (hn i))
  refine ⟨⟨pre ++ suf, w⟩, allowed_append ?_ hv, ?_, hw.2⟩
  · intro t ht
    simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp [g₀,g₁]
  · change (pre ++ suf).length ≤ _
    simp only [pre, List.length_append, List.length_cons, List.length_nil]
    omega

open PEqualNP.MetaComplexity PEqualNP.Represents

def lowType (a k : ℕ) (x : Fin (2^k)) : Fin (2^a) := Fin.ofNat (2^a) x.val

theorem lowIndex {a k : ℕ} (hak : a ≤ k) (x : Fin k → Bool) :
    lowType a k (Fin.ofNat (2^k) (tableIndex x)) =
      Fin.ofNat (2^a) (tableIndex (fun i : Fin a => x (Fin.castLE hak i))) := by
  apply Fin.ext
  change (tableIndex x % 2^k) % 2^a = _
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hak)]
  let f (i : Fin k) : ℕ := if x i then 2^i.val else 0
  let L := Finset.univ.filter (fun i : Fin k => i.val < a)
  have hleft : ∑ i ∈ L, f i = tableIndex (fun i : Fin a => x (Fin.castLE hak i)) := by
    symm
    unfold tableIndex
    refine Finset.sum_nbij (Fin.castLE hak) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro i _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
    · intro i _ j _ hij
      exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) hij)
    · intro i hi
      have hi' : i.val < a := (Finset.mem_filter.mp hi).2
      exact ⟨⟨i.val, hi'⟩, Finset.mem_univ _, Fin.ext rfl⟩
  have hright : 2^a ∣ ∑ i ∈ Lᶜ, f i := by
    refine Finset.dvd_sum fun i hi => ?_
    have hi' : a ≤ i.val := by simpa [L, not_lt] using hi
    dsimp [f]
    split_ifs
    · exact Nat.pow_dvd_pow 2 hi'
    · exact dvd_zero _
  obtain ⟨u, hu⟩ := hright
  change (∑ i, f i) % 2^a = (tableIndex fun i : Fin a => x (Fin.castLE hak i)) % 2^a
  rw [← Finset.sum_add_sum_compl L f, hleft, hu, Nat.add_mul_mod_self_left]

theorem fibersLow {a k : ℕ} (hak : a ≤ k) (π : Equiv.Perm (Fin (2^k)))
    (t : Fin (2^a)) :
    (Finset.univ.filter (fun x => lowType a k (π x) = t)).card = 2^(k-a) := by
  let b := 2^(k-a)
  let m := 2^a
  have hbm : b*m = 2^k := by dsimp [b,m]; rw [← pow_add, Nat.sub_add_cancel hak]
  let e : Fin b × Fin m ≃ Fin (2^k) := finProdFinEquiv.trans (finCongr hbm)
  have htype (z : Fin b × Fin m) : lowType a k (e z) = z.2 := by
    apply Fin.ext
    change (z.2.val + m*z.1.val) % m = z.2.val
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt z.2.isLt]
  change (Finset.univ.filter (fun x => lowType a k (π x) = t)).card = b
  rw [← Fintype.card_fin b, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun i _ => π.symm (e (i,t))) ?_ ?_ ?_
  · intro i _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply, htype]
  · intro i _ j _ h
    exact congrArg Prod.fst (e.injective (π.symm.injective h))
  · intro y hy
    obtain ⟨⟨i,j⟩, hij⟩ := e.surjective (π y)
    have hj : j = t := by
      calc
        j = lowType a k (e (i,j)) := (htype (i,j)).symm
        _ = t := by rw [hij]; exact (Finset.mem_filter.mp hy).2
    subst j
    exact ⟨i, Finset.mem_univ _, by rw [hij, π.symm_apply_apply]⟩

open scoped BigOperators

def sameColorPairs {m d : ℕ} (c : Fin m → Fin d) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun z => z.1 < z.2 ∧ c z.1 = c z.2)

lemma sameColorPairs_bound {m d : ℕ} (c : Fin m → Fin d) :
    m ^ 2 ≤ d * (2 * (sameColorPairs c).card + m) := by
  classical
  let f : Fin d → Finset (Fin m) := fun b => Finset.univ.filter (fun i => c i = b)
  let R : Finset (Fin m × Fin m) := Finset.univ.filter (fun z => c z.1 = c z.2)
  let U := sameColorPairs c
  let L := U.map (Equiv.prodComm (Fin m) (Fin m)).toEmbedding
  let D := (Finset.univ : Finset (Fin m)).diag
  have hfs : (∑ b : Fin d, (f b).card) = m := by
    have h := Finset.card_eq_sum_card_fiberwise (f := c) (s := Finset.univ)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    simpa [f] using h.symm
  have hRs : R.card = ∑ b : Fin d, (f b).card ^ 2 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := fun z : Fin m × Fin m => c z.1)
      (s := R) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [h]
    apply Finset.sum_congr rfl
    intro b _
    have hb : R.filter (fun z => c z.1 = b) = (f b) ×ˢ (f b) := by
      ext z
      simp only [R, f, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
      constructor
      · rintro ⟨he, hb⟩
        exact ⟨hb, he.symm.trans hb⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁.trans h₂.symm, h₁⟩
    rw [hb, Finset.card_product, pow_two]
  have hU (z : Fin m × Fin m) : z ∈ U ↔ z.1 < z.2 ∧ c z.1 = c z.2 := by
    simp [U, sameColorPairs]
  have hL (z : Fin m × Fin m) : z ∈ L ↔ z.2 < z.1 ∧ c z.1 = c z.2 := by
    rw [show L = U.image Prod.swap from Finset.map_eq_image _ _, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨((hU x).mp hx).1, ((hU x).mp hx).2.symm⟩
    · intro hz
      exact ⟨z.swap, (hU _).mpr ⟨hz.1, hz.2.symm⟩, Prod.swap_swap z⟩
  have hD (z : Fin m × Fin m) : z ∈ D ↔ z.1 = z.2 := by simp [D]
  have hsplit : R = U ∪ L ∪ D := by
    ext z
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hU, hL, hD]
    constructor
    · intro hz
      rcases lt_trichotomy z.1 z.2 with h | h | h
      · exact Or.inl (Or.inl ⟨h, hz⟩)
      · exact Or.inr h
      · exact Or.inl (Or.inr ⟨h, hz⟩)
    · rintro ((h | h) | h)
      · exact h.2
      · exact h.2
      · rw [h]
  have hul : Disjoint U L := Finset.disjoint_left.mpr fun z hzU hzL =>
    (not_lt_of_ge (le_of_lt ((hU z).mp hzU).1)) ((hL z).mp hzL).1
  have hud : Disjoint (U ∪ L) D := by
    refine Finset.disjoint_left.mpr ?_
    intro z hz hzD
    have hd := (hD z).mp hzD
    rcases Finset.mem_union.mp hz with hu | hl
    · exact (ne_of_lt ((hU z).mp hu).1) hd
    · exact (ne_of_gt ((hL z).mp hl).1) hd
  have hRc : R.card = 2 * U.card + m := by
    rw [hsplit, Finset.card_union_of_disjoint hud, Finset.card_union_of_disjoint hul]
    simp [L, D, two_mul]
  rw [← hRc, hRs]
  simpa [hfs] using
    (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun b => (f b).card))

def bitWeight {I : Type*} [Fintype I] (b : I → Bool) : ℕ :=
  (Finset.univ.filter (fun i => b i = true)).card

noncomputable def lowWords (I : Type*) [Fintype I] (t : ℕ) : Finset (I → Bool) := by
  classical exact Finset.univ.filter (fun b => bitWeight b ≤ t)

lemma card_lowWords {I : Type*} [Fintype I] (k t : ℕ)
    (hI : Fintype.card I = 4 * k) (ht : t ≤ 4 * k) :
    (lowWords I t).card ≤ 2 ^ (k + 3 * t) := by
  classical
  let w : Bool → ℕ := fun b => if b = true then 1 else 8
  have hprod (b : I → Bool) : (∏ i, w (b i)) = 8 ^ (4 * k - bitWeight b) := by
    let A : Finset I := Finset.univ.filter (fun i => b i = true)
    let B : Finset I := Finset.univ.filter (fun i => ¬ b i = true)
    have hab : A.card + B.card = 4 * k := by
      rw [← hI, ← Finset.card_univ]
      exact Finset.card_filter_add_card_filter_not _
    have hB : B.card = 4 * k - bitWeight b := by
      change B.card = 4 * k - A.card
      omega
    have hAprod : (∏ i ∈ A, w (b i)) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      simp [w, (Finset.mem_filter.mp hi).2]
    have hBprod : (∏ i ∈ B, w (b i)) = 8 ^ B.card := by
      rw [← Finset.prod_const]
      apply Finset.prod_congr rfl
      intro i hi
      simp [w, (Finset.mem_filter.mp hi).2]
    have hsplit : (∏ i ∈ A, w (b i)) * (∏ i ∈ B, w (b i)) = ∏ i, w (b i) :=
      Finset.prod_filter_mul_prod_filter_not _ _ _
    rw [← hsplit, hAprod, one_mul, hBprod, hB]
  have hsum : (∑ b : I → Bool, ∏ i, w (b i)) = 9 ^ (4 * k) := by
    rw [← Fintype.prod_sum (fun (_ : I) => w)]
    simp [w, hI]
  have hweighted : (lowWords I t).card * 8 ^ (4 * k - t) ≤ 9 ^ (4 * k) := by
    calc
      _ = ∑ _b ∈ lowWords I t, 8 ^ (4 * k - t) := by simp
      _ ≤ ∑ b ∈ lowWords I t, ∏ i, w (b i) := by
        apply Finset.sum_le_sum
        intro b hb
        have hb' : bitWeight b ≤ t := by
          simpa only [lowWords, Finset.mem_filter, Finset.mem_univ, true_and] using hb
        rw [hprod]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ ∑ b : I → Bool, ∏ i, w (b i) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = _ := hsum
  have hexp : k + 3 * t + 3 * (4 * k - t) = 13 * k := by omega
  have hlim : 9 ^ (4 * k) ≤ 2 ^ (k + 3 * t) * 8 ^ (4 * k - t) := by
    calc
      9 ^ (4 * k) = (9 ^ 4 : ℕ) ^ k := by rw [pow_mul]
      _ ≤ (2 ^ 13 : ℕ) ^ k := Nat.pow_le_pow_left (by decide) _
      _ = _ := by
        rw [← pow_mul, show (8 : ℕ) = 2 ^ 3 by decide, ← pow_mul, ← pow_add, hexp]
  exact Nat.le_of_mul_le_mul_right (hweighted.trans hlim) (by positivity)

abbrev Table (m : ℕ) := Fin m × Fin m → Bool

def conflict {m : ℕ} (g : Table m) (p : Equiv.Perm (Fin m))
    (s : Fin m → Bool) (z : Fin m × Fin m) : Bool :=
  Bool.xor (Bool.xor (g (z.1, p z.2)) (g (z.2, p z.1))) (Bool.xor (s z.1) (s z.2))

lemma xor_true_iff_ne (x y : Bool) : Bool.xor x y = true ↔ x ≠ y := by
  cases x <;> cases y <;> decide

def badTables {m d : ℕ} (p : Equiv.Perm (Fin m)) (s : Fin m → Bool)
    (c : Fin m → Fin d) (t : ℕ) : Finset (Table m) :=
  Finset.univ.filter (fun g => ((sameColorPairs c).filter (fun z => conflict g p s z = true)).card ≤ t)

def tableColumns {m : ℕ} (p : Equiv.Perm (Fin m)) : Table m ≃ Table m where
  toFun g z := g (z.1, p z.2)
  invFun g z := g (z.1, p.symm z.2)
  left_inv g := by funext z; rcases z with ⟨i, j⟩; simp
  right_inv g := by funext z; rcases z with ⟨i, j⟩; simp

def tableTwist {m : ℕ} (S : Finset (Fin m × Fin m)) (s : Fin m → Bool)
    (g : Table m) (z : Fin m × Fin m) : Bool :=
  if z ∈ S then Bool.xor (Bool.xor (g z) (g z.swap)) (Bool.xor (s z.1) (s z.2)) else g z

lemma xor_twice (x y z : Bool) :
    Bool.xor (Bool.xor (Bool.xor (Bool.xor x y) z) y) z = x := by
  cases x <;> cases y <;> cases z <;> decide

lemma tableTwist_involution {m : ℕ} (S : Finset (Fin m × Fin m)) (s : Fin m → Bool)
    (hS : ∀ z ∈ S, z.1 < z.2) : Function.Involutive (tableTwist S s) := by
  intro g
  funext z
  by_cases hz : z ∈ S
  · have hrev : z.swap ∉ S := fun h => (not_lt_of_ge (le_of_lt (hS z hz))) (hS z.swap h)
    simpa only [tableTwist, ite_eq_left hz, ite_eq_right hrev] using
      xor_twice (g z) (g z.swap) (Bool.xor (s z.1) (s z.2))
  · simp [tableTwist, hz]

lemma card_badTables {m d k t : ℕ} (p : Equiv.Perm (Fin m)) (s : Fin m → Bool)
    (c : Fin m → Fin d) (ht : t ≤ 4 * k) (hk : 4 * k ≤ (sameColorPairs c).card) :
    (badTables p s c t).card ≤ 2 ^ (k + 3 * t) * 2 ^ (m * m - 4 * k) := by
  classical
  obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq hk
  have hS : ∀ z ∈ S, z.1 < z.2 := fun z hz => ((Finset.mem_filter.mp (hsub hz)).2).1
  let E := (tableColumns p).trans (((tableTwist_involution S s hS).toPerm _).trans
    (Equiv.piEquivPiSubtypeProd (fun z => z ∈ S) (fun _ => Bool)))
  have hE (g : Table m) (z : S) : (E g).1 z = conflict g p s z := by
    change tableTwist S s (tableColumns p g) z = _
    simp only [tableTwist, ite_eq_left z.property]
    rfl
  let B := badTables p s c t
  let W := lowWords S t
  have hmem (g : B) : (E g.1).1 ∈ W := by
    simp only [W, lowWords, Finset.mem_filter, Finset.mem_univ, true_and]
    have hg : ((sameColorPairs c).filter (fun z => conflict g.1 p s z = true)).card ≤ t :=
      (Finset.mem_filter.mp g.2).2
    refine le_trans ?_ hg
    let A := Finset.univ.filter (fun i : S => (E g.1).1 i = true)
    change A.card ≤ _
    have inject (i : A) : (i.1.1 : Fin m × Fin m) ∈
        (sameColorPairs c).filter (fun z => conflict g.1 p s z = true) := by
      exact Finset.mem_filter.mpr
        ⟨hsub i.1.2, (hE g.1 i.1).symm.trans (Finset.mem_filter.mp i.2).2⟩
    exact Finset.card_le_card_of_injective (f := fun i : A => ⟨i.1.1, inject i⟩)
      (fun _ _ he => by
        have hv := congrArg Subtype.val he
        exact Subtype.ext (Subtype.ext hv))
  let liftBad : B → W × ({z // z ∉ S} → Bool) := fun g =>
    (⟨(E g.1).1, hmem g⟩, (E g.1).2)
  have hlift : Function.Injective liftBad := by
    intro x y hxy
    apply Subtype.ext
    apply E.injective
    have h₁ := congrArg (fun v : W × ({z // z ∉ S} → Bool) => v.1.1) hxy
    have h₂ := congrArg Prod.snd hxy
    exact Prod.ext h₁ h₂
  have hSc : Fintype.card S = 4 * k := (Fintype.card_coe S).trans hcard
  calc
    B.card = Fintype.card B := (Fintype.card_coe B).symm
    _ ≤ Fintype.card (W × ({z // z ∉ S} → Bool)) := Fintype.card_le_of_injective liftBad hlift
    _ = W.card * 2 ^ (m * m - 4 * k) := by
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_subtype_compl, Fintype.card_prod, Fintype.card_fin, hSc]
    _ ≤ _ := Nat.mul_le_mul_right _ (card_lowWords k t hSc ht)

lemma card_configurations {a m d : ℕ} (hm : m = 2 ^ a) (hd : d ≤ m) :
    Fintype.card (Equiv.Perm (Fin m) × (Fin m → Bool) × (Fin m → Fin d)) ≤
      2 ^ ((2 * a + 1) * m) := by
  classical
  have hp : Fintype.card (Equiv.Perm (Fin m)) ≤ m ^ m := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using
      (Fintype.card_le_of_injective (fun p : Equiv.Perm (Fin m) => (p : Fin m → Fin m))
        Equiv.coe_fn_injective)
  have hpw : m ^ m = 2 ^ (a * m) := by rw [pow_mul, ← hm]
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Fintype.card_fin]
  calc
    _ ≤ m ^ m * (2 ^ m * m ^ m) := Nat.mul_le_mul hp
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd m))
    _ = _ := by rw [hpw, ← pow_add, ← pow_add]; congr 1; ring

lemma existsBase (a : ℕ) (ha : 16 ≤ a) : let m := 2^a;
    ∃ g : Fin m → Fin m → Bool, ∀ (d : ℕ), 8*a*d ≤ m →
      ∀ (p : Equiv.Perm (Fin m)) (s : Fin m → Bool) (c : Fin m → Fin d),
      a*m < 4 * ((Finset.univ : Finset (Fin m × Fin m)).filter (fun z =>
        z.1 < z.2 ∧ c z.1 = c z.2 ∧ Bool.xor (g z.1 (p z.2)) (g z.2 (p z.1)) ≠
          Bool.xor (s z.1) (s z.2))).card := by
  classical
  dsimp only
  let m := 2 ^ a
  change ∃ g : Fin m → Fin m → Bool, _
  have hm : 0 < m := by dsimp [m]; positivity
  obtain ⟨n, hn⟩ : 4 ∣ m := by
    change 2 ^ 2 ∣ 2 ^ a
    exact pow_dvd_pow 2 (by omega)
  have hnpos : 0 < n := by omega
  let t := a * n
  let k := 4 * t - n
  let D := m / (8 * a)
  have had : 0 < 8 * a := by omega
  have hD : D ≤ m := Nat.div_le_self _ _
  have hDm : 8 * a * D ≤ m := by
    simpa only [D, Nat.mul_comm (8 * a)] using (Nat.div_mul_le_self m (8 * a))
  have hn_t : n ≤ t := by
    dsimp [t]
    simpa using (Nat.mul_le_mul_right n (show 1 ≤ a by omega))
  have ht : t ≤ 4 * k := by dsimp [k]; omega
  have ham : a * m = 4 * t := by rw [hn]; dsimp [t]; ring
  have hExp : (2 * a + 1) * m + (k + 3 * t) < 4 * k := by
    have h16n := Nat.mul_le_mul_right n ha
    have hcfg : (2 * a + 1) * m = 8 * t + 4 * n := by rw [hn]; dsimp [t]; ring
    rw [hcfg]
    change 16 * n ≤ t at h16n
    dsimp [k]
    omega
  let Config := Equiv.Perm (Fin m) × (Fin m → Bool) × (Fin m → Fin D)
  let bad : Config → Finset (Table m) := fun q => badTables q.1 q.2.1 q.2.2 t
  have hpair (c : Fin m → Fin D) : 4 * k ≤ (sameColorPairs c).card := by
    have hDp : 0 < D := Nat.zero_lt_of_lt (c ⟨0, hm⟩).isLt
    have hbound : 8 * a * m ≤ 2 * (sameColorPairs c).card + m := by
      apply Nat.le_of_mul_le_mul_left _ hDp
      calc
        D * (8 * a * m) = (8 * a * D) * m := by ring
        _ ≤ m ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right m hDm
        _ ≤ _ := sameColorPairs_bound c
    rw [show 8 * a * m = 8 * (a * m) by ring, ham] at hbound
    dsimp [k]
    omega
  let allBad : Finset (Table m) := Finset.univ.biUnion bad
  have hN : Fintype.card (Table m) = 2 ^ (m * m) := by
    simp
  have h4k : 4 * k ≤ m * m := by
    have hlarge : 4 * a ≤ m := by
      calc
        _ ≤ 16 * (a - 4 + 1) := by omega
        _ ≤ 16 * 2 ^ (a - 4) := Nat.mul_le_mul_left _ Nat.lt_two_pow_self
        _ = m := by
          change 2 ^ 4 * 2 ^ (a - 4) = 2 ^ a
          rw [← pow_add, show 4 + (a - 4) = a by omega]
    calc
      4 * k ≤ 16 * t := by dsimp [k]; omega
      _ = (4 * a) * m := by rw [mul_assoc, ham]; ring
      _ ≤ m * m := Nat.mul_le_mul_right _ hlarge
  have hunion : allBad.card < Fintype.card (Table m) := by
    have hc := card_configurations (m := m) rfl hD
    calc
      allBad.card ≤ ∑ q : Config, (bad q).card := Finset.card_biUnion_le
      _ ≤ ∑ _q : Config, 2 ^ (k + 3 * t) * 2 ^ (m * m - 4 * k) :=
        Finset.sum_le_sum fun q _ => card_badTables q.1 q.2.1 q.2.2 ht (hpair q.2.2)
      _ = Fintype.card Config * (2 ^ (k + 3 * t) * 2 ^ (m * m - 4 * k)) := by simp
      _ ≤ 2 ^ ((2 * a + 1) * m) * (2 ^ (k + 3 * t) * 2 ^ (m * m - 4 * k)) :=
        Nat.mul_le_mul_right _ hc
      _ < _ := by
        rw [hN, ← pow_add, ← pow_add]
        exact Nat.pow_lt_pow_right (by decide) (by omega)
  obtain ⟨g, -, hg⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := allBad)
    (t := (Finset.univ : Finset (Table m))) (by simpa only [Finset.card_univ] using hunion)
  refine ⟨fun i j => g (i,j), ?_⟩
  intro d hd p s c
  have hdD : d ≤ D := (Nat.le_div_iff_mul_le had).mpr (by simpa [Nat.mul_comm] using hd)
  let C : Fin m → Fin D := fun i => (c i).castLE hdD
  have hcolor (i j : Fin m) : C i = C j ↔ c i = c j := by
    constructor
    · intro h
      have hv := congrArg Fin.val h
      exact Fin.ext hv
    · intro h
      exact congrArg (fun v : Fin d => v.castLE hdD) h
  have hg' : g ∉ badTables p s C t := fun h => hg (Finset.mem_biUnion.mpr
    ⟨(p, s, C), Finset.mem_univ _, h⟩)
  have hgood : t < ((sameColorPairs C).filter (fun z => conflict g p s z = true)).card := by
    by_contra! h
    exact hg' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hfilter : (sameColorPairs C).filter (fun z => conflict g p s z = true) =
      Finset.univ.filter (fun z => z.1 < z.2 ∧ c z.1 = c z.2 ∧
        Bool.xor (g (z.1, p z.2)) (g (z.2, p z.1)) ≠ Bool.xor (s z.1) (s z.2)) := by
    ext z
    simp only [sameColorPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      hcolor, conflict, xor_true_iff_ne, and_assoc]
  rw [hfilter] at hgood
  rw [ham]
  exact Nat.mul_lt_mul_of_pos_left hgood (by decide)

def poolColor (r c : Bool) : Fin 3 :=
  if r then (if c then 0 else 1) else (if c then 2 else 0)

theorem poolCollision (r₁ c₁ r₂ c₂ : Bool)
    (h : poolColor r₁ c₁ = poolColor r₂ c₂) : (r₁ || c₂) = (r₂ || c₁) := by
  cases r₁ <;> cases c₁ <;> cases r₂ <;> cases c₂ <;> simp [poolColor] at h ⊢

theorem parityOfSwap (u v r₁ r₂ c₁ c₂ : Bool)
    (h : Bool.xor u (Bool.xor r₁ c₂) = Bool.xor v (Bool.xor r₂ c₁)) :
    Bool.xor u v = Bool.xor (Bool.xor r₁ c₁) (Bool.xor r₂ c₂) := by
  cases u <;> cases v <;> cases r₁ <;> cases r₂ <;> cases c₁ <;> cases c₂ <;> simp at h ⊢


/-- The union of the fibres over a set `A` of types has `A.card * b` elements. -/
lemma td_fibre_card {m b N : ℕ} (typ : Fin N → Fin m)
    (h : ∀ t, (Finset.univ.filter (fun x => typ x = t)).card = b) (A : Finset (Fin m)) :
    (Finset.univ.filter (fun x => typ x ∈ A)).card = A.card * b := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise (f := typ)
    (s := Finset.univ.filter (fun x => typ x ∈ A)) (t := A)
    (fun x hx => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2)
  have hterm : ∀ u ∈ A,
      ((Finset.univ.filter (fun x => typ x ∈ A)).filter (fun x => typ x = u)).card = b := by
    intro u hu
    refine (congrArg Finset.card ?_).trans (h u)
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, hx⟩
      exact hx
    · intro hx
      exact ⟨by rw [hx]; exact hu, hx⟩
  exact hfib.trans (Finset.sum_const_nat hterm)

/-- The counting contradiction behind the marriage condition: `s < r` types cannot absorb `r` full rows when
every cell outside holds at most `w - 1` elements. -/
lemma td_arith {m b w H r s z : ℕ} (hsr : s < r) (hrm : r ≤ m)
    (h1 : r * b ≤ s * b + z) (h2 : z ≤ (w - 1) * (r * (m - s)))
    (hH : r * (m + 1 - r) ≤ H) (hw : (w - 1) * H < b) : False := by
  obtain ⟨t, rfl⟩ : ∃ t, r = s + 1 + t := ⟨r - s - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, m = s + 1 + t + d := ⟨m - (s + 1 + t), by omega⟩
  have e1 : s + 1 + t + d - s = t + 1 + d := by omega
  have e2 : s + 1 + t + d + 1 - (s + 1 + t) = d + 1 := by omega
  rw [e1] at h2
  rw [e2] at hH
  have h3 : (t + 1) * b ≤ z := by
    have e3 : (s + 1 + t) * b = s * b + (t + 1) * b := by ring
    rw [e3] at h1
    exact Nat.le_of_add_le_add_left h1
  have h4 : t + 1 + d ≤ (t + 1) * (d + 1) := by
    have e4 : (t + 1) * (d + 1) = t * d + (t + 1 + d) := by ring
    rw [e4]
    exact Nat.le_add_left _ _
  have h5 : (s + 1 + t) * (t + 1 + d) ≤ (t + 1) * H := by
    calc (s + 1 + t) * (t + 1 + d) ≤ (s + 1 + t) * ((t + 1) * (d + 1)) :=
          Nat.mul_le_mul_left _ h4
      _ = (t + 1) * ((s + 1 + t) * (d + 1)) := by ring
      _ ≤ (t + 1) * H := Nat.mul_le_mul_left _ hH
  have h6 : (t + 1) * b ≤ (t + 1) * ((w - 1) * H) := by
    calc (t + 1) * b ≤ z := h3
      _ ≤ (w - 1) * ((s + 1 + t) * (t + 1 + d)) := h2
      _ ≤ (w - 1) * ((t + 1) * H) := Nat.mul_le_mul_left _ h5
      _ = (t + 1) * ((w - 1) * H) := by ring
  have h7 : (t + 1) * ((w - 1) * H) < (t + 1) * b :=
    Nat.mul_lt_mul_of_pos_left hw (Nat.succ_pos t)
  exact absurd h6 (not_le.mpr h7)

/-- Marcus and Ree: a type matrix with all row and column sums `b` has a diagonal whose cells all hold at least
`w` elements, as soon as `(w - 1) * H < b` where `H` bounds `r * (m + 1 - r)`. -/
theorem thickDiagonal {m b N w H : ℕ} (typ₁ typ₂ : Fin N → Fin m)
    (h₁ : ∀ t, (Finset.univ.filter (fun x => typ₁ x = t)).card = b)
    (h₂ : ∀ t, (Finset.univ.filter (fun x => typ₂ x = t)).card = b)
    (hH : ∀ r : ℕ, r ≤ m → r * (m + 1 - r) ≤ H)
    (hw : (w - 1) * H < b) :
    ∃ (σ : Fin m → Fin m) (e : Fin m → Fin w → Fin N),
      Function.Bijective σ ∧
      Function.Injective (fun z : Fin m × Fin w => e z.1 z.2) ∧
      (∀ t j, typ₁ (e t j) = t) ∧ (∀ t j, typ₂ (e t j) = σ t) := by
  classical
  -- the cell of row type u and column type v, and the set T u of column types with a thick cell
  obtain ⟨cell, hcell⟩ : ∃ cell : Fin m → Fin m → Finset (Fin N),
      ∀ u v x, x ∈ cell u v ↔ (typ₁ x = u ∧ typ₂ x = v) :=
    ⟨fun u v => Finset.univ.filter (fun x => typ₁ x = u ∧ typ₂ x = v), fun u v x => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
  obtain ⟨T, hT⟩ : ∃ T : Fin m → Finset (Fin m), ∀ u v, v ∈ T u ↔ w ≤ (cell u v).card :=
    ⟨fun u => Finset.univ.filter (fun v => w ≤ (cell u v).card), fun u v => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
  have hsmall : ∀ u v, v ∉ T u → (cell u v).card ≤ w - 1 := by
    intro u v hv
    have hnle : ¬ w ≤ (cell u v).card := fun hle => hv ((hT u v).mpr hle)
    omega
  -- the marriage condition
  have hall : ∀ A : Finset (Fin m), A.card ≤ (A.biUnion T).card := by
    intro A
    by_contra hlt
    have hsr : (A.biUnion T).card < A.card := not_le.mp hlt
    have hrm : A.card ≤ m := by
      have hc := Finset.card_le_univ A
      rwa [Fintype.card_fin] at hc
    have hsub : Finset.univ.filter (fun x => typ₁ x ∈ A) ⊆
        Finset.univ.filter (fun x => typ₂ x ∈ A.biUnion T) ∪
          Finset.univ.filter (fun x => typ₁ x ∈ A ∧ typ₂ x ∉ A.biUnion T) := by
      intro x hx
      by_cases hxB : typ₂ x ∈ A.biUnion T
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxB⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2, hxB⟩)
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [td_fibre_card typ₁ h₁ A, td_fibre_card typ₂ h₂ (A.biUnion T)] at h1
    have hZ : (Finset.univ.filter (fun x => typ₁ x ∈ A ∧ typ₂ x ∉ A.biUnion T)).card ≤
        (w - 1) * (A ×ˢ (A.biUnion T)ᶜ).card := by
      refine Finset.card_le_mul_card_image_of_maps_to (f := fun x => (typ₁ x, typ₂ x))
        ?_ (w - 1) ?_
      · intro x hx
        exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hx).2.1,
          Finset.mem_compl.mpr (Finset.mem_filter.mp hx).2.2⟩
      · intro p hp
        have hpA : p.1 ∈ A := (Finset.mem_product.mp hp).1
        have hpB : p.2 ∉ A.biUnion T := Finset.mem_compl.mp (Finset.mem_product.mp hp).2
        have hnT : p.2 ∉ T p.1 := fun hmem => hpB (Finset.mem_biUnion.mpr ⟨p.1, hpA, hmem⟩)
        refine (Finset.card_le_card ?_).trans (hsmall p.1 p.2 hnT)
        intro y hy
        have hyp := (Finset.mem_filter.mp hy).2
        exact (hcell p.1 p.2 y).mpr ⟨congrArg Prod.fst hyp, congrArg Prod.snd hyp⟩
    rw [Finset.card_product, Finset.card_compl, Fintype.card_fin] at hZ
    exact td_arith hsr hrm h1 hZ (hH A.card hrm) hw
  obtain ⟨σ, hσ, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective T).mp hall
  -- w elements in every cell of the diagonal
  have hex : ∀ u, ∃ S : Finset (Fin N), S ⊆ cell u (σ u) ∧ S.card = w := fun u =>
    Finset.exists_subset_card_eq ((hT u (σ u)).mp (hmem u))
  choose S hS hcard using hex
  have hval : ∀ u j, typ₁ ((S u).orderEmbOfFin (hcard u) j) = u ∧
      typ₂ ((S u).orderEmbOfFin (hcard u) j) = σ u := fun u j =>
    (hcell u (σ u) _).mp (hS u (Finset.orderEmbOfFin_mem (S u) (hcard u) j))
  refine ⟨σ, fun u j => (S u).orderEmbOfFin (hcard u) j,
    Finite.injective_iff_bijective.mp hσ, ?_, fun u j => (hval u j).1, fun u j => (hval u j).2⟩
  rintro ⟨u, j⟩ ⟨u', j'⟩ hz
  have hz' : (S u).orderEmbOfFin (hcard u) j = (S u').orderEmbOfFin (hcard u') j' := hz
  have huu : u = u' := (hval u j).1.symm.trans ((congrArg typ₁ hz').trans (hval u' j').1)
  subst huu
  exact congrArg (Prod.mk _) (((S _).orderEmbOfFin (hcard _)).injective hz')

/-- After writing `z₁` at `x` and `z₂` at `y ≠ x`, the word reads `z₁` at `x`. -/
lemma sc_read_x {m w : ℕ} (x y : Fin m) (hxy : x ≠ y) (z₁ z₂ : Fin w) (f : Fin m → Fin w) :
    Function.update (Function.update f x z₁) y z₂ x = z₁ := by
  rw [Function.update_of_ne hxy, Function.update_self]

/-- After writing `z₁` at `x` and `z₂` at `y`, the word reads `z₂` at `y`. -/
lemma sc_read_y {m w : ℕ} (x y : Fin m) (z₁ z₂ : Fin w) (f : Fin m → Fin w) :
    Function.update (Function.update f x z₁) y z₂ y = z₂ := by
  rw [Function.update_self]

/-- Writing two values at `x` and `y` and then writing the old values back gives the old word. -/
lemma sc_restore {m w : ℕ} (x y : Fin m) (z₁ z₂ : Fin w) (f : Fin m → Fin w) :
    Function.update (Function.update (Function.update (Function.update f x z₁) y z₂) x (f x)) y (f y)
      = f := by
  funext i
  by_cases hiy : i = y
  · rw [hiy, Function.update_self]
  · rw [Function.update_of_ne hiy]
    by_cases hix : i = x
    · rw [hix, Function.update_self]
    · rw [Function.update_of_ne hix, Function.update_of_ne hiy, Function.update_of_ne hix]

/-- Fixing two coordinates of a word: `w * w` times the number of words with `P (f x) (f y)` is `w ^ m` times
the number of pairs with `P`. -/
theorem sum_two_coords {m w : ℕ} (x y : Fin m) (hxy : x ≠ y) (P : Fin w → Fin w → Prop)
    [DecidableRel P] :
    w * w * (Finset.univ.filter (fun f : Fin m → Fin w => P (f x) (f y))).card =
      w ^ m * (Finset.univ.filter (fun z : Fin w × Fin w => P z.1 z.2)).card := by
  -- Both sides count pairs (z, f) of a pair of letters and a word: the left side those with `P (f x) (f y)`,
  -- the right side those with `P z.1 z.2`. Exchanging z with the two coordinates of f maps one set onto the other.
  have h1 : ((Finset.univ : Finset ((Fin w × Fin w) × (Fin m → Fin w))).filter
      (fun p => P (p.2 x) (p.2 y))).card =
      w * w * (Finset.univ.filter (fun f : Fin m → Fin w => P (f x) (f y))).card := by
    have hs : (Finset.univ : Finset ((Fin w × Fin w) × (Fin m → Fin w))).filter
        (fun p => P (p.2 x) (p.2 y)) =
        (Finset.univ : Finset (Fin w × Fin w)) ×ˢ
          (Finset.univ.filter (fun f : Fin m → Fin w => P (f x) (f y))) := by
      ext p
      simp
    rw [hs, Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have h2 : ((Finset.univ : Finset ((Fin w × Fin w) × (Fin m → Fin w))).filter
      (fun p => P p.1.1 p.1.2)).card =
      (Finset.univ.filter (fun z : Fin w × Fin w => P z.1 z.2)).card * w ^ m := by
    have hs : (Finset.univ : Finset ((Fin w × Fin w) × (Fin m → Fin w))).filter
        (fun p => P p.1.1 p.1.2) =
        (Finset.univ.filter (fun z : Fin w × Fin w => P z.1 z.2)) ×ˢ
          (Finset.univ : Finset (Fin m → Fin w)) := by
      ext p
      simp
    rw [hs, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h3 : ((Finset.univ : Finset ((Fin w × Fin w) × (Fin m → Fin w))).filter
      (fun p => P (p.2 x) (p.2 y))).card =
      ((Finset.univ : Finset ((Fin w × Fin w) × (Fin m → Fin w))).filter
        (fun p => P p.1.1 p.1.2)).card := by
    refine Finset.card_bij'
      (fun p _ => ((p.2 x, p.2 y), Function.update (Function.update p.2 x p.1.1) y p.1.2))
      (fun p _ => ((p.2 x, p.2 y), Function.update (Function.update p.2 x p.1.1) y p.1.2)) ?_ ?_ ?_ ?_
    · rintro ⟨⟨z₁, z₂⟩, f⟩ hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_univ _, hp.2⟩
    · rintro ⟨⟨z₁, z₂⟩, f⟩ hp
      rw [Finset.mem_filter] at hp ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      show P (Function.update (Function.update f x z₁) y z₂ x)
        (Function.update (Function.update f x z₁) y z₂ y)
      rw [sc_read_x x y hxy z₁ z₂ f, sc_read_y x y z₁ z₂ f]
      exact hp.2
    · rintro ⟨⟨z₁, z₂⟩, f⟩ _
      show ((Function.update (Function.update f x z₁) y z₂ x,
          Function.update (Function.update f x z₁) y z₂ y),
        Function.update (Function.update (Function.update (Function.update f x z₁) y z₂) x (f x)) y (f y))
        = ((z₁, z₂), f)
      rw [sc_read_x x y hxy z₁ z₂ f, sc_read_y x y z₁ z₂ f, sc_restore x y z₁ z₂ f]
    · rintro ⟨⟨z₁, z₂⟩, f⟩ _
      show ((Function.update (Function.update f x z₁) y z₂ x,
          Function.update (Function.update f x z₁) y z₂ y),
        Function.update (Function.update (Function.update (Function.update f x z₁) y z₂) x (f x)) y (f y))
        = ((z₁, z₂), f)
      rw [sc_read_x x y hxy z₁ z₂ f, sc_read_y x y z₁ z₂ f, sc_restore x y z₁ z₂ f]
  exact h1.symm.trans (h3.trans (h2.trans (Nat.mul_comm _ _)))

theorem lossOfCells {a m w N q : ℕ} (hw : 0 < w)
    (typ : Fin N → Fin m) (g : Fin m → Fin m → Bool)
    (hard : ∀ (p : Equiv.Perm (Fin m)) (s : Fin m → Bool) (c : Fin m → Fin (3^q)),
      a*m < 4 * ((Finset.univ : Finset (Fin m × Fin m)).filter (fun z =>
        z.1 < z.2 ∧ c z.1 = c z.2 ∧ Bool.xor (g z.1 (p z.2)) (g z.2 (p z.1)) ≠
          Bool.xor (s z.1) (s z.2))).card)
    (π : Equiv.Perm (Fin N)) (rf cf : Fin N → Bool)
    (R C : Fin q → Finset (Fin N)) (out : Finset (Fin N) → (Fin q → Bool) → Bool)
    (σ : Fin m → Fin m) (hσ : Function.Bijective σ)
    (e : Fin m → Fin w → Fin N)
    (hinj : Function.Injective (fun z : Fin m × Fin w => e z.1 z.2))
    (hrow : ∀ t j, typ (e t j) = t)
    (hcol : ∀ t j, typ (π (e t j)) = σ t) :
    w * w * (a * m) < 4 * ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
      out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (g (typ z.1) (typ (π z.2))) (Bool.xor (rf z.1) (cf (π z.2))))).card := by
  classical
  let score (x y : Fin N) : Bool :=
    out {x,y} (fun j => decide (x ∈ R j ∨ π y ∈ C j))
  let truth (x y : Fin N) : Bool :=
    Bool.xor (g (typ x) (typ (π y))) (Bool.xor (rf x) (cf (π y)))
  let err : Finset (Fin N × Fin N) := Finset.univ.filter fun z => score z.1 z.2 ≠ truth z.1 z.2
  let p : Equiv.Perm (Fin m) := Equiv.ofBijective σ hσ
  let sX (X : Fin N) : Bool := Bool.xor (rf X) (cf (π X))
  let dig (X : Fin N) (j : Fin q) : Fin 3 :=
    poolColor (decide (X ∈ R j)) (decide (π X ∈ C j))
  let code : (Fin q → Fin 3) ≃ Fin (3^q) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin])
  -- the conflict of the cells (e x j1, e y j2) and (e y j2, e x j1)
  let Cb (x y : Fin m) (j1 j2 : Fin w) : Prop :=
    code (dig (e x j1)) = code (dig (e y j2)) ∧
      Bool.xor (g x (p y)) (g y (p x)) ≠ Bool.xor (sX (e x j1)) (sX (e y j2))
  let Bad (f : Fin m → Fin w) : Finset (Fin m × Fin m) := Finset.univ.filter fun z =>
    z.1 < z.2 ∧ Cb z.1 z.2 (f z.1) (f z.2)
  let Q : Finset ((Fin m × Fin m) × (Fin w × Fin w)) := Finset.univ.filter fun u =>
    u.1.1 < u.1.2 ∧ Cb u.1.1 u.1.2 u.2.1 u.2.2
  let A (z : Fin m × Fin m) : Finset (Fin m → Fin w) := Finset.univ.filter fun f =>
    z.1 < z.2 ∧ Cb z.1 z.2 (f z.1) (f z.2)
  let B (z : Fin m × Fin m) : Finset (Fin w × Fin w) := Finset.univ.filter fun jj =>
    z.1 < z.2 ∧ Cb z.1 z.2 jj.1 jj.2
  let selected : ((Fin m × Fin m) × (Fin w × Fin w)) → Fin N × Fin N := fun u =>
    let X := e u.1.1 u.2.1
    let Y := e u.1.2 u.2.2
    if score X Y ≠ truth X Y then (X,Y) else (Y,X)
  -- a word picks one representative of every type, so the hard table gives many conflicts on it
  have hBad : ∀ f : Fin m → Fin w, a * m < 4 * (Bad f).card := by
    intro f
    have h := hard p (fun t => sX (e t (f t))) (fun t => code (dig (e t (f t))))
    refine lt_of_lt_of_le h (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
    intro z hz
    obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3⟩
  -- every conflict is paid for by an error in one of the two transposed cells
  have hmem : ∀ u ∈ Q, selected u ∈ err := by
    rintro ⟨⟨x,y⟩,⟨j1,j2⟩⟩ hu
    have hu' : x < y ∧ Cb x y j1 j2 := (Finset.mem_filter.mp hu).2
    obtain ⟨_, hcolor, hconf⟩ := hu'
    have hdig := code.injective hcolor
    have hpools : (fun j => decide (e x j1 ∈ R j ∨ π (e y j2) ∈ C j)) =
        (fun j => decide (e y j2 ∈ R j ∨ π (e x j1) ∈ C j)) := by
      funext j
      have decOr (P Q : Prop) [Decidable P] [Decidable Q] :
          decide (P ∨ Q) = (decide P || decide Q) := by
        by_cases hp : P <;> by_cases hq : Q <;> simp [hp,hq]
      simpa only [decOr] using poolCollision (decide (e x j1 ∈ R j))
        (decide (π (e x j1) ∈ C j)) (decide (e y j2 ∈ R j))
        (decide (π (e y j2) ∈ C j)) (congrFun hdig j)
    have hscore : score (e x j1) (e y j2) = score (e y j2) (e x j1) := by
      change out {e x j1, e y j2} (fun j => decide (e x j1 ∈ R j ∨ π (e y j2) ∈ C j)) =
        out {e y j2, e x j1} (fun j => decide (e y j2 ∈ R j ∨ π (e x j1) ∈ C j))
      rw [hpools, Finset.pair_comm]
    have htruth : truth (e x j1) (e y j2) ≠ truth (e y j2) (e x j1) := by
      intro ht
      apply hconf
      have ht' : Bool.xor (g (typ (e x j1)) (typ (π (e y j2))))
            (Bool.xor (rf (e x j1)) (cf (π (e y j2)))) =
          Bool.xor (g (typ (e y j2)) (typ (π (e x j1))))
            (Bool.xor (rf (e y j2)) (cf (π (e x j1)))) := ht
      rw [hrow, hrow, hcol, hcol] at ht'
      exact parityOfSwap _ _ _ _ _ _ ht'
    change (if score (e x j1) (e y j2) ≠ truth (e x j1) (e y j2) then (e x j1, e y j2)
      else (e y j2, e x j1)) ∈ err
    split_ifs with h
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [← hscore, not_ne_iff.mp h]; exact htruth⟩
  have hselect : Set.InjOn selected (Q : Set ((Fin m × Fin m) × (Fin w × Fin w))) := by
    rintro ⟨⟨x,y⟩,⟨j1,j2⟩⟩ h₁ ⟨⟨u,v⟩,⟨k1,k2⟩⟩ h₂ heq
    have hx : x < y := (Finset.mem_filter.mp h₁).2.1
    have hu : u < v := (Finset.mem_filter.mp h₂).2.1
    have hpair {x y : Fin m} {j k : Fin w} (h : e x j = e y k) : x = y ∧ j = k := by
      have h' : (x,j) = (y,k) := hinj h
      exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
    have heq' : (if score (e x j1) (e y j2) ≠ truth (e x j1) (e y j2) then (e x j1, e y j2)
        else (e y j2, e x j1)) =
      (if score (e u k1) (e v k2) ≠ truth (e u k1) (e v k2) then (e u k1, e v k2)
        else (e v k2, e u k1)) := heq
    split_ifs at heq' <;>
      have hfst := hpair (congrArg Prod.fst heq') <;>
      have hsnd := hpair (congrArg Prod.snd heq') <;>
      rcases hfst with ⟨rfl, rfl⟩ <;> rcases hsnd with ⟨rfl, rfl⟩ <;>
      first | rfl | exact (lt_asymm hx hu).elim
  have hle : Q.card ≤ err.card := Finset.card_le_card_of_injOn selected hmem hselect
  -- the double count: a conflict of two cells lies on the same share of all words
  have hswap : ∑ f : Fin m → Fin w, (Bad f).card = ∑ z : Fin m × Fin m, (A z).card := by
    simp only [Bad, A, Finset.card_filter]
    exact Finset.sum_comm
  have hQ : Q.card = ∑ z : Fin m × Fin m, (B z).card := by
    simp only [Q, B, Finset.card_filter]
    exact Fintype.sum_prod_type _
  have hz : ∀ z : Fin m × Fin m, w * w * (A z).card = w ^ m * (B z).card := by
    intro z
    by_cases h : z.1 < z.2
    · have h2 := sum_two_coords z.1 z.2 (ne_of_lt h) (Cb z.1 z.2)
      have hA : A z = Finset.univ.filter (fun f : Fin m → Fin w => Cb z.1 z.2 (f z.1) (f z.2)) := by
        ext f
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, h]
      have hB : B z = Finset.univ.filter (fun jj : Fin w × Fin w => Cb z.1 z.2 jj.1 jj.2) := by
        ext jj
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, h]
      rw [hA, hB]
      exact h2
    · have hA : A z = ∅ := by
        ext f
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, h, false_and,
          Finset.notMem_empty]
      have hB : B z = ∅ := by
        ext jj
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, h, false_and,
          Finset.notMem_empty]
      rw [hA, hB, Finset.card_empty, Finset.card_empty, Nat.mul_zero, Nat.mul_zero]
  have hdc : w * w * (∑ f : Fin m → Fin w, (Bad f).card) = w ^ m * Q.card := by
    rw [hswap, hQ, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => hz z)
  -- all words together
  have hne : (Finset.univ : Finset (Fin m → Fin w)).Nonempty :=
    ⟨fun _ => ⟨0, hw⟩, Finset.mem_univ _⟩
  have hsum : (∑ _f : Fin m → Fin w, a * m) < ∑ f : Fin m → Fin w, 4 * (Bad f).card :=
    Finset.sum_lt_sum_of_nonempty hne (fun f _ => hBad f)
  have hconst : (∑ _f : Fin m → Fin w, a * m) = w ^ m * (a * m) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, smul_eq_mul]
  rw [hconst, ← Finset.mul_sum] at hsum
  refine Nat.lt_of_mul_lt_mul_left (a := w ^ m) ?_
  calc
    w ^ m * (w * w * (a * m)) = w * w * (w ^ m * (a * m)) := by ring
    _ < w * w * (4 * ∑ f : Fin m → Fin w, (Bad f).card) :=
      Nat.mul_lt_mul_of_pos_left hsum (Nat.mul_pos hw hw)
    _ = 4 * (w * w * ∑ f : Fin m → Fin w, (Bad f).card) := by ring
    _ = 4 * (w ^ m * Q.card) := by rw [hdc]
    _ ≤ 4 * (w ^ m * err.card) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hle)
    _ = w ^ m * (4 * err.card) := by ring

end PEqualNP.Outside.L_meta_25722

theorem PEqualNP.Outside.L_meta_25722 : ∀ (a k : ℕ), 16 ≤ a → 2^(2*a) ≤ k →
  let n := 2^k
  let I := Fin n
  let Table := I → I → Bool
  let loss := fun (G : Table) (q : ℕ) (π : Equiv.Perm I) (rowFlip colFlip : I → Bool)
      (R C : Fin q → Finset I) (out : Finset I → (Fin q → Bool) → Bool) =>
    ((Finset.univ : Finset (I × I)).filter (fun z =>
      out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G z.1 (π z.2)) (Bool.xor (rowFlip z.1) (colFlip (π z.2))))).card
  let m := 2^a
  let H := (m+1)^2/4
  ∃ G : Table,
    PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k := k) (l := k) G)
      (3*2^(2*a)) ∧
    ∀ q : ℕ, 8*a*3^q ≤ 2^a →
      ∀ (π : Equiv.Perm I) (rowFlip colFlip : I → Bool)
        (R C : Fin q → Finset I) (out : Finset I → (Fin q → Bool) → Bool),
        a*n^2 < 4*m*H^2*loss G q π rowFlip colFlip R C out := by
  intro a k ha hk n I Table loss m H
  have hak : a ≤ k := by
    calc
      a ≤ 2^a := Nat.lt_two_pow_self.le
      _ ≤ 2^(2*a) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ k := hk
  obtain ⟨g, hg⟩ := PEqualNP.Outside.L_meta_25722.existsBase a ha
  let G : Table := fun x y => g (PEqualNP.Outside.L_meta_25722.lowType a k x) (PEqualNP.Outside.L_meta_25722.lowType a k y)
  refine ⟨G, ?_, ?_⟩
  · let select : Fin (a+a) → Fin (k+k) := Fin.append
      (fun i => Fin.castAdd k (Fin.castLE hak i)) (fun i => Fin.natAdd k (Fin.castLE hak i))
    let f (bits : Fin (a+a) → Bool) : Bool :=
      g (Fin.ofNat (2^a) (PEqualNP.MetaComplexity.tableIndex (fun i : Fin a => bits (Fin.castAdd a i))))
        (Fin.ofNat (2^a) (PEqualNP.MetaComplexity.tableIndex (fun i : Fin a => bits (Fin.natAdd a i))))
    have heval : (fun (x : Fin (k+k) → Bool) => f (fun j => x (select j))) =
        PEqualNP.Represents.adjFun G := by
      funext x
      simp only [PEqualNP.Represents.adjFun, G, PEqualNP.Outside.L_meta_25722.lowIndex hak, f, select, Fin.append_left,
        Fin.append_right]
    obtain ⟨c, hc, hsize, hfun⟩ := heval ▸ PEqualNP.Outside.L_meta_25722.lookupSize select f
    refine ⟨c, hc, hsize.trans ?_, hfun⟩
    exact Nat.mul_le_mul_left 3 (by rw [two_mul])
  · intro q hq π rf cf R C out
    have hl (t : Fin (2^a)) :
        (Finset.univ.filter (fun x => PEqualNP.Outside.L_meta_25722.lowType a k x = t)).card = 2^(k-a) :=
      PEqualNP.Outside.L_meta_25722.fibersLow hak (Equiv.refl _) t
    have hbm : 2^(k-a) * 2^a = n := by dsimp [n]; rw [← pow_add, Nat.sub_add_cancel hak]
    have hm2 : 2 ≤ m := by
      calc 2 = 2^1 := rfl
        _ ≤ 2^a := Nat.pow_le_pow_right (by decide) (by omega)
    have hHpos : 0 < H := Nat.div_pos (by nlinarith) (by decide)
    have hH : ∀ r : ℕ, r ≤ m → r * (m + 1 - r) ≤ H := by
      intro r hr
      obtain ⟨s, hs⟩ : ∃ s, m + 1 = r + s := ⟨m + 1 - r, by omega⟩
      have h1 : m + 1 - r = s := by omega
      rw [h1]
      refine (Nat.le_div_iff_mul_le (by decide)).mpr ?_
      rw [hs]
      nlinarith [two_mul_le_add_sq r s]
    have hb : 0 < 2^(k-a) := Nat.two_pow_pos _
    have hw : ((2^(k-a) - 1) / H + 1 - 1) * H < 2^(k-a) := by
      rw [Nat.add_sub_cancel]
      exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) (by omega)
    have hbw : 2^(k-a) ≤ H * ((2^(k-a) - 1) / H + 1) := by
      have := Nat.lt_div_mul_add (a := 2^(k-a) - 1) hHpos
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
      omega
    obtain ⟨σ, e, hσ, he, hr, hc⟩ := PEqualNP.Outside.L_meta_25722.thickDiagonal (w := (2^(k-a) - 1) / H + 1)
      (PEqualNP.Outside.L_meta_25722.lowType a k) (fun x => PEqualNP.Outside.L_meta_25722.lowType a k (π x)) hl (PEqualNP.Outside.L_meta_25722.fibersLow hak π) hH hw
    have key := PEqualNP.Outside.L_meta_25722.lossOfCells (Nat.succ_pos _) (PEqualNP.Outside.L_meta_25722.lowType a k) g
      (hg (3^q) hq) π rf cf R C out σ hσ e he hr hc
    change a * n^2 < 4 * m * H^2 * loss G q π rf cf R C out
    have key' : ((2^(k-a) - 1) / H + 1) * ((2^(k-a) - 1) / H + 1) * (a * m) <
        4 * loss G q π rf cf R C out := key
    calc a * n^2 = a * (2^(k-a) * m)^2 := by rw [← hbm]
      _ ≤ a * ((H * ((2^(k-a) - 1) / H + 1)) * m)^2 := by gcongr
      _ = (m * H^2) * (((2^(k-a) - 1) / H + 1) * ((2^(k-a) - 1) / H + 1) * (a * m)) := by ring
      _ < (m * H^2) * (4 * loss G q π rf cf R C out) :=
          Nat.mul_lt_mul_of_pos_left key' (by positivity)
      _ = 4 * m * H^2 * loss G q π rf cf R C out := by ring
