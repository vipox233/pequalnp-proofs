import PEqualNP.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Perm
import Mathlib.Combinatorics.Hall.Finite

namespace PEqualNP.Outside.L_meta_25715_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def literalInput {n : ℕ} (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ List.ofFn (fun i => !x i)

private def allowed (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem allowed_append {g h : List Gate} (hg : allowed g) (hh : allowed h) :
    allowed (g ++ h) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hg t ht
  · exact hh t ht

private def values (gs : List Gate) (input : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires input

private theorem values_append (g h : List Gate) (input : List Bool) :
    values (g ++ h) input = values h (values g input) := by
  exact List.foldl_append

private theorem values_length (gs : List Gate) (input : List Bool) :
    (values gs input).length = input.length + gs.length := by
  induction gs generalizing input with
  | nil => simp [values, Circuit.wires]
  | cons g gs ih =>
    unfold values Circuit.wires at ih ⊢
    simp only [List.foldl_cons, List.length_cons, ih, List.length_append, List.length_nil]
    omega

private theorem values_preserve (gs : List Gate) (input : List Bool) {i : ℕ}
    (hi : i < input.length) : (values gs input).getD i false = input.getD i false := by
  induction gs generalizing input with
  | nil => rfl
  | cons g gs ih =>
    unfold values Circuit.wires at ih ⊢
    simp only [List.foldl_cons]
    rw [ih _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private def atWire {n : ℕ} (gs : List Gate) (i : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  i < n + n + gs.length ∧ ∀ x, (values gs (literalInput x)).getD i false = f x

private theorem atWire_extend {n : ℕ} {gs : List Gate} (h : List Gate)
    {i : ℕ} {f : (Fin n → Bool) → Bool} (hf : atWire gs i f) : atWire (gs ++ h) i f := by
  refine ⟨by have := hf.1; simp; omega, fun x => ?_⟩
  rw [values_append, values_preserve]
  · exact hf.2 x
  · simpa [values_length, literalInput] using hf.1

private theorem atWire_snoc {n : ℕ} (gs : List Gate) (g : Gate) :
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

private theorem andWire {n : ℕ} {gs : List Gate} {i j : ℕ}
    {f g : (Fin n → Bool) → Bool} (hf : atWire gs i f) (hg : atWire gs j g) :
    atWire (gs ++ [⟨GateOp.and, [i,j]⟩]) (n+n+gs.length) (fun x => f x && g x) := by
  refine ⟨(atWire_snoc (n := n) gs ⟨GateOp.and, [i,j]⟩).1, fun x => ?_⟩
  rw [(atWire_snoc (n := n) gs ⟨GateOp.and, [i,j]⟩).2 x]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
    Bool.and_true, hf.2 x, hg.2 x]

private theorem orWire {n : ℕ} {gs : List Gate} {i j : ℕ}
    {f g : (Fin n → Bool) → Bool} (hf : atWire gs i f) (hg : atWire gs j g) :
    atWire (gs ++ [⟨GateOp.or, [i,j]⟩]) (n+n+gs.length) (fun x => f x || g x) := by
  refine ⟨(atWire_snoc (n := n) gs ⟨GateOp.or, [i,j]⟩).1, fun x => ?_⟩
  rw [(atWire_snoc (n := n) gs ⟨GateOp.or, [i,j]⟩).2 x]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false, hf.2 x, hg.2 x]

private theorem multiplex {n : ℕ} {gs : List Gate} {i j u v : ℕ}
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

private theorem lookupExtension {n : ℕ} (d : ℕ) (sel : Fin d → Fin n)
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

private theorem lookupSize {n d : ℕ} (sel : Fin d → Fin n) (f : (Fin d → Bool) → Bool) :
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

private def lowType (a k : ℕ) (x : Fin (2^k)) : Fin (2^a) := Fin.ofNat (2^a) x.val

private theorem lowIndex {a k : ℕ} (hak : a ≤ k) (x : Fin k → Bool) :
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

private theorem fibersLow {a k : ℕ} (hak : a ≤ k) (π : Equiv.Perm (Fin (2^k)))
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

private def sameColorPairs {m d : ℕ} (c : Fin m → Fin d) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun z => z.1 < z.2 ∧ c z.1 = c z.2)

private lemma sameColorPairs_bound {m d : ℕ} (c : Fin m → Fin d) :
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

private def bitWeight {I : Type*} [Fintype I] (b : I → Bool) : ℕ :=
  (Finset.univ.filter (fun i => b i = true)).card

private noncomputable def lowWords (I : Type*) [Fintype I] (t : ℕ) : Finset (I → Bool) := by
  classical exact Finset.univ.filter (fun b => bitWeight b ≤ t)

private lemma card_lowWords {I : Type*} [Fintype I] (k t : ℕ)
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

private abbrev Table (m : ℕ) := Fin m × Fin m → Bool

private def conflict {m : ℕ} (g : Table m) (p : Equiv.Perm (Fin m))
    (s : Fin m → Bool) (z : Fin m × Fin m) : Bool :=
  Bool.xor (Bool.xor (g (z.1, p z.2)) (g (z.2, p z.1))) (Bool.xor (s z.1) (s z.2))

private lemma xor_true_iff_ne (x y : Bool) : Bool.xor x y = true ↔ x ≠ y := by
  cases x <;> cases y <;> decide

private def badTables {m d : ℕ} (p : Equiv.Perm (Fin m)) (s : Fin m → Bool)
    (c : Fin m → Fin d) (t : ℕ) : Finset (Table m) :=
  Finset.univ.filter (fun g => ((sameColorPairs c).filter (fun z => conflict g p s z = true)).card ≤ t)

private def tableColumns {m : ℕ} (p : Equiv.Perm (Fin m)) : Table m ≃ Table m where
  toFun g z := g (z.1, p z.2)
  invFun g z := g (z.1, p.symm z.2)
  left_inv g := by funext z; rcases z with ⟨i, j⟩; simp
  right_inv g := by funext z; rcases z with ⟨i, j⟩; simp

private def tableTwist {m : ℕ} (S : Finset (Fin m × Fin m)) (s : Fin m → Bool)
    (g : Table m) (z : Fin m × Fin m) : Bool :=
  if z ∈ S then Bool.xor (Bool.xor (g z) (g z.swap)) (Bool.xor (s z.1) (s z.2)) else g z

private lemma xor_twice (x y z : Bool) :
    Bool.xor (Bool.xor (Bool.xor (Bool.xor x y) z) y) z = x := by
  cases x <;> cases y <;> cases z <;> decide

private lemma tableTwist_involution {m : ℕ} (S : Finset (Fin m × Fin m)) (s : Fin m → Bool)
    (hS : ∀ z ∈ S, z.1 < z.2) : Function.Involutive (tableTwist S s) := by
  intro g
  funext z
  by_cases hz : z ∈ S
  · have hrev : z.swap ∉ S := fun h => (not_lt_of_ge (le_of_lt (hS z hz))) (hS z.swap h)
    simpa only [tableTwist, ite_eq_left hz, ite_eq_right hrev] using
      xor_twice (g z) (g z.swap) (Bool.xor (s z.1) (s z.2))
  · simp [tableTwist, hz]

private lemma card_badTables {m d k t : ℕ} (p : Equiv.Perm (Fin m)) (s : Fin m → Bool)
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

private lemma card_configurations {a m d : ℕ} (hm : m = 2 ^ a) (hd : d ≤ m) :
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

private lemma existsBase (a : ℕ) (ha : 16 ≤ a) : let m := 2^a;
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

private lemma sectionUnionCard {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (typ : α → β) (T : Finset β) (d : ℕ)
    (h : ∀ t, (S.filter (fun x => typ x = t)).card = d) :
    (T.biUnion (fun t => S.filter (fun x => typ x = t))).card = T.card * d := by
  rw [Finset.card_biUnion]
  · simp [h]
  · intro u _ v _ huv
    exact Finset.disjoint_left.mpr fun x hu hv =>
      huv ((Finset.mem_filter.mp hu).2.symm.trans (Finset.mem_filter.mp hv).2)

private lemma sectionDrop {m N d : ℕ} (S : Finset (Fin N)) (typ : Fin N → Fin m)
    (f : Fin m → Fin N) (hf : ∀ t, f t ∈ S)
    (hb : Function.Bijective (fun t => typ (f t)))
    (h : ∀ t, (S.filter (fun x => typ x = t)).card = d + 1) (t : Fin m) :
    (((S \ Finset.univ.image f).filter (fun x => typ x = t)).card = d) := by
  classical
  obtain ⟨u, hu⟩ := hb.2 t
  have hem : f u ∈ S.filter (fun x => typ x = t) := Finset.mem_filter.mpr ⟨hf u, hu⟩
  have heq : (S \ Finset.univ.image f).filter (fun x => typ x = t) =
      (S.filter (fun x => typ x = t)).erase (f u) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hx, hn⟩, ht⟩
      exact ⟨fun hxu => hn ⟨u, hxu.symm⟩, hx, ht⟩
    · rintro ⟨hne, hx, ht⟩
      refine ⟨⟨hx, ?_⟩, ht⟩
      rintro ⟨v, rfl⟩
      exact hne (congrArg f (hb.1 (ht.trans hu.symm)))
  rw [heq, Finset.card_erase_of_mem hem, h, Nat.add_sub_cancel]

private lemma pairedSectionsOn {m N : ℕ} (typ₁ typ₂ : Fin N → Fin m) (b : ℕ)
    (S : Finset (Fin N))
    (h₁ : ∀ t, (S.filter (fun x => typ₁ x = t)).card = b)
    (h₂ : ∀ t, (S.filter (fun x => typ₂ x = t)).card = b) :
    ∃ e : Fin b → Fin m → Fin N,
      Function.Injective (fun z : Fin b × Fin m => e z.1 z.2) ∧
      (∀ i t, e i t ∈ S) ∧ (∀ i t, typ₁ (e i t) = t) ∧
      (∀ i, Function.Bijective (fun t => typ₂ (e i t))) := by
  classical
  induction b generalizing S with
  | zero =>
    exact ⟨Fin.elim0, fun x => x.1.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0⟩
  | succ d ih =>
    let adj (t : Fin m) := (S.filter (fun x => typ₁ x = t)).image typ₂
    have hall : ∀ T : Finset (Fin m), T.card ≤ (T.biUnion adj).card := by
      intro T
      have sub : T.biUnion (fun t => S.filter (fun x => typ₁ x = t)) ⊆
          (T.biUnion adj).biUnion (fun t => S.filter (fun x => typ₂ x = t)) := by
        intro x hx
        obtain ⟨t, ht, hx⟩ := Finset.mem_biUnion.mp hx
        exact Finset.mem_biUnion.mpr ⟨typ₂ x,
          Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩,
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, rfl⟩⟩
      have h := Finset.card_le_card sub
      rw [sectionUnionCard S typ₁ T (d + 1) h₁,
        sectionUnionCard S typ₂ (T.biUnion adj) (d + 1) h₂] at h
      exact Nat.le_of_mul_le_mul_right h (Nat.succ_pos d)
    obtain ⟨g, hg, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' adj).mp hall
    have hw (t : Fin m) : ∃ x, x ∈ S.filter (fun x => typ₁ x = t) ∧ typ₂ x = g t :=
      Finset.mem_image.mp (hmem t)
    choose f hf ht₂ using hw
    have hS (t : Fin m) : f t ∈ S := (Finset.mem_filter.mp (hf t)).1
    have ht₁ (t : Fin m) : typ₁ (f t) = t := (Finset.mem_filter.mp (hf t)).2
    have hb₁ : Function.Bijective (fun t => typ₁ (f t)) := by
      simp only [ht₁]
      exact Function.bijective_id
    have hb₂ : Function.Bijective (fun t => typ₂ (f t)) := by
      simp only [ht₂]
      exact ⟨hg, Finite.injective_iff_surjective.mp hg⟩
    obtain ⟨e, he, heS, he₁, he₂⟩ := ih (S \ Finset.univ.image f)
      (sectionDrop S typ₁ f hS hb₁ h₁) (sectionDrop S typ₂ f hS hb₂ h₂)
    refine ⟨Fin.cons f e, ?_, ?_, ?_, ?_⟩
    · have sep (i : Fin d) (s t : Fin m) : e i s ≠ f t := by
        intro eq
        exact (Finset.mem_sdiff.mp (heS i s)).2
          (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, eq.symm⟩)
      rintro ⟨i, s⟩ ⟨j, t⟩
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        exact congrArg (fun u => ((0 : Fin (d + 1)), u)) (hb₁.1 (congrArg typ₁ h))
      · intro h
        exact (sep j t s h.symm).elim
      · intro h
        exact (sep i s t h).elim
      · intro h
        exact congrArg (fun z : Fin d × Fin m => (z.1.succ, z.2))
          (he (a₁ := (i, s)) (a₂ := (j, t)) h)
    · intro i
      exact Fin.cases hS (fun j t => (Finset.mem_sdiff.mp (heS j t)).1) i
    · intro i
      exact Fin.cases ht₁ he₁ i
    · intro i
      exact Fin.cases hb₂ he₂ i

private lemma pairedSections {m b N : ℕ} (typ₁ typ₂ : Fin N → Fin m)
    (h₁ : ∀ t, (Finset.univ.filter (fun x => typ₁ x = t)).card = b)
    (h₂ : ∀ t, (Finset.univ.filter (fun x => typ₂ x = t)).card = b) :
    ∃ e : Fin b → Fin m → Fin N,
      Function.Injective (fun z : Fin b × Fin m => e z.1 z.2) ∧
      (∀ i t, typ₁ (e i t) = t) ∧ (∀ i, Function.Bijective (fun t => typ₂ (e i t))) := by
  obtain ⟨e, hi, _, hleft, hright⟩ := pairedSectionsOn typ₁ typ₂ b Finset.univ h₁ h₂
  exact ⟨e, hi, hleft, hright⟩

private def poolColor (r c : Bool) : Fin 3 :=
  if r then (if c then 0 else 1) else (if c then 2 else 0)

private theorem poolCollision (r₁ c₁ r₂ c₂ : Bool)
    (h : poolColor r₁ c₁ = poolColor r₂ c₂) : (r₁ || c₂) = (r₂ || c₁) := by
  cases r₁ <;> cases c₁ <;> cases r₂ <;> cases c₂ <;> simp [poolColor] at h ⊢

private theorem parityOfSwap (u v r₁ r₂ c₁ c₂ : Bool)
    (h : Bool.xor u (Bool.xor r₁ c₂) = Bool.xor v (Bool.xor r₂ c₁)) :
    Bool.xor u v = Bool.xor (Bool.xor r₁ c₁) (Bool.xor r₂ c₂) := by
  cases u <;> cases v <;> cases r₁ <;> cases r₂ <;> cases c₁ <;> cases c₂ <;> simp at h ⊢

private theorem lossOfSections {a m b N q : ℕ} (hb : 0 < b)
    (typ : Fin N → Fin m) (g : Fin m → Fin m → Bool)
    (hard : ∀ (p : Equiv.Perm (Fin m)) (s : Fin m → Bool) (c : Fin m → Fin (3^q)),
      a*m < 4 * ((Finset.univ : Finset (Fin m × Fin m)).filter (fun z =>
        z.1 < z.2 ∧ c z.1 = c z.2 ∧ Bool.xor (g z.1 (p z.2)) (g z.2 (p z.1)) ≠
          Bool.xor (s z.1) (s z.2))).card)
    (π : Equiv.Perm (Fin N)) (rf cf : Fin N → Bool)
    (R C : Fin q → Finset (Fin N)) (out : Finset (Fin N) → (Fin q → Bool) → Bool)
    (e : Fin b → Fin m → Fin N) (hinj : Function.Injective (fun z : Fin b × Fin m => e z.1 z.2))
    (hrow : ∀ i t, typ (e i t) = t)
    (hcol : ∀ i, Function.Bijective (fun t => typ (π (e i t)))) :
    a*(b*m) < 4 * ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
      out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (g (typ z.1) (typ (π z.2))) (Bool.xor (rf z.1) (cf (π z.2))))).card := by
  classical
  let score (x y : Fin N) : Bool :=
    out {x,y} (fun j => decide (x ∈ R j ∨ π y ∈ C j))
  let truth (x y : Fin N) : Bool :=
    Bool.xor (g (typ x) (typ (π y))) (Bool.xor (rf x) (cf (π y)))
  let err : Finset (Fin N × Fin N) := Finset.univ.filter fun z => score z.1 z.2 ≠ truth z.1 z.2
  let p (i : Fin b) : Equiv.Perm (Fin m) := Equiv.ofBijective _ (hcol i)
  let s (i : Fin b) (t : Fin m) : Bool := Bool.xor (rf (e i t)) (cf (π (e i t)))
  let digit (i : Fin b) (t : Fin m) (j : Fin q) : Fin 3 :=
    poolColor (decide (e i t ∈ R j)) (decide (π (e i t) ∈ C j))
  let code : (Fin q → Fin 3) ≃ Fin (3^q) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin])
  let Bad (i : Fin b) : Finset (Fin m × Fin m) := Finset.univ.filter fun z =>
    z.1 < z.2 ∧ code (digit i z.1) = code (digit i z.2) ∧
      Bool.xor (g z.1 (p i z.2)) (g z.2 (p i z.1)) ≠ Bool.xor (s i z.1) (s i z.2)
  let selected : (Fin b × (Fin m × Fin m)) → Fin N × Fin N := fun w =>
    let x := e w.1 w.2.1
    let y := e w.1 w.2.2
    if score x y ≠ truth x y then (x,y) else (y,x)
  let Total : Finset (Fin b × (Fin m × Fin m)) :=
    Finset.univ.filter (fun w => w.2 ∈ Bad w.1)
  have hmem : ∀ w ∈ Total, selected w ∈ err := by
    rintro ⟨i,x,y⟩ hw
    have hbad : (x,y) ∈ Bad i := (Finset.mem_filter.mp hw).2
    obtain ⟨_, hcolor, hconf⟩ := (Finset.mem_filter.mp hbad).2
    have hdig := code.injective hcolor
    have hpools : (fun j => decide (e i x ∈ R j ∨ π (e i y) ∈ C j)) =
        (fun j => decide (e i y ∈ R j ∨ π (e i x) ∈ C j)) := by
      funext j
      have decOr (P Q : Prop) [Decidable P] [Decidable Q] :
          decide (P ∨ Q) = (decide P || decide Q) := by
        by_cases hp : P <;> by_cases hq : Q <;> simp [hp,hq]
      simpa only [decOr] using poolCollision (decide (e i x ∈ R j))
        (decide (π (e i x) ∈ C j)) (decide (e i y ∈ R j))
        (decide (π (e i y) ∈ C j)) (congrFun hdig j)
    have hscore : score (e i x) (e i y) = score (e i y) (e i x) := by
      dsimp [score]
      rw [hpools, Finset.pair_comm]
    have htruth : truth (e i x) (e i y) ≠ truth (e i y) (e i x) := by
      intro ht
      apply hconf
      have hpi (z : Fin m) : p i z = typ (π (e i z)) := rfl
      dsimp [truth] at ht
      rw [hrow, hrow] at ht
      simpa only [hpi, s] using parityOfSwap _ _ _ _ _ _ ht
    change (if score (e i x) (e i y) ≠ truth (e i x) (e i y) then (e i x, e i y)
      else (e i y, e i x)) ∈ err
    split_ifs with h
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [← hscore, not_ne_iff.mp h]; exact htruth⟩
  have hselect : Set.InjOn selected (Total : Set (Fin b × (Fin m × Fin m))) := by
    rintro ⟨i,x,y⟩ h₁ ⟨j,u,v⟩ h₂ heq
    have hx : x < y := (Finset.mem_filter.mp (Finset.mem_filter.mp h₁).2).2.1
    have hu : u < v := (Finset.mem_filter.mp (Finset.mem_filter.mp h₂).2).2.1
    have hpair {i j : Fin b} {x y : Fin m} (h : e i x = e j y) : i = j ∧ x = y := by
      have h' : (i,x) = (j,y) := hinj h
      exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
    dsimp [selected] at heq
    split_ifs at heq <;>
      have hfst := hpair (congrArg Prod.fst heq) <;>
      have hsnd := hpair (congrArg Prod.snd heq) <;>
      rcases hfst with ⟨rfl, hfst⟩ <;> rcases hsnd with ⟨_, hsnd⟩ <;>
      subst_vars <;> first | rfl | exact (lt_asymm hx hu).elim
  have hle : Total.card ≤ err.card := Finset.card_le_card_of_injOn selected hmem hselect
  have hcard : Total.card = ∑ i, (Bad i).card := by
    dsimp only [Total]
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.card_filter]
    congr 1
    ext z
    simp
  have hnonempty : (Finset.univ : Finset (Fin b)).Nonempty := ⟨⟨0, hb⟩, Finset.mem_univ _⟩
  have hsum : (∑ _i : Fin b, a*m) < ∑ i : Fin b, 4 * (Bad i).card :=
    Finset.sum_lt_sum_of_nonempty hnonempty
      (fun i _ => hard (p i) (s i) (fun t => code (digit i t)))
  have hright : 4 * Total.card = ∑ i : Fin b, 4 * (Bad i).card := by
    rw [hcard, Finset.mul_sum]
  rw [← hright, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  calc
    a * (b*m) = b * (a*m) := by ring
    _ < 4 * Total.card := hsum
    _ ≤ 4 * err.card := Nat.mul_le_mul_left _ hle

end PEqualNP.Outside.L_meta_25715_aux

open PEqualNP.Outside.L_meta_25715_aux in
open PEqualNP.MetaComplexity PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25715 :
∀ (a k : ℕ), 16 ≤ a → 2^(2*a) ≤ k →
  let n := 2^k
  let I := Fin n
  let Table := I → I → Bool
  let loss := fun (G : Table) (q : ℕ) (π : Equiv.Perm I) (rowFlip colFlip : I → Bool)
      (R C : Fin q → Finset I) (out : Finset I → (Fin q → Bool) → Bool) =>
    ((Finset.univ : Finset (I × I)).filter (fun z =>
      out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G z.1 (π z.2)) (Bool.xor (rowFlip z.1) (colFlip (π z.2))))).card
  ∃ G : Table,
    PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k := k) (l := k) G)
      (3*k) ∧
    ∀ q : ℕ, 8*a*3^q ≤ 2^a →
      ∀ (π : Equiv.Perm I) (rowFlip colFlip : I → Bool)
        (R C : Fin q → Finset I) (out : Finset I → (Fin q → Bool) → Bool),
        a*n < 4*loss G q π rowFlip colFlip R C out := by
  intro a k ha hk n I Table loss
  have hak : a ≤ k := by
    calc
      a ≤ 2^a := Nat.lt_two_pow_self.le
      _ ≤ 2^(2*a) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ k := hk
  obtain ⟨g, hg⟩ := existsBase a ha
  let G : Table := fun x y => g (lowType a k x) (lowType a k y)
  refine ⟨G, ?_, ?_⟩
  · let select : Fin (a+a) → Fin (k+k) := Fin.append
      (fun i => Fin.castAdd k (Fin.castLE hak i)) (fun i => Fin.natAdd k (Fin.castLE hak i))
    let f (bits : Fin (a+a) → Bool) : Bool :=
      g (Fin.ofNat (2^a) (tableIndex (fun i : Fin a => bits (Fin.castAdd a i))))
        (Fin.ofNat (2^a) (tableIndex (fun i : Fin a => bits (Fin.natAdd a i))))
    have heval : (fun (x : Fin (k+k) → Bool) => f (fun j => x (select j))) = adjFun G := by
      funext x
      simp only [adjFun, G, lowIndex hak, f, select, Fin.append_left, Fin.append_right]
    obtain ⟨c, hc, hsize, hfun⟩ := heval ▸ lookupSize select f
    refine ⟨c, hc, hsize.trans ?_, hfun⟩
    exact Nat.mul_le_mul_left 3 (by simpa only [two_mul] using hk)
  · intro q hq π rf cf R C out
    have hl (t : Fin (2^a)) : (Finset.univ.filter (fun x => lowType a k x = t)).card = 2^(k-a) :=
      fibersLow hak (Equiv.refl _) t
    obtain ⟨e, he, hr, hc⟩ := pairedSections (lowType a k) (fun x => lowType a k (π x)) hl
      (fibersLow hak π)
    have hbm : 2^(k-a) * 2^a = n := by dsimp [n]; rw [← pow_add, Nat.sub_add_cancel hak]
    simpa only [hbm] using lossOfSections (Nat.two_pow_pos (k-a)) (lowType a k) g
      (hg (3^q) hq) π rf cf R C out e he hr hc
