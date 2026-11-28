import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_1006_aux

variable {t : ℕ}

abbrev LF (t : ℕ) := Fin (3*t) → ZMod 2

private def lNext (i : Fin (3*t)) : Fin (3*t) :=
  ⟨(i.val+1) % (3*t), Nat.mod_lt _ (by have := i.isLt; omega)⟩

private def lPrev (i : Fin (3*t)) : Fin (3*t) :=
  ⟨if i.val = 0 then 3*t-1 else i.val-1, by have := i.isLt; split <;> omega⟩

private lemma lfNext_val (i : Fin (3*t)) :
    (lNext i).val = if i.val + 1 = 3*t then 0 else i.val + 1 := by
  change (i.val+1) % (3*t) = _
  have h := i.isLt
  split_ifs with h'
  · rw [h', Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma lfNext_prev (i : Fin (3*t)) : lNext (lPrev i) = i := by
  apply Fin.ext
  rw [lfNext_val]
  change (if (if i.val = 0 then 3*t-1 else i.val-1) + 1 = 3*t then 0 else
    (if i.val = 0 then 3*t-1 else i.val-1) + 1) = _
  have hi := i.isLt
  split_ifs <;> omega

private lemma lfPrev_next (i : Fin (3*t)) : lPrev (lNext i) = i := by
  apply Fin.ext
  change (if (lNext i).val = 0 then 3*t-1 else (lNext i).val-1) = _
  rw [lfNext_val]
  have hi := i.isLt
  by_cases h : i.val + 1 = 3*t
  · simp [h]; omega
  · simp [h]

private lemma lfPrev_inj : Function.Injective (@lPrev t) :=
  fun a b h => by simpa only [lfNext_prev] using congrArg lNext h

private lemma lfPrev_twice_ne (i : Fin (3*t)) : lPrev (lPrev i) ≠ i := by
  intro h
  have h' := congrArg Fin.val h
  change (if (if i.val = 0 then 3*t-1 else i.val-1) = 0 then 3*t-1 else
    (if i.val = 0 then 3*t-1 else i.val-1)-1) = i.val at h'
  have hi := i.isLt
  split_ifs at h' <;> omega

private def lDual (v : Fin 2 → ZMod 2) : LF t := fun i =>
  if i.val % 3 = 0 then v 0 else if i.val % 3 = 1 then v 1 else v 0 + v 1

private def lDot (x y : LF t) : ZMod 2 := ∑ i, x i*y i

private def lLane (x : LF t) : Prop := ∀ v, lDot (lDual v) x = 0

private def lHard (x y : LF t) : Prop := ∀ i, x i ≠ 0 → y i = 0 ∧ y (lPrev i) = 0

private def lCover (z y : LF t) : Prop := ∀ i, z i ≠ 0 → y i ≠ 0 ∨ y (lPrev i) ≠ 0

private def lUnit (j : Fin (3*t)) : LF t := fun i => if i = j then 1 else 0

private lemma lfAdd_self (a : ZMod 2) : a + a = 0 := by fin_cases a <;> rfl

private lemma lfDual_add (v w : Fin 2 → ZMod 2) :
    (lDual (v + w) : LF t) = lDual v + lDual w := by
  ext i
  simp only [lDual, Pi.add_apply]
  split_ifs <;> ring

private lemma lfDot_add_right (x y z : LF t) : lDot x (y+z) = lDot x y + lDot x z := by
  simp [lDot, mul_add, Finset.sum_add_distrib]

private lemma lfDot_unit (x : LF t) (j : Fin (3*t)) : lDot x (lUnit j) = x j := by
  simp [lDot, lUnit, mul_ite]

private noncomputable def lSet (P : LF t × LF t → Prop) : Finset (LF t × LF t) := by
  classical
  exact Finset.univ.filter P

private lemma lfMem_set (P : LF t × LF t → Prop) (p) : p ∈ lSet P ↔ P p := by
  classical
  simp [lSet]

private def lGood (p : LF t × LF t) : Prop := lLane p.1 ∧ lLane p.2 ∧ lHard p.1 p.2

private noncomputable def lWords : Finset (LF t × LF t) := lSet lGood

private noncomputable def lCount (P : LF t × LF t → Prop) : ℚ := ((lSet P).card : ℚ)

private lemma lfCount_mono {P Q : LF t × LF t → Prop} (h : ∀ p, P p → Q p) :
    lCount P ≤ lCount Q := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  exact (lfMem_set _ _).2 (h p ((lfMem_set _ _).1 hp))

private lemma lfCount_nonneg (P : LF t × LF t → Prop) : 0 ≤ lCount P := by
  unfold lCount
  positivity

private lemma lfPick (P : Finset ℕ) (hP : P.card < 9) : ∃ n < 9, n ∉ P := by
  obtain ⟨n, hn, hn'⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (t := Finset.range 9) (by simpa using hP)
  exact ⟨n, Finset.mem_range.mp hn, hn'⟩

private lemma lfFourBlocks (P : Finset ℕ) (hP : P.card ≤ 5) :
    ∃ a b c d : ℕ, a < 9 ∧ b < 9 ∧ c < 9 ∧ d < 9 ∧
      a ∉ P ∧ b ∉ P ∧ c ∉ P ∧ d ∉ P ∧
      b ≠ a ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  obtain ⟨a, ha, haP⟩ := lfPick P (by omega)
  have h₁ := Finset.card_insert_le a P
  obtain ⟨b, hb, hbP⟩ := lfPick (insert a P) (by omega)
  have h₂ := Finset.card_insert_le b (insert a P)
  obtain ⟨c, hc, hcP⟩ := lfPick (insert b (insert a P)) (by omega)
  have h₃ := Finset.card_insert_le c (insert b (insert a P))
  obtain ⟨d, hd, hdP⟩ := lfPick (insert c (insert b (insert a P))) (by omega)
  simp only [Finset.mem_insert, not_or] at hbP hcP hdP
  exact ⟨a,b,c,d,ha,hb,hc,hd,haP,hbP.2,hcP.2.2,hdP.2.2.2,
    hbP.1,hcP.2.1,hcP.1,hdP.2.2.1,hdP.2.1,hdP.1⟩

private def lfBlock (i : Fin (3*t)) : ℕ := i.val / 6

private def lfCenter (ht : 32 ≤ t) (r : ℕ) (hr : r < 9) (s : ℕ) (hs : s < 2) :
    Fin (3*t) := ⟨6*r+3+s, by omega⟩

private lemma lfCenter_spec (ht : 32 ≤ t) {r s : ℕ} (hr : r < 9) (hs : s < 2) :
    let i := lfCenter ht r hr s hs
    i.val % 3 = s ∧ lfBlock i = r ∧ lfBlock (lPrev i) = r ∧ lfBlock (lNext i) = r := by
  dsimp [lfCenter, lfBlock]
  rw [lfNext_val]
  let n := 6*r+3+s
  change n%3 = s ∧ n/6 = r ∧
    (if n=0 then 3*t-1 else n-1)/6 = r ∧
    (if n+1=3*t then 0 else n+1)/6 = r
  have h0 : n ≠ 0 := by dsimp [n]; omega
  have h1 : n+1 ≠ 3*t := by dsimp [n]; omega
  simp only [ite_eq_right h0, ite_eq_right h1]
  dsimp [n]
  omega

private def lfClear (S : Finset (Fin (3*t))) (x : LF t) : LF t := fun i =>
  if i ∈ S then 0 else x i

private def lfAxis (s : Fin 2) (k : Fin 2) : ZMod 2 := if k = s then 1 else 0

private lemma lfLaneAxes {x : LF t}
    (h0 : lDot (lDual (lfAxis 0)) x = 0) (h1 : lDot (lDual (lfAxis 1)) x = 0) : lLane x := by
  intro v
  have aux (i : Fin (3*t)) : lDual v i = v 0 * lDual (lfAxis 0) i + v 1 * lDual (lfAxis 1) i := by
    unfold lDual
    split_ifs <;> simp [lfAxis]
  unfold lDot at *
  simp_rw [aux, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, h0, h1,
    mul_zero, add_zero]

private def lfFill (S : Finset (Fin (3*t))) (a b : Fin (3*t)) (x : LF t) : LF t :=
  let u := lfClear S x
  u + (fun i => lDot (lDual (lfAxis 0)) u * lUnit a i) +
      (fun i => lDot (lDual (lfAxis 1)) u * lUnit b i)

private lemma lfFill_eval (S : Finset (Fin (3*t))) (a b : Fin (3*t)) (x : LF t)
    (i : Fin (3*t)) (ha : i ≠ a) (hb : i ≠ b) :
    lfFill S a b x i = lfClear S x i := by
  simp [lfFill, lUnit, ha, hb]

private lemma lfDot_scale_unit (x : LF t) (c : ZMod 2) (j : Fin (3*t)) :
    lDot x (fun i => c * lUnit j i) = c * x j := by
  simp [lDot, lUnit, mul_ite, mul_comm]

private lemma lfFill_lane (S : Finset (Fin (3*t))) (a b : Fin (3*t)) (x : LF t)
    (ha : a.val % 3 = 0) (hb : b.val % 3 = 1) : lLane (lfFill S a b x) := by
  apply lfLaneAxes
  · simp [lfFill, lfDot_add_right, lfDot_scale_unit, lDual, ha, hb, lfAxis, lfAdd_self]
  · simp [lfFill, lfDot_add_right, lfDot_scale_unit, lDual, ha, hb, lfAxis, lfAdd_self]

private def lfRepairMask (a b c d : Fin (3*t)) : Finset (Fin (3*t)) :=
  {a,b,c,d,lNext c,lNext d}

private def lfRepairMaskY (a b c d : Fin (3*t)) : Finset (Fin (3*t)) :=
  {c,d,a,b,lPrev a,lPrev b}

private lemma lfRepairHard (a b c d : Fin (3*t)) (x y : LF t) (h : lHard x y)
    (sep : ∀ i ∈ lfRepairMask a b c d, ∀ j ∈ lfRepairMaskY a b c d,
      (i = a ∨ i = b) → (j = c ∨ j = d) → i ≠ j ∧ lPrev i ≠ j) :
    lHard (lfFill (lfRepairMask a b c d) a b x) (lfFill (lfRepairMaskY a b c d) c d y) := by
  let S := lfRepairMask a b c d
  let T := lfRepairMaskY a b c d
  have main (i j : Fin (3*t)) (hij : j = i ∨ j = lPrev i)
      (hx : lfFill S a b x i ≠ 0) : lfFill T c d y j = 0 := by
    by_cases hi : i = a ∨ i = b
    · have hiS : i ∈ S := by rcases hi with rfl | rfl <;> simp [S, lfRepairMask]
      have hjT : j ∈ T := by
        rcases hi with rfl | rfl <;> rcases hij with rfl | rfl <;> simp [T, lfRepairMaskY]
      have hj : j ≠ c ∧ j ≠ d := by
        constructor <;> intro hh <;>
          have hh' := sep i hiS j hjT hi (by simp [hh]) <;>
          rcases hij with rfl | rfl <;> simp at hh'
      simp [lfFill_eval T c d y j hj.1 hj.2, lfClear, hjT]
    · push Not at hi
      rw [lfFill_eval S a b x i hi.1 hi.2] at hx
      have hiS : i ∉ S := by intro hm; exact hx (by simp [lfClear, hm])
      have hx' : x i ≠ 0 := by simpa [lfClear, hiS] using hx
      have hj : j ≠ c ∧ j ≠ d := by
        constructor <;> intro hh <;> apply hiS
        · rcases hij with h' | h'
          · have : i = c := h'.symm.trans hh
            simp [S, lfRepairMask, this]
          · have : i = lNext c := by rw [← hh, h', lfNext_prev]
            simp [S, lfRepairMask, this]
        · rcases hij with h' | h'
          · have : i = d := h'.symm.trans hh
            simp [S, lfRepairMask, this]
          · have : i = lNext d := by rw [← hh, h', lfNext_prev]
            simp [S, lfRepairMask, this]
      have hy : y j = 0 := by
        rcases hij with he | he
        · rw [he]; exact (h i hx').1
        · rw [he]; exact (h i hx').2
      simp [lfFill_eval T c d y j hj.1 hj.2, lfClear, hy]
  intro i hi
  exact ⟨main i i (Or.inl rfl) hi, main i (lPrev i) (Or.inr rfl) hi⟩

-- Each chosen block holds a repair center and its two possible neighbor indices.
-- Two centers of residues zero and one repair the two independent checks of a word.
private lemma lfRepair {t : ℕ} (ht : 32 ≤ t) (E : Finset (Fin (3*t))) (hE : E.card ≤ 5) :
    ∃ S T : Finset (Fin (3*t)), S.card + T.card ≤ 12 ∧ Disjoint E S ∧ Disjoint E T ∧
      ∃ ρ : LF t × LF t → LF t × LF t,
        (∀ p, lHard p.1 p.2 → lGood (ρ p)) ∧
        (∀ p i, i ∉ S → (ρ p).1 i = p.1 i) ∧
        (∀ p i, i ∉ T → (ρ p).2 i = p.2 i) := by
  classical
  let P := E.image lfBlock
  have hP : P.card ≤ 5 := Finset.card_image_le.trans hE
  obtain ⟨a,b,c,d,ha,hb,hc,hd,haP,hbP,hcP,hdP,hba,hca,hcb,hda,hdb,hdc⟩ := lfFourBlocks P hP
  let a' := lfCenter ht a ha 0 (by decide)
  let b' := lfCenter ht b hb 1 (by decide)
  let c' := lfCenter ht c hc 0 (by decide)
  let d' := lfCenter ht d hd 1 (by decide)
  have A : a'.val % 3 = 0 ∧ lfBlock a' = a ∧ lfBlock (lPrev a') = a ∧ lfBlock (lNext a') = a :=
    lfCenter_spec ht ha (by decide)
  have B : b'.val % 3 = 1 ∧ lfBlock b' = b ∧ lfBlock (lPrev b') = b ∧ lfBlock (lNext b') = b :=
    lfCenter_spec ht hb (by decide)
  have C : c'.val % 3 = 0 ∧ lfBlock c' = c ∧ lfBlock (lPrev c') = c ∧ lfBlock (lNext c') = c :=
    lfCenter_spec ht hc (by decide)
  have D : d'.val % 3 = 1 ∧ lfBlock d' = d ∧ lfBlock (lPrev d') = d ∧ lfBlock (lNext d') = d :=
    lfCenter_spec ht hd (by decide)
  let S := lfRepairMask a' b' c' d'
  let T := lfRepairMaskY a' b' c' d'
  have hcard (e f g h i j : Fin (3*t)) : ({e,f,g,h,i,j} : Finset _).card ≤ 6 := by
    have h₁ := Finset.card_insert_le e ({f,g,h,i,j} : Finset _)
    have h₂ := Finset.card_insert_le f ({g,h,i,j} : Finset _)
    have h₃ := Finset.card_insert_le g ({h,i,j} : Finset _)
    have h₄ := Finset.card_insert_le h ({i,j} : Finset _)
    have h₅ := Finset.card_insert_le i ({j} : Finset _)
    simp only [Finset.card_singleton] at h₅
    omega
  have hS : S.card ≤ 6 := hcard ..
  have hT : T.card ≤ 6 := hcard ..
  have hs : Disjoint E S := by
    apply Finset.disjoint_left.mpr
    intro i hi hS
    have hiP : lfBlock i ∈ P := Finset.mem_image_of_mem lfBlock hi
    simp only [S, lfRepairMask, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [A.2.1,B.2.1,C.2.1,C.2.2.2,D.2.1,D.2.2.2] at hiP <;> contradiction
  have hτ : Disjoint E T := by
    apply Finset.disjoint_left.mpr
    intro i hi hT
    have hiP : lfBlock i ∈ P := Finset.mem_image_of_mem lfBlock hi
    simp only [T, lfRepairMaskY, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [A.2.1,A.2.2.1,B.2.1,B.2.2.1,C.2.1,D.2.1] at hiP <;> contradiction
  refine ⟨S,T,by omega,hs,hτ,fun p => (lfFill S a' b' p.1,lfFill T c' d' p.2), ?_, ?_, ?_⟩
  · intro p hp
    refine ⟨lfFill_lane S a' b' p.1 A.1 B.1, lfFill_lane T c' d' p.2 C.1 D.1, ?_⟩
    apply lfRepairHard _ _ _ _ _ _ hp
    intro i _ j _ hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      constructor <;> intro he <;> have h := congrArg lfBlock he <;>
      simp only [A.2.1,A.2.2.1,B.2.1,B.2.2.1,C.2.1,D.2.1] at h <;> omega
  · intro p i hi
    have ha' : i ≠ a' := by intro h; subst i; exact hi (by simp [S, lfRepairMask])
    have hb' : i ≠ b' := by intro h; subst i; exact hi (by simp [S, lfRepairMask])
    simp [lfFill_eval S a' b' p.1 i ha' hb', lfClear, hi]
  · intro p i hi
    have hc' : i ≠ c' := by intro h; subst i; exact hi (by simp [T, lfRepairMaskY])
    have hd' : i ≠ d' := by intro h; subst i; exact hi (by simp [T, lfRepairMaskY])
    simp [lfFill_eval T c' d' p.2 i hc' hd', lfClear, hi]

-- The output and the original bits at overwritten sites determine the input.
private lemma lfOverwriteCount (P Q : LF t × LF t → Prop)
    (S T : Finset (Fin (3*t))) (f : LF t × LF t → LF t × LF t)
    (hm : ∀ p, P p → Q (f p))
    (hx : ∀ p i, i ∉ S → (f p).1 i = p.1 i)
    (hy : ∀ p i, i ∉ T → (f p).2 i = p.2 i) :
    lCount P ≤ lCount Q * 2^(S.card+T.card) := by
  classical
  let k (p : LF t × LF t) : (LF t × LF t) × ((S → ZMod 2) × (T → ZMod 2)) :=
    (f p, (fun i => p.1 i, fun i => p.2 i))
  have hc := Finset.card_le_card_of_injOn k (s := lSet P)
    (t := (lSet Q).product Finset.univ) ?_ ?_
  · simp [Finset.card_product, Fintype.card_prod, ZMod.card, ← pow_add] at hc
    unfold lCount
    exact_mod_cast hc
  · intro p hp
    exact Finset.mem_product.mpr ⟨(lfMem_set _ _).mpr (hm p ((lfMem_set _ _).mp hp)),
      Finset.mem_univ _⟩
  · intro p _ q _ he
    have hf : f p = f q := congrArg Prod.fst he
    have hS := congrArg (fun k => k.2.1) he
    have hT := congrArg (fun k => k.2.2) he
    apply Prod.ext
    · funext i
      by_cases h : i ∈ S
      · exact congrFun hS ⟨i,h⟩
      · rw [← hx p i h, ← hx q i h, hf]
    · funext i
      by_cases h : i ∈ T
      · exact congrFun hT ⟨i,h⟩
      · rw [← hy p i h, ← hy q i h, hf]

private lemma lfNorm (ht : 32 ≤ t) :
    lCount (fun p : LF t × LF t => lHard p.1 p.2) ≤ lCount (lGood (t := t)) * 2^12 := by
  obtain ⟨S,T,hST,_,_,f,hf,hx,hy⟩ := lfRepair ht (∅ : Finset (Fin (3*t))) (by simp)
  refine (lfOverwriteCount _ _ S T f hf hx hy).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hST)
    (lfCount_nonneg _)

private def lfForceY (k j : Fin (3*t)) (y : LF t) : LF t := fun r =>
  if r = k then 1 else lfClear {j,lPrev j} y r

private lemma lfForceHard (k j : Fin (3*t)) (x y : LF t) (h : lHard x y) :
    lHard (lfClear {k,lNext k} x) (lfForceY k j y) := by
  intro r hr
  have hnot : r ∉ ({k,lNext k} : Finset _) := by
    intro hm
    exact hr (ite_eq_left hm)
  have hn : r ≠ k ∧ r ≠ lNext k := by simpa using hnot
  have hprev : lPrev r ≠ k := by
    intro he
    exact hn.2 (by rw [← he, lfNext_prev])
  have hxy := h r (by simpa [lfClear, hnot] using hr)
  exact ⟨by simp [lfForceY, lfClear, hn.1, hxy.1],
    by simp [lfForceY, lfClear, hprev, hxy.2]⟩

private lemma lfForceChoose {i j : Fin (3*t)} (h : i ≠ j) :
    ∃ k, (k = i ∨ k = lPrev i) ∧ k ≠ j ∧ k ≠ lPrev j := by
  by_cases he : i = lPrev j
  · refine ⟨lPrev i, Or.inr rfl, ?_, ?_⟩
    · rw [he]
      exact lfPrev_twice_ne j
    · exact fun hc => h (lfPrev_inj hc)
  · exact ⟨i, Or.inl rfl, h, he⟩

private def lfHit (i : Fin (3*t)) (y : LF t) : Prop := y i ≠ 0 ∨ y (lPrev i) ≠ 0

private lemma lfCover_unit_iff (i : Fin (3*t)) (y : LF t) : lCover (lUnit i) y ↔ lfHit i y := by
  constructor
  · intro h
    exact h i (by simp [lUnit])
  · intro h k hk
    by_cases he : k = i
    · simpa [he, lfHit] using h
    · exact False.elim (hk (by simp [lUnit, he]))

-- Force a hit at i and a miss at j before repairing the two words.
private lemma lfGap (ht : 32 ≤ t) {i j : Fin (3*t)} (hne : i ≠ j) :
    lCount (lGood (t := t)) / 2^17 ≤
      lCount (fun p : LF t × LF t => lGood p ∧ lfHit i p.2 ∧ ¬ lfHit j p.2) := by
  classical
  obtain ⟨k,hki,hkj,hkp⟩ := lfForceChoose hne
  let U : Finset (Fin (3*t)) := {k,lNext k}
  let V : Finset (Fin (3*t)) := {k,j,lPrev j}
  have hU : U.card ≤ 2 := by
    have h := Finset.card_insert_le k ({lNext k} : Finset _)
    simpa [U] using h
  have hV : V.card ≤ 3 := by
    have h₁ := Finset.card_insert_le k ({j,lPrev j} : Finset _)
    have h₂ := Finset.card_insert_le j ({lPrev j} : Finset _)
    simp only [Finset.card_singleton] at h₂
    change ({k,j,lPrev j} : Finset _).card ≤ 3
    omega
  have hE : (U ∪ V).card ≤ 5 := (Finset.card_union_le U V).trans (by omega)
  obtain ⟨S,T,hST,_,hdis,ρ,hρ,hx,hy⟩ := lfRepair ht (U ∪ V) hE
  let g (p : LF t × LF t) : LF t × LF t := (lfClear U p.1, lfForceY k j p.2)
  have hY (r : Fin (3*t)) (hr : r ∈ V) (p : LF t × LF t) :
      (ρ (g p)).2 r = (g p).2 r := by
    apply hy
    exact fun hm => (Finset.disjoint_left.mp hdis) (Finset.mem_union_right U hr) hm
  have htgt (p : LF t × LF t) (hp : lGood p) :
      lGood (ρ (g p)) ∧ lfHit i (ρ (g p)).2 ∧ ¬ lfHit j (ρ (g p)).2 := by
    refine ⟨hρ _ (lfForceHard k j p.1 p.2 hp.2.2), ?_, ?_⟩
    · have hk : (ρ (g p)).2 k = 1 := by
        rw [hY k (by simp [V])]
        simp [g, lfForceY]
      rcases hki with he | he
      · exact Or.inl (by rw [← he, hk]; decide)
      · exact Or.inr (by rw [← he, hk]; decide)
    · unfold lfHit
      rw [hY j (by simp [V]), hY (lPrev j) (by simp [V])]
      simp [g, lfForceY, lfClear, hkj.symm, hkp.symm]
  have hx' (p : LF t × LF t) (r : Fin (3*t)) (hr : r ∉ U ∪ S) :
      (ρ (g p)).1 r = p.1 r := by
    have hn : r ∉ U ∧ r ∉ S := by simpa using hr
    rw [hx _ _ hn.2]
    simp [g, lfClear, hn.1]
  have hy' (p : LF t × LF t) (r : Fin (3*t)) (hr : r ∉ V ∪ T) :
      (ρ (g p)).2 r = p.2 r := by
    have hn : r ∉ V ∧ r ∉ T := by simpa using hr
    rw [hy _ _ hn.2]
    have hv : r ≠ k ∧ r ≠ j ∧ r ≠ lPrev j := by simpa [V] using hn.1
    simp [g, lfForceY, lfClear, hv.1, hv.2.1, hv.2.2]
  have hcard : (U ∪ S).card + (V ∪ T).card ≤ 17 := by
    have h₁ := Finset.card_union_le U S
    have h₂ := Finset.card_union_le V T
    omega
  let Q (p : LF t × LF t) := lGood p ∧ lfHit i p.2 ∧ ¬ lfHit j p.2
  have hc := lfOverwriteCount (lGood (t := t)) Q (U ∪ S) (V ∪ T) (fun p => ρ (g p)) htgt hx' hy'
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2^17)).mpr
  refine hc.trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hcard)
    (lfCount_nonneg _)

private def lfSupp (z : LF t) : Finset (Fin (3*t)) := by
  classical
  exact Finset.univ.filter (fun i => z i ≠ 0)

private lemma lfSupp_mem (z : LF t) (i : Fin (3*t)) : i ∈ lfSupp z ↔ z i ≠ 0 := by
  classical
  simp [lfSupp]

private lemma lfGapCard (ht : 32 ≤ t) {u : LF t} {i j : Fin (3*t)}
    (hne : i ≠ j) (hi : u i ≠ 0) (hj : u j ≠ 0) :
    lCount (fun p : LF t × LF t => lGood p ∧ lCover u p.2) + lCount (lGood (t := t)) / 2^17 ≤
      lCount (fun p : LF t × LF t => lGood p ∧ lCover (lUnit i) p.2) := by
  classical
  let P (p : LF t × LF t) := lGood p ∧ lCover u p.2
  let Q (p : LF t × LF t) := lGood p ∧ lfHit i p.2 ∧ ¬ lfHit j p.2
  let R (p : LF t × LF t) := lGood p ∧ lCover (lUnit i) p.2
  have hd : Disjoint (lSet P) (lSet Q) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact ((lfMem_set Q p).mp hq).2.2 (((lfMem_set P p).mp hp).2 j hj)
  have hs : lSet P ∪ lSet Q ⊆ lSet R := by
    intro p hp
    apply (lfMem_set R p).mpr
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨hg,hc⟩ := (lfMem_set P p).mp hp
      exact ⟨hg, (lfCover_unit_iff i _).mpr (hc i hi)⟩
    · obtain ⟨hg,hr,-⟩ := (lfMem_set Q p).mp hp
      exact ⟨hg, (lfCover_unit_iff i _).mpr hr⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd] at hc
  have hcast : lCount P + lCount Q ≤ lCount R := by unfold lCount; exact_mod_cast hc
  have hgap : lCount (lGood (t := t)) / 2^17 ≤ lCount Q := lfGap ht hne
  linarith

section LaneDecay
open scoped Classical

private def lfDecayEvent (i : Fin (3*t)) (p : LF t × LF t) : Prop :=
  p.2 i ≠ 0 ∨ p.2 (lPrev i) ≠ 0

private noncomputable def lfDecayConfigs (S : Finset (Fin (3*t))) : Finset (LF t × LF t) :=
  Finset.univ.filter fun p => lHard p.1 p.2 ∧ ∀ i ∈ S, lfDecayEvent i p

private theorem lfDecayMem {S : Finset (Fin (3*t))} {p : LF t × LF t} :
    p ∈ lfDecayConfigs S ↔ lHard p.1 p.2 ∧ ∀ i ∈ S, lfDecayEvent i p := by
  simp [lfDecayConfigs]

private def lfDecayClear (i : Fin (3*t)) (p : LF t × LF t) : LF t × LF t :=
  (p.1, fun k => if k = i ∨ k = lPrev i then 0 else p.2 k)

private theorem lfDecayStep (i : Fin (3*t)) (S : Finset (Fin (3*t)))
    (hdis : ∀ j ∈ S, Disjoint ({i, lPrev i} : Finset _) {j, lPrev j}) :
    ((lfDecayConfigs (insert i S)).card : ℚ) ≤ (lfDecayConfigs S).card * (3/4 : ℚ) := by
  classical
  let A := lfDecayConfigs S
  let B := A.filter (lfDecayEvent i)
  let C := A.filter fun p => ¬ lfDecayEvent i p
  let D := (Finset.univ : Finset (ZMod 2 × ZMod 2)).erase (0, 0)
  let f : LF t × LF t → (LF t × LF t) × (ZMod 2 × ZMod 2) :=
    fun p => (lfDecayClear i p, (p.2 i, p.2 (lPrev i)))
  have hinj : B.card ≤ (C ×ˢ D).card := by
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      change p ∈ B at hp
      change f p ∈ C ×ˢ D
      obtain ⟨hpA, hpE⟩ := Finset.mem_filter.mp hp
      have hpH := lfDecayMem.mp hpA
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨lfDecayMem.mpr ⟨?_, ?_⟩, ?_⟩
        · have hz (k : Fin (3*t)) (hk : p.2 k = 0) : (lfDecayClear i p).2 k = 0 := by
            simp [lfDecayClear, hk]
          intro k hk
          exact ⟨hz k (hpH.1 k hk).1, hz (lPrev k) (hpH.1 k hk).2⟩
        · intro j hj
          have hout (k : Fin (3*t)) (hk : k ∈ ({j, lPrev j} : Finset _)) :
              ¬ (k = i ∨ k = lPrev i) := by
            intro h
            exact (Finset.disjoint_left.mp (hdis j hj)) (by simpa using h) hk
          have h₁ := hout j (by simp)
          have h₂ := hout (lPrev j) (by simp)
          change lfDecayEvent j (lfDecayClear i p)
          simpa [lfDecayEvent, lfDecayClear, h₁, h₂] using hpH.2 j hj
        · change ¬ lfDecayEvent i (lfDecayClear i p)
          simp [lfDecayEvent, lfDecayClear]
      · apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_univ _⟩
        intro he
        rcases hpE with h | h
        · exact h (congrArg Prod.fst he)
        · exact h (congrArg Prod.snd he)
    · intro p _ q _ he
      have hc : lfDecayClear i p = lfDecayClear i q := congrArg Prod.fst he
      have hb : (p.2 i, p.2 (lPrev i)) = (q.2 i, q.2 (lPrev i)) := congrArg Prod.snd he
      apply Prod.ext
      · change (lfDecayClear i p).1 = (lfDecayClear i q).1
        exact congrArg Prod.fst hc
      · funext k
        by_cases h : k = i ∨ k = lPrev i
        · rcases h with rfl | rfl
          · exact congrArg Prod.fst hb
          · exact congrArg Prod.snd hb
        · have hk := congrFun (congrArg Prod.snd hc) k
          simpa [lfDecayClear, h] using hk
  have hD : D.card = 3 := by
    dsimp only [D]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_prod, ZMod.card]
  have hB : B = lfDecayConfigs (insert i S) := by
    ext p
    simp only [B, A, lfDecayConfigs, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hh, hs⟩, hi⟩
      refine ⟨hh, fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi
      · exact hs j hj
    · rintro ⟨hh, hs⟩
      exact ⟨⟨hh, fun j hj => hs j (Finset.mem_insert_of_mem hj)⟩,
        hs i (Finset.mem_insert_self i S)⟩
  have hparts : B.card + C.card = A.card :=
    Finset.card_filter_add_card_filter_not (s := A) (lfDecayEvent i)
  rw [Finset.card_product, hD] at hinj
  have hqr : (B.card : ℚ) ≤ (C.card : ℚ) * 3 := by exact_mod_cast hinj
  have hpr : (B.card : ℚ) + (C.card : ℚ) = (A.card : ℚ) := by exact_mod_cast hparts
  rw [← hB]
  change (B.card : ℚ) ≤ (A.card : ℚ) * (3/4 : ℚ)
  linarith

private theorem lfDecayAux (S : Finset (Fin (3*t)))
    (hdis : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint ({i, lPrev i} : Finset _) {j, lPrev j}) :
    ((lfDecayConfigs S).card : ℚ) ≤ (lfDecayConfigs (∅ : Finset (Fin (3*t)))).card *
      (3/4 : ℚ)^S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have hrest : ∀ j ∈ S, ∀ k ∈ S, j ≠ k →
          Disjoint ({j, lPrev j} : Finset _) {k, lPrev k} := by
        intro j hj k hk hjk
        exact hdis j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
      have hfirst : ∀ j ∈ S, Disjoint ({i, lPrev i} : Finset _) {j, lPrev j} := by
        intro j hj
        exact hdis i (Finset.mem_insert_self i S) j (Finset.mem_insert_of_mem hj)
          (fun he => hi (he.symm ▸ hj))
      rw [Finset.card_insert_of_notMem hi, pow_succ, ← mul_assoc]
      exact (lfDecayStep i S hfirst).trans
        (mul_le_mul_of_nonneg_right (ih hrest) (by norm_num))

private theorem lfDecay (S : Finset (Fin (3*t)))
    (hdis : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint ({i, lPrev i} : Finset _) {j, lPrev j}) :
    lCount (fun p : LF t × LF t => lHard p.1 p.2 ∧
      ∀ i ∈ S, p.2 i ≠ 0 ∨ p.2 (lPrev i) ≠ 0) ≤
    lCount (fun p : LF t × LF t => lHard p.1 p.2) * (3/4 : ℚ)^S.card := by
  classical
  have h (R : Finset (Fin (3*t))) : lfDecayConfigs R =
      lSet (fun p : LF t × LF t => lHard p.1 p.2 ∧
        ∀ i ∈ R, p.2 i ≠ 0 ∨ p.2 (lPrev i) ≠ 0) := by
    ext p
    rw [lfDecayMem, lfMem_set]
    rfl
  have h0 : lfDecayConfigs (∅ : Finset (Fin (3*t))) =
      lSet (fun p : LF t × LF t => lHard p.1 p.2) := by
    ext p
    rw [lfDecayMem, lfMem_set]
    simp
  unfold lCount
  simpa only [h S, h0] using lfDecayAux S hdis

end LaneDecay

private def lfFourierFree (y : LF t) (i : Fin (3*t)) : Prop :=
  y i = 0 ∧ y (lPrev i) = 0

private lemma lfFourierHardUnit (y : LF t) (i : Fin (3*t))
    (hi : lfFourierFree y i) : lHard (lUnit i) y := by
  intro j hj
  by_cases h : j = i
  · subst j
    exact hi
  · exact False.elim (hj (by simp [lUnit, h]))

private lemma lfFourierHardAdd {x w y : LF t} (hx : lHard x y) (hw : lHard w y) :
    lHard (x + w) y := by
  intro i hi
  by_cases hx0 : x i = 0
  · apply hw i
    intro hw0
    exact hi (by simp [Pi.add_apply, hx0, hw0])
  · exact hx i hx0

private lemma lfFourierAddEqZero {a b : ZMod 2} : a + b = 0 ↔ a = b := by
  rw [← eq_neg_iff_add_eq_zero, ZMod.neg_eq_self_mod_two]

private lemma lfFourierSameResidue {y z : LF t}
    (h : ∀ x : LF t, lLane x ∧ lHard x y → lDot z x = 0)
    {i j : Fin (3*t)} (hi : lfFourierFree y i) (hj : lfFourierFree y j)
    (hij : i.val % 3 = j.val % 3) : z i = z j := by
  have hLane : lLane (lUnit i + lUnit j) := by
    intro v
    rw [lfDot_add_right, lfDot_unit, lfDot_unit]
    have he : (lDual v : LF t) i = lDual v j := by simp [lDual, hij]
    rw [he, lfAdd_self]
  have hzero := h (lUnit i + lUnit j) ⟨hLane,
    lfFourierHardAdd (lfFourierHardUnit y i hi) (lfFourierHardUnit y j hj)⟩
  rw [lfDot_add_right, lfDot_unit, lfDot_unit] at hzero
  exact lfFourierAddEqZero.mp hzero

private lemma lfFourierThreeResidues {y z : LF t}
    (h : ∀ x : LF t, lLane x ∧ lHard x y → lDot z x = 0)
    {i j k : Fin (3*t)} (hi : lfFourierFree y i) (hj : lfFourierFree y j)
    (hk : lfFourierFree y k) (ri : i.val % 3 = 0) (rj : j.val % 3 = 1)
    (rk : k.val % 3 = 2) : z k = z i + z j := by
  have hLane : lLane (lUnit i + lUnit j + lUnit k) := by
    intro v
    simp only [lfDot_add_right, lfDot_unit]
    have hvi : (lDual v : LF t) i = v 0 := by simp [lDual, ri]
    have hvj : (lDual v : LF t) j = v 1 := by simp [lDual, rj]
    have hvk : (lDual v : LF t) k = v 0 + v 1 := by simp [lDual, rk]
    rw [hvi, hvj, hvk, lfAdd_self]
  have hzero := h (lUnit i + lUnit j + lUnit k) ⟨hLane,
    lfFourierHardAdd (lfFourierHardAdd (lfFourierHardUnit y i hi)
      (lfFourierHardUnit y j hj)) (lfFourierHardUnit y k hk)⟩
  simp only [lfDot_add_right, lfDot_unit] at hzero
  exact (lfFourierAddEqZero.mp hzero).symm

-- The first two residues determine the third only when both are constrained.
private lemma lfFourierInterpolate {p0 p1 p2 : Prop} {a b c : ZMod 2}
    (h : p0 → p1 → p2 → c = a + b) :
    ∃ v : Fin 2 → ZMod 2,
      (p0 → a = v 0) ∧ (p1 → b = v 1) ∧ (p2 → c = v 0 + v 1) := by
  classical
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  by_cases h0 : p0 <;> by_cases h1 : p1
  · refine ⟨fun i => if i = 0 then a else b, by simp, by simp [h10], ?_⟩
    simpa [h10] using h h0 h1
  · refine ⟨fun i => if i = 0 then a else c + a, by simp, by simp [h1], ?_⟩
    intro _
    simp [h10]
    calc
      c = c + (a + a) := by rw [lfAdd_self, add_zero]
      _ = a + (c + a) := by ac_rfl
  · refine ⟨fun i => if i = 0 then c + b else b, by simp [h0], by simp [h10], ?_⟩
    intro _
    simp [h10, add_assoc, lfAdd_self]
  · exact ⟨fun i => if i = 0 then 0 else c, by simp [h0], by simp [h1], by simp [h10]⟩

private lemma lfFourierCoverIff (y z : LF t) :
    (∃ v : Fin 2 → ZMod 2, lCover (z + lDual v) y) ↔
      ∀ x : LF t, lLane x ∧ lHard x y → lDot z x = 0 := by
  classical
  constructor
  · rintro ⟨v, hv⟩ x hx
    have hfree (i : Fin (3*t)) (hi : lfFourierFree y i) : z i = lDual v i := by
      apply lfFourierAddEqZero.mp
      change (z + lDual v : LF t) i = 0
      by_contra hne
      exact (hv i hne).elim (fun h => h hi.1) (fun h => h hi.2)
    calc
      lDot z x = lDot (lDual v) x := by
        unfold lDot
        refine Finset.sum_congr rfl (fun i _ => ?_)
        by_cases hxi : x i = 0
        · simp [hxi]
        · rw [hfree i (hx.2 i hxi)]
      _ = 0 := hx.1 v
  · intro h
    let P (r : ℕ) : Prop := ∃ i : Fin (3*t), lfFourierFree y i ∧ i.val % 3 = r
    let k (r : ℕ) (hr : P r) : Fin (3*t) := Classical.choose hr
    have hk (r : ℕ) (hr : P r) : lfFourierFree y (k r hr) ∧ (k r hr).val % 3 = r :=
      Classical.choose_spec hr
    let c (r : ℕ) : ZMod 2 := if hr : P r then z (k r hr) else 0
    have hc (r : ℕ) (hr : P r) : c r = z (k r hr) := dite_eq_left hr
    have hsum (h0 : P 0) (h1 : P 1) (h2 : P 2) : c 2 = c 0 + c 1 := by
      rw [hc 2 h2, hc 0 h0, hc 1 h1]
      exact lfFourierThreeResidues h (hk 0 h0).1 (hk 1 h1).1 (hk 2 h2).1
        (hk 0 h0).2 (hk 1 h1).2 (hk 2 h2).2
    obtain ⟨v, hv0, hv1, hv2⟩ := lfFourierInterpolate hsum
    refine ⟨v, ?_⟩
    intro i hi
    by_cases hyi : y i = 0
    · right
      intro hyp
      have hfi : lfFourierFree y i := ⟨hyi, hyp⟩
      have hp (r : ℕ) (hr : i.val % 3 = r) : P r := ⟨i, hfi, hr⟩
      have he (r : ℕ) (hr : i.val % 3 = r) : z i = c r := by
        rw [hc r (hp r hr)]
        exact lfFourierSameResidue h hfi (hk r (hp r hr)).1 (hr.trans (hk r (hp r hr)).2.symm)
      apply hi
      change z i + lDual v i = 0
      apply lfFourierAddEqZero.mpr
      have hr : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hr with hr | hr | hr
      · simpa [lDual, hr] using (he 0 hr).trans (hv0 (hp 0 hr))
      · simpa [lDual, hr] using (he 1 hr).trans (hv1 (hp 1 hr))
      · simpa [lDual, hr] using (he 2 hr).trans (hv2 (hp 2 hr))
    · exact Or.inl hyi

private lemma lfFourierNonzero (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
  apply ZMod.val_injective 2
  rw [ZMod.val_one'' (by decide : 2 ≠ 1)]
  have hlt := ZMod.val_lt a
  have hne := (ZMod.val_ne_zero a).mpr ha
  omega

open scoped Classical in
private theorem lfFourierFiber (y z : LF t) :
    let fiber := (Finset.univ : Finset (LF t)).filter (fun x => lLane x ∧ lHard x y)
    (∑ x ∈ fiber, if lDot z x = 0 then (1 : ℚ) else -1) =
      if ∃ v : Fin 2 → ZMod 2, lCover (z + lDual v) y then (fiber.card : ℚ) else 0 := by
  intro fiber
  have hmem (x : LF t) : x ∈ fiber ↔ lLane x ∧ lHard x y := by simp [fiber]
  by_cases h : ∃ v : Fin 2 → ZMod 2, lCover (z + lDual v) y
  · rw [ite_eq_left h]
    have ha := (lfFourierCoverIff y z).mp h
    calc
      _ = ∑ _x ∈ fiber, (1 : ℚ) := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [ite_eq_left (ha x ((hmem x).mp hx))]
      _ = _ := by simp [nsmul_eq_mul]
  · rw [ite_eq_right h]
    have ha : ¬ ∀ x : LF t, lLane x ∧ lHard x y → lDot z x = 0 :=
      fun hh => h ((lfFourierCoverIff y z).mpr hh)
    obtain ⟨w, hbad⟩ := Classical.not_forall.mp ha
    obtain ⟨hw, hne⟩ := Classical.not_imp.mp hbad
    refine Finset.sum_involution (fun (x : LF t) _ => x + w) ?_ ?_ ?_ ?_
    · intro x _
      rw [lfDot_add_right]
      by_cases hx : lDot z x = 0
      · simp [hx, hne]
      · have he := (lfFourierNonzero _ hx).trans (lfFourierNonzero _ hne).symm
        rw [ite_eq_right hx, ite_eq_left (lfFourierAddEqZero.mpr he), neg_add_cancel]
    · intro x _ _ he
      have hd := congrArg (lDot z) he
      rw [lfDot_add_right] at hd
      exact hne (add_left_cancel (hd.trans (add_zero _).symm))
    · intro x hx
      have hx' := (hmem x).mp hx
      apply (hmem (x + w)).mpr
      refine ⟨?_, lfFourierHardAdd hx'.2 hw.2⟩
      intro v
      rw [lfDot_add_right, hx'.1 v, hw.1 v, add_zero]
    · intro x _
      funext i
      simp only [Pi.add_apply, add_assoc, lfAdd_self, add_zero]

private lemma lfPrev_residue (i : Fin (3*t)) : (lPrev i).val % 3 = (i.val + 2) % 3 := by
  change (if i.val = 0 then 3*t-1 else i.val-1) % 3 = _
  have hi := i.isLt
  split_ifs <;> omega

private lemma lfNext_residue (i : Fin (3*t)) : (lNext i).val % 3 = (i.val + 1) % 3 := by
  rw [lfNext_val]
  split_ifs <;> omega

private lemma lfSameResiduePairs {i j : Fin (3*t)} (he : i ≠ j) (h : i.val % 3 = j.val % 3) :
    Disjoint ({i, lPrev i} : Finset _) {j, lPrev j} := by
  apply Finset.disjoint_left.mpr
  intro k hk hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk hj
  rcases hk with hki | hki <;> rcases hj with hkj | hkj
  · exact he (hki.symm.trans hkj)
  · have hh := congrArg (fun i : Fin (3*t) => i.val % 3) (hki.symm.trans hkj)
    rw [lfPrev_residue] at hh
    omega
  · have hh := congrArg (fun i : Fin (3*t) => i.val % 3) (hki.symm.trans hkj)
    rw [lfPrev_residue] at hh
    omega
  · exact he (lfPrev_inj (hki.symm.trans hkj))

private lemma lfChooseColor (z : LF t) (hw : t ≤ (lfSupp z).card) :
    ∃ S : Finset (Fin (3*t)), S ⊆ lfSupp z ∧ t/3 ≤ S.card ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint ({i, lPrev i} : Finset _) {j, lPrev j} := by
  let A (r : ℕ) := (lfSupp z).filter (fun i => i.val % 3 = r)
  have hcov : lfSupp z ⊆ A 0 ∪ A 1 ∪ A 2 := by
    intro i hi
    simp only [A, Finset.mem_union, Finset.mem_filter, hi, true_and]
    omega
  have hc := Finset.card_le_card hcov
  have hc' := Finset.card_union_le (A 0 ∪ A 1) (A 2)
  have hc'' := Finset.card_union_le (A 0) (A 1)
  have he : ∃ r ∈ Finset.range 3, t/3 ≤ (A r).card := by
    by_contra! h
    have h0 := h 0 (by simp)
    have h1 := h 1 (by simp)
    have h2 := h 2 (by simp)
    omega
  obtain ⟨r,_,hr⟩ := he
  refine ⟨A r, Finset.filter_subset _ _, hr, ?_⟩
  intro i hi j hj hij
  exact lfSameResiduePairs hij ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)

private def lfTriple (r : ℕ) (hr : r < 3) (k : Fin t) : Fin (3*t) :=
  ⟨3*k.val+r, by have := k.isLt; omega⟩

private lemma lfDualBig (v : Fin 2 → ZMod 2) (hne : v ≠ 0) :
    2*t ≤ (lfSupp (lDual v : LF t)).card := by
  classical
  let E (r : ℕ) (hr : r < 3) := (Finset.univ : Finset (Fin t)).image (lfTriple r hr)
  have he (r : ℕ) (hr : r < 3) : (E r hr).card = t := by
    unfold E
    rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro k l h
    apply Fin.ext
    have hh := congrArg Fin.val h
    change 3*k.val+r = 3*l.val+r at hh
    omega
  have hr (r : ℕ) (hr : r < 3) (i : Fin (3*t)) (hi : i ∈ E r hr) : i.val % 3 = r := by
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    change (3*k.val+r)%3 = r
    omega
  let bit (r : ℕ) := if r=0 then v 0 else if r=1 then v 1 else v 0+v 1
  have hb : ∃ r s : ℕ, r < 3 ∧ s < 3 ∧ r ≠ s ∧ bit r ≠ 0 ∧ bit s ≠ 0 := by
    by_cases h0 : v 0 = 0 <;> by_cases h1 : v 1 = 0
    · exfalso
      apply hne
      funext i
      fin_cases i <;> assumption
    · exact ⟨1,2,by decide,by decide,by decide,by simpa [bit],by simpa [bit,h0]⟩
    · exact ⟨0,2,by decide,by decide,by decide,by simpa [bit],by simpa [bit,h1]⟩
    · exact ⟨0,1,by decide,by decide,by decide,by simpa [bit],by simpa [bit]⟩
  obtain ⟨r,s,hr',hs',hrs,hbr,hbs⟩ := hb
  have hd : Disjoint (E r hr') (E s hs') := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact hrs ((hr r hr' i hi).symm.trans (hr s hs' i hj))
  have hsub (q : ℕ) (hq : q < 3) (hbq : bit q ≠ 0) : E q hq ⊆ lfSupp (lDual v) := by
    intro i hi
    exact (lfSupp_mem _ _).mpr (by simpa [lDual, hr q hq i hi, bit] using hbq)
  have hc := Finset.card_le_card (Finset.union_subset (hsub r hr' hbr) (hsub s hs' hbs))
  rw [Finset.card_union_of_disjoint hd, he, he] at hc
  omega

private lemma lfDistinctWeights (z : LF t) {v w : Fin 2 → ZMod 2} (hvw : v ≠ w) :
    2*t ≤ (lfSupp (z + lDual v)).card + (lfSupp (z + lDual w)).card := by
  classical
  have hne : v + w ≠ 0 := by
    intro h
    apply hvw
    funext i
    exact lfFourierAddEqZero.mp (congrFun h i)
  have hdual : (lDual (v+w) : LF t) = (z + lDual v) + (z + lDual w) := by
    rw [lfDual_add]
    ext i
    simp only [Pi.add_apply]
    calc
      _ = (z i + z i) + (lDual v i + lDual w i) := by rw [lfAdd_self, zero_add]
      _ = _ := by ac_rfl
  have hsub : lfSupp (lDual (v+w)) ⊆ lfSupp (z + lDual v) ∪ lfSupp (z + lDual w) := by
    rw [hdual]
    intro i hi
    simp only [Finset.mem_union, lfSupp_mem] at hi ⊢
    by_contra! h
    exact hi (by simp [h.1,h.2])
  exact (lfDualBig (t := t) _ hne).trans
    ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))

private lemma lfChooseLead (z : LF t) : ∃ v : Fin 2 → ZMod 2,
    ∀ w ≠ v, t ≤ (lfSupp (z + lDual w)).card := by
  by_cases h : ∃ v : Fin 2 → ZMod 2, (lfSupp (z + lDual v)).card < t
  · obtain ⟨v,hv⟩ := h
    refine ⟨v, ?_⟩
    intro w hw
    have hsum := lfDistinctWeights z hw
    omega
  · exact ⟨0, fun w _ => Nat.le_of_not_gt (fun h' => h ⟨w,h'⟩)⟩

private def lfCoverGood (u : LF t) (p : LF t × LF t) : Prop := lGood p ∧ lCover u p.2

-- One residue class supplies disjoint predecessor pairs for the decay bound.
private lemma lfHeavy (ht : 32 ≤ t) (z : LF t) (hw : t ≤ (lfSupp z).card) :
    lCount (lfCoverGood z) ≤ lCount (lGood (t := t)) * 2^12 * (3/4 : ℚ)^(t/3) := by
  obtain ⟨S,hS,hsc,hd⟩ := lfChooseColor z hw
  calc
    _ ≤ lCount (fun p : LF t × LF t => lHard p.1 p.2 ∧ ∀ i ∈ S, p.2 i ≠ 0 ∨ p.2 (lPrev i) ≠ 0) :=
      lfCount_mono (fun p hp => ⟨hp.1.2.2, fun i hi => hp.2 i ((lfSupp_mem _ _).mp (hS hi))⟩)
    _ ≤ lCount (fun p : LF t × LF t => lHard p.1 p.2) * (3/4 : ℚ)^S.card := lfDecay S hd
    _ ≤ lCount (lGood (t := t)) * 2^12 * (3/4 : ℚ)^(t/3) := by
      apply mul_le_mul (lfNorm ht) _ (by positivity) (by have := lfCount_nonneg (lGood (t := t)); positivity)
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hsc

private lemma lfTwoSupport (z : LF t) (h0 : z ≠ 0) (h1 : ∀ i, z ≠ lUnit i) :
    ∃ i j : Fin (3*t), i ≠ j ∧ z i ≠ 0 ∧ z j ≠ 0 := by
  classical
  have he : ∃ i, z i ≠ 0 := by
    by_contra! h
    exact h0 (funext h)
  obtain ⟨i,hi⟩ := he
  have he' : ∃ j, i ≠ j ∧ z j ≠ 0 := by
    by_contra! h
    apply h1 i
    funext j
    by_cases hj : j = i
    · subst j
      simp [lUnit, lfFourierNonzero _ hi]
    · simpa [lUnit, hj] using h j (fun hji => hj hji.symm)
  obtain ⟨j,hij,hj⟩ := he'
  exact ⟨i,j,hij,hi,hj⟩

private def lfRotate (x : LF t) : LF t := fun i => x (lPrev i)

private def lfNextPerm (t : ℕ) : Equiv.Perm (Fin (3*t)) where
  toFun := lNext
  invFun := lPrev
  left_inv := lfPrev_next
  right_inv := lfNext_prev

private lemma lfDualRotate (v : Fin 2 → ZMod 2) (i : Fin (3*t)) :
    lDual v (lNext i) = lDual (fun j => if j = 0 then v 1 else v 0 + v 1) i := by
  have hr : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · have hn : (lNext i).val % 3 = 1 := by rw [lfNext_residue]; omega
    simp [lDual, hr, hn]
  · have hn : (lNext i).val % 3 = 2 := by rw [lfNext_residue]; omega
    simp [lDual, hr, hn]
  · have hn : (lNext i).val % 3 = 0 := by rw [lfNext_residue]; omega
    simp [lDual, hr, hn]
    rw [← add_assoc, add_comm (v 1) (v 0), add_assoc, lfAdd_self, add_zero]

private lemma lfLaneRotate {x : LF t} (hx : lLane x) : lLane (lfRotate x) := by
  intro v
  let f (i : Fin (3*t)) := lDual v i * lfRotate x i
  calc
    lDot (lDual v) (lfRotate x) = ∑ i, f (lNext i) := (Equiv.sum_comp (lfNextPerm t) f).symm
    _ = 0 := by
      simpa [f, lfRotate, lfPrev_next, lfDualRotate, lDot] using
        hx (fun j => if j = 0 then v 1 else v 0 + v 1)

private lemma lfRotateGood (p : LF t × LF t) (hp : lGood p) : lGood (lfRotate p.1, lfRotate p.2) :=
  ⟨lfLaneRotate hp.1, lfLaneRotate hp.2.1, fun i hi => hp.2.2 (lPrev i) hi⟩

private lemma lfRotateInj : Function.Injective (@lfRotate t) := by
  intro a b h
  funext i
  simpa [lfRotate, lfPrev_next] using congrFun h (lNext i)

private noncomputable def lfUnitCount (i : Fin (3*t)) : ℚ := lCount (lfCoverGood (lUnit i))

private lemma lfRotateCount (i : Fin (3*t)) : lfUnitCount i ≤ lfUnitCount (lNext i) := by
  classical
  unfold lfUnitCount lCount
  apply Nat.cast_le.mpr
  apply Finset.card_le_card_of_injOn (fun p : LF t × LF t => (lfRotate p.1, lfRotate p.2))
  · intro p hp
    have h := (lfMem_set (lfCoverGood (lUnit i)) p).mp hp
    apply (lfMem_set (lfCoverGood (lUnit (lNext i))) _).mpr
    refine ⟨lfRotateGood p h.1, (lfCover_unit_iff _ _).mpr ?_⟩
    simpa [lfRotate, lfHit, lfPrev_next] using (lfCover_unit_iff i p.2).mp h.2
  · intro p _ q _ hpq
    exact Prod.ext (lfRotateInj (congrArg Prod.fst hpq)) (lfRotateInj (congrArg Prod.snd hpq))

-- Rotating gives a nondecreasing sequence of counts that returns to its start.
private lemma lfUnitSame (i j : Fin (3*t)) : lfUnitCount i = lfUnitCount j := by
  have hn : 0 < 3*t := by have := i.isLt; omega
  let f (r : ℕ) : Fin (3*t) := ⟨r % (3*t), Nat.mod_lt _ hn⟩
  have hf (r : ℕ) : f (r+1) = lNext (f r) := by
    apply Fin.ext
    change (r+1)%(3*t) = (r%(3*t)+1)%(3*t)
    simp [Nat.mod_add_mod]
  have hm : Monotone (fun r => lfUnitCount (f r)) := by
    apply monotone_nat_of_le_succ
    intro r
    rw [hf]
    exact lfRotateCount _
  have hEnd : f (3*t) = f 0 := by apply Fin.ext; simp [f]
  have hi : f i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hj : f j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  have he (k : Fin (3*t)) : lfUnitCount (f k.val) = lfUnitCount (f 0) := by
    apply le_antisymm
    · simpa only [hEnd] using hm k.isLt.le
    · exact hm (Nat.zero_le _)
  rw [← hi, ← hj, he i, he j]

open scoped Classical in
private noncomputable def lfCoeff (z : LF t) : ℚ :=
  lWords.sum (fun p => if lDot z p.1 = 0 then 1 else -1)

private def lfExistsCover (z : LF t) (p : LF t × LF t) : Prop :=
  lGood p ∧ ∃ v : Fin 2 → ZMod 2, lCover (z + lDual v) p.2

-- On each fiber over the second word, all signs are positive or cancel in pairs.
private lemma lfCoeff_eq (z : LF t) : lfCoeff z = lCount (lfExistsCover z) := by
  classical
  unfold lfCoeff lWords lCount lSet
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one]
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : lLane y
  · have h := lfFourierFiber y z
    dsimp only at h
    rw [Finset.sum_filter] at h
    have hm : (((Finset.univ : Finset (LF t)).filter (fun x => lLane x ∧ lHard x y)).card : ℚ) =
        ∑ x : LF t, if lLane x ∧ lHard x y then 1 else 0 := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      simp only [Nat.cast_one]
      rw [Finset.sum_filter]
    rw [hm] at h
    by_cases hv : ∃ v : Fin 2 → ZMod 2, lCover (z + lDual v) y
    · simpa [lGood, lfExistsCover, hy, hv] using h
    · simpa [lGood, lfExistsCover, hy, hv] using h
  · simp [lGood, lfExistsCover, hy]

private lemma lfDual_zero : (lDual (0 : Fin 2 → ZMod 2) : LF t) = 0 := by
  ext i
  simp [lDual]

private lemma lfUnitLeCoeff (i : Fin (3*t)) : lfUnitCount i ≤ lfCoeff (lUnit i) := by
  rw [lfCoeff_eq]
  exact lfCount_mono (fun p hp => ⟨hp.1, 0, by simpa [lfDual_zero] using hp.2⟩)

-- Count the possible covering representatives by a union bound.
set_option maxHeartbeats 1000000 in
private lemma lfCoverBound (ht : 32 ≤ t) (z : LF t) (v : Fin 2 → ZMod 2)
    (hv : ∀ w ≠ v, t ≤ (lfSupp (z + lDual w)).card) :
    lfCoeff z ≤ lCount (lfCoverGood (z + lDual v)) +
      lCount (lGood (t := t))*3*2^12*(3/4 : ℚ)^(t/3) := by
  classical
  let V := (Finset.univ : Finset (Fin 2 → ZMod 2)).erase v
  let S (w : Fin 2 → ZMod 2) := lSet (lfCoverGood (z + lDual w))
  have hsub : lSet (lfExistsCover z) ⊆ S v ∪ V.biUnion S := by
    intro p hp
    obtain ⟨hg,w,hw⟩ := (lfMem_set (lfExistsCover z) p).mp hp
    have hm : p ∈ S w := (lfMem_set (lfCoverGood (z + lDual w)) p).mpr ⟨hg,hw⟩
    by_cases h : w = v
    · exact Finset.mem_union_left _ (h ▸ hm)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, by simp [V,h],hm⟩)
  have hb : (V.biUnion S).card ≤ ∑ w ∈ V, (S w).card := Finset.card_biUnion_le
  have hn : (lSet (lfExistsCover z)).card ≤ (S v).card + ∑ w ∈ V, (S w).card :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le (S v) (V.biUnion S)).trans
      (Nat.add_le_add_left hb (S v).card))
  have hq : lCount (lfExistsCover z) ≤ lCount (lfCoverGood (z + lDual v)) +
      ∑ w ∈ V, lCount (lfCoverGood (z + lDual w)) := by
    unfold lCount
    exact_mod_cast hn
  have hc : V.card = 3 := by
    unfold V
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp [Fintype.card_fin, ZMod.card]
  have hh : (∑ w ∈ V, lCount (lfCoverGood (z + lDual w))) ≤
      lCount (lGood (t := t))*3*2^12*(3/4 : ℚ)^(t/3) := by
    calc
      _ ≤ ∑ _w ∈ V, lCount (lGood (t := t))*2^12*(3/4 : ℚ)^(t/3) := by
        apply Finset.sum_le_sum
        intro w hw
        exact lfHeavy ht _ (hv w (Finset.mem_erase.mp hw).1)
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, hc]; ring
  rw [lfCoeff_eq]
  exact hq.trans (add_le_add (le_refl _) hh)

private lemma lfMain (ht : 32 ≤ t) (z : LF t)
    (h0 : ∀ v, z ≠ lDual v) (h1 : ∀ v i, z ≠ lDual v + lUnit i) (i : Fin (3*t)) :
    lfCoeff z + lCount (lGood (t := t))/2^17 ≤ lfCoeff (lUnit i) +
      lCount (lGood (t := t))*3*2^12*(3/4 : ℚ)^(t/3) := by
  obtain ⟨v,hv⟩ := lfChooseLead z
  have hv0 : z + lDual v + lDual v = z := by
    funext k
    simp [Pi.add_apply, add_assoc, lfAdd_self]
  have hv1 : z + lDual v ≠ 0 := by
    intro h
    rw [h, zero_add] at hv0
    exact h0 v hv0.symm
  have hv2 (j : Fin (3*t)) : z + lDual v ≠ lUnit j := by
    intro h
    rw [h, add_comm] at hv0
    exact h1 v j hv0.symm
  obtain ⟨j,k,hjk,hj,hk⟩ := lfTwoSupport (z + lDual v) hv1 hv2
  have hg := lfGapCard ht hjk hj hk
  have hb := lfCoverBound ht z v hv
  have hu := lfUnitLeCoeff i
  rw [← lfUnitSame j i] at hu
  change lCount (lfCoverGood (lUnit j)) ≤ lfCoeff (lUnit i) at hu
  change lCount (lfCoverGood (z + lDual v)) + lCount (lGood (t := t))/2^17 ≤
    lCount (lfCoverGood (lUnit j)) at hg
  linarith

end PEqualNP.Outside.L_lib_1006_aux

open PEqualNP.Outside.L_lib_1006_aux

theorem PEqualNP.Outside.L_lib_1006 :
    ∀ (t : ℕ) (ht : 0 < t), 32 ≤ t →
      letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      let F := ZMod 2
      let a := 3*t
      let W := Fin a → F
      let next := fun i : Fin a =>
        (⟨(i.val+1) % a, Nat.mod_lt _ (Nat.mul_pos (Nat.zero_lt_succ 2) ht)⟩ : Fin a)
      let dual := fun (v : Fin 2 → F) (i : Fin a) =>
        if i.val % 3 = 0 then v 0 else if i.val % 3 = 1 then v 1 else v 0 + v 1
      let dot := fun (x y : W) => ∑ i, x i * y i
      let lane := fun x : W => ∀ v, dot (dual v) x = 0
      let words := (Finset.univ : Finset (W × W)).filter (fun w =>
        lane w.1 ∧ lane w.2 ∧ ∀ i, w.2 i * w.1 i = 0 ∧ w.2 i * w.1 (next i) = 0)
      let coeff := fun z : W => words.sum (fun w => if dot z w.1 = 0 then (1 : ℚ) else -1)
      let unit := fun (j i : Fin a) => if i = j then (1 : F) else 0
      ∀ z : W, (∀ v, z ≠ dual v) → (∀ v j, z ≠ dual v + unit j) →
        ∀ i : Fin a,
          coeff z + (words.card : ℚ)/2^17 ≤ coeff (unit i) +
            (words.card : ℚ)*3*2^12*(3/4 : ℚ)^(t/3) := by
  intro t ht h32 F a W next dual dot lane words coeff unit z h0 h1 i
  have hd (v : Fin 2 → F) : dual v = lDual (t := t) v := by
    funext k
    by_cases hk0 : k.val % 3 = 0 <;> by_cases hk1 : k.val % 3 = 1 <;>
      simp [dual, lDual, hk0, hk1]
  have hdot (u v : W) : dot u v = lDot u v := rfl
  have hlane (u : W) : lane u ↔ lLane u := by
    simp only [lane, lLane, hdot, hd]
    rfl
  have hu (j : Fin a) : unit j = lUnit j := by
    funext k
    by_cases hk : k = j <;> simp [unit, lUnit, hk]
  have hwords : words = lWords (t := t) := by
    ext p
    rw [show lWords (t := t) = lSet lGood from rfl, lfMem_set]
    simp only [words, Finset.mem_filter, Finset.mem_univ, true_and, hlane]
    change (lLane p.1 ∧ lLane p.2 ∧ ∀ j, p.2 j * p.1 j = 0 ∧ p.2 j * p.1 (lNext j) = 0) ↔ lGood p
    constructor
    · rintro ⟨hx,hy,h⟩
      refine ⟨hx,hy,fun j hj => ⟨?_,?_⟩⟩
      · exact (mul_eq_zero.mp (h j).1).resolve_right hj
      · apply (mul_eq_zero.mp (h (lPrev j)).2).resolve_right
        simpa only [lfNext_prev] using hj
    · rintro ⟨hx,hy,h⟩
      refine ⟨hx,hy,fun j => ⟨?_,?_⟩⟩
      · apply mul_eq_zero.mpr
        by_cases h0' : p.1 j = 0
        · exact Or.inr h0'
        · exact Or.inl (h j h0').1
      · apply mul_eq_zero.mpr
        by_cases h0' : p.1 (lNext j) = 0
        · exact Or.inr h0'
        · exact Or.inl (by simpa only [lfPrev_next] using (h (lNext j) h0').2)
  have hc (u : W) : coeff u = lfCoeff u := by
    simp only [coeff]
    unfold lfCoeff
    rw [hwords]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : lDot u p.1 = 0
    · have hp' : dot u p.1 = 0 := hp
      simp only [ite_eq_left hp, ite_eq_left hp']
    · have hp' : dot u p.1 ≠ 0 := hp
      simp only [ite_eq_right hp, ite_eq_right hp']
  rw [hc z, hc (unit i), hwords, hu i]
  refine lfMain h32 z (fun v => ?_) (fun v j => ?_) i
  · rw [← hd v]
    exact h0 v
  · rw [← hd v, ← hu j]
    exact h1 v j

