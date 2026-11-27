import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_238_aux
open PEqualNP.ProofComplexity
section Clauses
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def tableOf (a : V → Bool) : Finset V := Finset.univ.filter (fun v => a v = true)
def assignOf (A : Finset V) (v : V) : Bool := decide (v ∈ A)

omit [DecidableEq V] in
@[local simp] theorem mem_tableOf (a : V → Bool) (v : V) : v ∈ tableOf a ↔ a v = true := by
  simp [tableOf]
omit [Fintype V] in
@[local simp] theorem assignOf_true (A : Finset V) (v : V) : assignOf A v = true ↔ v ∈ A := by
  simp [assignOf]
@[local simp] theorem tableOf_assignOf (A : Finset V) : tableOf (assignOf A) = A := by
  ext v; simp

 def MaxReject (P : Finset V → Prop) (A : Finset V) : Prop :=
  ¬ P A ∧ ∀ v ∉ A, P (insert v A)

noncomputable def rejects (P : Finset V → Prop) : Finset (Finset V) := by
  classical exact Finset.univ.filter (MaxReject P)
@[local simp] theorem mem_rejects (P : Finset V → Prop) (A : Finset V) :
    A ∈ rejects P ↔ MaxReject P A := by
  classical simp [rejects]

 def posEmbed : V ↪ Literal V := ⟨fun v => (v, true), fun _ _ h => congrArg Prod.fst h⟩
 def missing (A : Finset V) : Clause V := (Finset.univ \ A).map posEmbed

@[local simp] theorem mem_missing (A : Finset V) (l : Literal V) :
    l ∈ missing A ↔ l.1 ∉ A ∧ l.2 = true := by
  rcases l with ⟨v, b⟩
  rw [missing, Finset.mem_map]
  constructor
  · rintro ⟨u, hu, he⟩
    change (u, true) = (v, b) at he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨(Finset.mem_sdiff.mp hu).2, rfl⟩
  · rintro ⟨hv, rfl⟩
    exact ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩

 theorem missing_inj : Function.Injective (missing : Finset V → Clause V) := by
  intro A B h
  ext v
  have hh := Finset.ext_iff.mp h (v, true)
  have hn : v ∉ A ↔ v ∉ B := by simpa only [mem_missing, and_true] using hh
  simpa only [not_not] using not_congr hn

noncomputable def canon (P : Finset V → Prop) : Finset (Clause V) :=
  (rejects P).map ⟨missing, missing_inj⟩

 theorem canon_mem (P : Finset V → Prop) (C : Clause V) :
    C ∈ canon P ↔ ∃ A, MaxReject P A ∧ missing A = C := by
  simp [canon]

 theorem extend_reject {P : Finset V → Prop} {A : Finset V} (h : ¬ P A) :
    ∃ B, MaxReject P B ∧ A ⊆ B := by
  classical
  let s := (Finset.univ : Finset (Finset V)).filter (fun B => A ⊆ B ∧ ¬ P B)
  have hA : A ∈ s := by simp [s, h]
  obtain ⟨B, hB, hmax⟩ := Finset.exists_max_image s Finset.card ⟨A, hA⟩
  have h' : A ⊆ B ∧ ¬ P B := by simpa [s] using hB
  refine ⟨B, ⟨h'.2, fun v hv => ?_⟩, h'.1⟩
  by_contra hi
  have hm : insert v B ∈ s := by
    simp [s, h'.1.trans (Finset.subset_insert _ _), hi]
  have hh := hmax (insert v B) hm
  rw [Finset.card_insert_of_notMem hv] at hh
  omega

 theorem canon_enc (P : Finset V → Prop) (hm : Monotone P) (a : V → Bool) :
    P (tableOf a) ↔ Satisfies a (↑(canon P) : Set _) := by
  classical
  constructor
  · intro ha C hC
    obtain ⟨B, hb, rfl⟩ := (canon_mem P C).mp hC
    have hd : ¬ tableOf a ⊆ B := fun h => hb.1 (hm h ha)
    obtain ⟨v, hv, hn⟩ := Finset.not_subset.mp hd
    exact ⟨(v, true), (mem_missing _ _).mpr ⟨hn, rfl⟩, (mem_tableOf _ _).mp hv⟩
  · intro ha
    by_contra hn
    obtain ⟨B, hb, hsub⟩ := extend_reject hn
    obtain ⟨l, hl, hs⟩ := ha (missing B) ((canon_mem _ _).mpr ⟨B, hb, rfl⟩)
    have h := (mem_missing _ _).mp hl
    exact h.1 (hsub ((mem_tableOf _ _).mpr (hs.trans h.2)))

 theorem canon_pos (P : Finset V → Prop) (C : Clause V) (hC : C ∈ canon P)
    (l : Literal V) (hl : l ∈ C) : l.2 = true := by
  obtain ⟨A, _, rfl⟩ := (canon_mem _ _).mp hC
  exact ((mem_missing A l).mp hl).2

 theorem canon_forced (P : Finset V → Prop) (G : Finset (Clause V))
    (he : ∀ a : V → Bool, P (tableOf a) ↔ Satisfies a (↑G : Set _))
    (C : Clause V) (hC : C ∈ canon P) : ∃ B ∈ G, B.filter (fun l => l.2 = true) = C := by
  classical
  obtain ⟨A, hA, rfl⟩ := (canon_mem _ _).mp hC
  have hn : ¬ Satisfies (assignOf A) (↑G : Set _) := by
    intro hh
    exact hA.1 (by simpa using (he _).mpr hh)
  unfold Satisfies at hn
  push Not at hn
  obtain ⟨B, hB, hbad⟩ := hn
  refine ⟨B, hB, ?_⟩
  ext l
  rw [Finset.mem_filter, mem_missing]
  constructor
  · rintro ⟨hl, hs⟩
    exact ⟨fun hv => hbad ⟨l, hl, ((assignOf_true _ _).mpr hv).trans hs.symm⟩, hs⟩
  · rintro ⟨hv, hs⟩
    have hh : Satisfies (assignOf (insert l.1 A)) (↑G : Set _) :=
      (he _).mp (by simpa using hA.2 l.1 hv)
    obtain ⟨z, hz, hzsat⟩ := hh B hB
    have hne : assignOf A z.1 ≠ z.2 := fun heq => hbad ⟨z, hz, heq⟩
    have hvar : z.1 = l.1 := by
      by_contra hd
      apply hne
      simpa [assignOf, Finset.mem_insert, hd] using hzsat
    have hsign : z.2 = true := hzsat.symm.trans ((assignOf_true _ _).mpr (by simp [hvar]))
    have hzl : z = l := Prod.ext hvar (hsign.trans hs.symm)
    exact ⟨hzl ▸ hz, hs⟩

 theorem canon_bound (P : Finset V → Prop) (G : Finset (Clause V))
    (hf : ∀ C ∈ canon P, ∃ B ∈ G, B.filter (fun l => l.2 = true) = C)
    (k : ℕ) : ((canon P).filter (fun C => k ≤ C.card)).card ≤
      (G.filter (fun B => k ≤ B.card)).card := by
  classical
  let chooseB (C : Clause V) : Clause V := if h : C ∈ canon P then Classical.choose (hf C h) else ∅
  have hb (C : Clause V) (hc : C ∈ canon P) :
      chooseB C ∈ G ∧ (chooseB C).filter (fun l => l.2 = true) = C := by
    simp only [chooseB, dite_eq_left hc]
    exact Classical.choose_spec (hf C hc)
  apply Finset.card_le_card_of_injOn chooseB
  · intro C hc
    obtain ⟨hc, hk⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨(hb C hc).1, hk.trans ?_⟩
    calc
      C.card = ((chooseB C).filter (fun l => l.2 = true)).card :=
        congrArg Finset.card (hb C hc).2.symm
      _ ≤ (chooseB C).card := Finset.card_filter_le _ _
  · intro C hc D hd he
    rw [← (hb C (Finset.mem_filter.mp hc).1).2, ← (hb D (Finset.mem_filter.mp hd).1).2, he]

end Clauses
section Rows
variable {q n : ℕ}

 def rowOf (T : Finset (Fin n × (Fin q × Fin q))) (i : Fin n) : Finset (Fin q × Fin q) :=
  Finset.univ.filter (fun e => (i, e) ∈ T)

 def flatten (A : Fin n → Finset (Fin q × Fin q)) : Finset (Fin n × (Fin q × Fin q)) :=
  Finset.univ.filter (fun p => p.2 ∈ A p.1)

@[local simp] theorem mem_rowOf (T : Finset (Fin n × (Fin q × Fin q))) (i : Fin n) (e : Fin q × Fin q) :
    e ∈ rowOf T i ↔ (i, e) ∈ T := by simp [rowOf]
@[local simp] theorem mem_flatten (A : Fin n → Finset (Fin q × Fin q)) (p : Fin n × (Fin q × Fin q)) :
    p ∈ flatten A ↔ p.2 ∈ A p.1 := by simp [flatten]
@[local simp] theorem flatten_rowOf (T : Finset (Fin n × (Fin q × Fin q))) : flatten (rowOf T) = T := by
  ext p; rcases p with ⟨i, e⟩; simp
@[local simp] theorem rowOf_flatten (A : Fin n → Finset (Fin q × Fin q)) : rowOf (flatten A) = A := by
  funext i; ext e; simp

 theorem rowOf_insert (T : Finset (Fin n × (Fin q × Fin q))) (i : Fin n) (e : Fin q × Fin q) :
    rowOf (insert (i,e) T) = Function.update (rowOf T) i (insert e (rowOf T i)) := by
  funext j
  by_cases h : j = i
  · subst j; ext f; simp
  · ext f; simp [h]

 theorem missing_card_flatten (A : Fin n → Finset (Fin q × Fin q)) :
    (missing (flatten A)).card = ∑ i, (q * q - (A i).card) := by
  classical
  let fiber (i : Fin n) : Finset (Fin n × (Fin q × Fin q)) :=
    ((Finset.univ : Finset (Fin q × Fin q)) \ A i).map ⟨fun e => (i,e), fun _ _ h => congrArg Prod.snd h⟩
  have hf (i : Fin n) (p : Fin n × (Fin q × Fin q)) : p ∈ fiber i ↔ p.1 = i ∧ p.2 ∉ A i := by
    rcases p with ⟨j, e⟩
    simp only [fiber, Finset.mem_map]
    constructor
    · rintro ⟨f, hm, he⟩
      change (i, f) = (j, e) at he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨rfl, (Finset.mem_sdiff.mp hm).2⟩
    · rintro ⟨rfl, h⟩
      exact ⟨e, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
  have hu : Finset.univ \ flatten A = (Finset.univ : Finset (Fin n)).biUnion fiber := by
    ext p
    simp [hf]
  have hd : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint fiber := by
    intro i _ j _ hn
    apply Finset.disjoint_left.mpr
    intro p h₁ h₂
    exact hn (((hf i p).mp h₁).1.symm.trans ((hf j p).mp h₂).1)
  rw [missing, Finset.card_map, hu, Finset.card_biUnion hd]
  apply Finset.sum_congr rfl
  intro i _
  simp [fiber, Finset.card_sdiff_of_subset (Finset.subset_univ _), Fintype.card_prod]

 theorem canon_width (P : Finset (Fin n × (Fin q × Fin q)) → Prop) (k : ℕ) :
    ((canon P).filter (fun C => C.card = k)).card =
      (∑ A ∈ rejects P, if (missing A).card = k then 1 else 0) := by
  classical
  change (((rejects P).map ⟨missing, missing_inj⟩).filter (fun C => C.card = k)).card = _
  rw [Finset.filter_map, Finset.card_map]
  simp

end Rows


open scoped BigOperators


private theorem matrix_pow_walk_ite {S A : Type*} [Fintype S] [DecidableEq S]
    [CommSemiring A] (M : Matrix S S A) (n : ℕ) (s t : S) :
    (M ^ n) s t = ∑ p : Fin (n + 1) → S,
      if p 0 = s ∧ p (Fin.last n) = t then
        ∏ i : Fin n, M (p i.castSucc) (p i.succ) else 0 := by
  classical
  induction n generalizing s with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    symm
    rw [Fintype.sum_eq_single (fun _ => s)]
    · simp
    · intro p hp
      have hne : p 0 ≠ s := fun he => hp (funext fun i => Fin.eq_zero i ▸ he)
      simp [hne]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    let e := Fin.consEquiv (fun _ : Fin (n + 2) => S)
    conv_rhs => rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    have hstep (a : S) :
        ∏ i : Fin (n + 1),
          M (Fin.cons (α := fun _ => S) a p i.castSucc) (p i) =
          M a (p 0) * ∏ i : Fin n, M (p i.castSucc) (p i.succ) := by
      rw [Fin.prod_univ_succ]
      rfl
    rw [Fintype.sum_eq_single (p 0), Fintype.sum_eq_single s]
    · simp [e, hstep, mul_ite]
    · intro a ha
      simp [e, ha]
    · intro a ha
      simp [Ne.symm ha]

theorem matrix_pow_walks {S A : Type*} [Fintype S] [DecidableEq S]
    [CommSemiring A] (M : Matrix S S A) (n : ℕ) (s t : S) :
    (M ^ n) s t =
      ∑ p ∈ Finset.univ.filter (fun p : Fin (n + 1) → S =>
        p 0 = s ∧ p (Fin.last n) = t),
        ∏ i : Fin n, M (p i.castSucc) (p i.succ) := by
  rw [Finset.sum_filter, matrix_pow_walk_ite]

theorem matrix_pow_valid_walks {S A : Type*} [Fintype S] [DecidableEq S]
    [CommSemiring A] (valid : S → S → Prop) [DecidableRel valid] (weight : S → S → A)
    (n : ℕ) (s t : S) :
    (Matrix.of (fun a b => if valid a b then weight a b else 0) ^ n) s t =
      ∑ p ∈ Finset.univ.filter (fun p : Fin (n + 1) → S =>
        (p 0 = s ∧ p (Fin.last n) = t) ∧ ∀ i : Fin n, valid (p i.castSucc) (p i.succ)),
        ∏ i : Fin n, weight (p i.castSucc) (p i.succ) := by
  rw [Finset.sum_filter,
    matrix_pow_walk_ite (Matrix.of fun a b => if valid a b then weight a b else 0) n s t]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Matrix.of_apply, Fintype.prod_ite_zero]
  split_ifs <;> simp_all

theorem matrix_pow_sum_valid_walks {S A I : Type*} [Fintype S] [DecidableEq S]
    [CommSemiring A] (valid : S → S → Prop) [DecidableRel valid] (weight : S → S → A)
    (n : ℕ) (rs : Finset I) (start finish : I → S)
    (hinj : Function.Injective (fun r => (start r, finish r))) :
    ∑ r ∈ rs, (Matrix.of (fun a b => if valid a b then weight a b else 0) ^ n)
      (start r) (finish r) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin (n + 1) → S =>
        (∃ r ∈ rs, p 0 = start r ∧ p (Fin.last n) = finish r) ∧
          ∀ i : Fin n, valid (p i.castSucc) (p i.succ)),
        ∏ i : Fin n, weight (p i.castSucc) (p i.succ) := by
  classical
  simp_rw [matrix_pow_valid_walks valid weight, Finset.sum_filter]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : ∃ r ∈ rs, p 0 = start r ∧ p (Fin.last n) = finish r
  · obtain ⟨r, hr, hstart, hfinish⟩ := h
    rw [Finset.sum_eq_single_of_mem r hr]
    · have he : ∃ r' ∈ rs, p 0 = start r' ∧ p (Fin.last n) = finish r' :=
        ⟨r, hr, hstart, hfinish⟩
      simp only [he, true_and]
      simp [hstart, hfinish]
    · intro r' _ hne
      have hb : ¬ (p 0 = start r' ∧ p (Fin.last n) = finish r') := by
        rintro ⟨hstart', hfinish'⟩
        exact hne (hinj (Prod.ext (hstart'.symm.trans hstart) (hfinish'.symm.trans hfinish)))
      simp [hb]
  · simp only [h, false_and, ite_false]
    apply Finset.sum_eq_zero
    intro r hr
    rw [ite_eq_right (fun h' => h ⟨r, hr, h'.1⟩)]


noncomputable section Geometry
open Classical

abbrev GeoRel (q : ℕ) := Finset (Fin q × Fin q)

def geoMul {q : ℕ} (a b : GeoRel q) : GeoRel q :=
  Finset.univ.filter fun e => ∃ k : Fin q, (e.1, k) ∈ a ∧ (k, e.2) ∈ b

def geoOne {q : ℕ} : GeoRel q := Finset.univ.filter fun e => e.1 = e.2

@[local simp] theorem geoMemMul {q : ℕ} {a b : GeoRel q} {x y : Fin q} :
    (x, y) ∈ geoMul a b ↔ ∃ k : Fin q, (x, k) ∈ a ∧ (k, y) ∈ b := by
  simp [geoMul]

@[local simp] theorem geoMemOne {q : ℕ} {x y : Fin q} : (x, y) ∈ (geoOne : GeoRel q) ↔ x = y := by
  simp [geoOne]

theorem geoMul_one_left {q : ℕ} (a : GeoRel q) : geoMul geoOne a = a := by
  ext ⟨x, y⟩
  simp

theorem geoMul_one_right {q : ℕ} (a : GeoRel q) : geoMul a geoOne = a := by
  ext ⟨x, y⟩
  simp

theorem geoMul_assoc {q : ℕ} (a b c : GeoRel q) :
    geoMul (geoMul a b) c = geoMul a (geoMul b c) := by
  ext ⟨x, y⟩
  simp only [geoMemMul]
  constructor
  · rintro ⟨k, ⟨l, hl, hlk⟩, hk⟩
    exact ⟨l, hl, k, hlk, hk⟩
  · rintro ⟨l, hl, k, hlk, hk⟩
    exact ⟨k, ⟨l, hl, hlk⟩, hk⟩

def geoPath {n q : ℕ} (A : Fin n → GeoRel q) (lo hi : Fin (n + 1)) (a b : Fin q) : Prop :=
  ∃ x : Fin (n + 1) → Fin q, x lo = a ∧ x hi = b ∧
    ∀ j : Fin n, lo.val ≤ j.val → j.val < hi.val → (x j.castSucc, x j.succ) ∈ A j

theorem geoPath_refl {n q : ℕ} (A : Fin n → GeoRel q) (p : Fin (n + 1)) (a b : Fin q) :
    geoPath A p p a b ↔ a = b := by
  constructor
  · rintro ⟨x, ha, hb, _⟩
    exact ha.symm.trans hb
  · rintro rfl
    exact ⟨fun _ => a, rfl, rfl, fun _ h₁ h₂ => (Nat.not_lt_of_ge h₁ h₂).elim⟩

theorem geoPath_step {n q : ℕ} (A : Fin n → GeoRel q) (i : Fin n) (a b : Fin q) :
    geoPath A i.castSucc i.succ a b ↔ (a,b) ∈ A i := by
  constructor
  · rintro ⟨x, ha, hb, hx⟩
    simpa only [ha, hb] using hx i (Nat.le_refl _) (Nat.lt_succ_self _)
  · intro h
    have hne : i.succ ≠ i.castSucc := by
      intro he
      have hv := congrArg Fin.val he
      change i.val + 1 = i.val at hv
      omega
    refine ⟨fun j => if j = i.castSucc then a else b, ite_eq_left rfl, ite_eq_right hne, ?_⟩
    intro j hj₁ hj₂
    have he : j = i := Fin.ext (by
      change i.val ≤ j.val at hj₁
      change j.val < i.val + 1 at hj₂
      omega)
    subst j
    dsimp only
    rwa [ite_eq_left (show i.castSucc = i.castSucc from rfl), ite_eq_right hne]

theorem geoPath_split {n q : ℕ} (A : Fin n → GeoRel q) {lo mid hi : Fin (n + 1)}
    (hlm : lo.val ≤ mid.val) (hmh : mid.val ≤ hi.val) (a b : Fin q) :
    geoPath A lo hi a b ↔ ∃ c : Fin q, geoPath A lo mid a c ∧ geoPath A mid hi c b := by
  constructor
  · rintro ⟨x, ha, hb, hx⟩
    exact ⟨x mid,
      ⟨x, ha, rfl, fun j hj₁ hj₂ => hx j hj₁ (lt_of_lt_of_le hj₂ hmh)⟩,
      ⟨x, rfl, hb, fun j hj₁ hj₂ => hx j (le_trans hlm hj₁) hj₂⟩⟩
  · rintro ⟨c, ⟨x, ha, hxc, hx⟩, ⟨y, hyc, hb, hy⟩⟩
    let z : Fin (n + 1) → Fin q := fun j => if j.val ≤ mid.val then x j else y j
    have hzlo : z lo = a := (ite_eq_left hlm).trans ha
    have hzhi : z hi = b := by
      by_cases h : hi.val ≤ mid.val
      · have he : hi = mid := Fin.ext (le_antisymm h hmh)
        subst hi
        exact (ite_eq_left h).trans (hxc.trans (hyc.symm.trans hb))
      · exact (ite_eq_right h).trans hb
    refine ⟨z, hzlo, hzhi, ?_⟩
    intro j hj₁ hj₂
    by_cases h : j.val < mid.val
    · have hcast : z j.castSucc = x j.castSucc := ite_eq_left (Nat.le_of_lt h)
      have hsucc : z j.succ = x j.succ := ite_eq_left h
      rw [hcast, hsucc]
      exact hx j hj₁ h
    · have hh : mid.val ≤ j.val := Nat.le_of_not_gt h
      have hs : ¬ j.succ.val ≤ mid.val := by change ¬ j.val + 1 ≤ mid.val; omega
      have hcast : z j.castSucc = y j.castSucc := by
        by_cases hj : j.castSucc.val ≤ mid.val
        · have he : j.castSucc = mid := Fin.ext (le_antisymm hj hh)
          calc
            z j.castSucc = x j.castSucc := ite_eq_left hj
            _ = y j.castSucc := by rw [he, hxc, hyc]
        · exact ite_eq_right hj
      have hsucc : z j.succ = y j.succ := ite_eq_right hs
      rw [hcast, hsucc]
      exact hy j hh hj₂

theorem geoPath_congr {n q : ℕ} {A B : Fin n → GeoRel q} {lo hi : Fin (n + 1)}
    {a b : Fin q} (h : ∀ j : Fin n, lo.val ≤ j.val → j.val < hi.val → A j = B j) :
    geoPath A lo hi a b ↔ geoPath B lo hi a b := by
  constructor
  · rintro ⟨x, ha, hb, hx⟩
    exact ⟨x, ha, hb, fun j hj₁ hj₂ => h j hj₁ hj₂ ▸ hx j hj₁ hj₂⟩
  · rintro ⟨x, ha, hb, hx⟩
    exact ⟨x, ha, hb, fun j hj₁ hj₂ => (h j hj₁ hj₂).symm ▸ hx j hj₁ hj₂⟩

def geoPrefix {n q : ℕ} (A : Fin n → GeoRel q) (j : Fin (n + 1)) : GeoRel q :=
  Finset.univ.filter fun e => geoPath A 0 j e.1 e.2

def geoSuffix {n q : ℕ} (A : Fin n → GeoRel q) (j : Fin (n + 1)) : GeoRel q :=
  Finset.univ.filter fun e => geoPath A j (Fin.last n) e.1 e.2

@[local simp] theorem geoMemPrefix {n q : ℕ} {A : Fin n → GeoRel q} {j : Fin (n + 1)} {a b : Fin q} :
    (a,b) ∈ geoPrefix A j ↔ geoPath A 0 j a b := by simp [geoPrefix]

@[local simp] theorem geoMemSuffix {n q : ℕ} {A : Fin n → GeoRel q} {j : Fin (n + 1)} {a b : Fin q} :
    (a,b) ∈ geoSuffix A j ↔ geoPath A j (Fin.last n) a b := by simp [geoSuffix]

theorem geoPrefix_zero {n q : ℕ} (A : Fin n → GeoRel q) : geoPrefix A 0 = geoOne := by
  ext ⟨a,b⟩
  simp [geoPath_refl]

theorem geoSuffix_last {n q : ℕ} (A : Fin n → GeoRel q) : geoSuffix A (Fin.last n) = geoOne := by
  ext ⟨a,b⟩
  simp [geoPath_refl]

theorem geoPrefix_step {n q : ℕ} (A : Fin n → GeoRel q) (i : Fin n) :
    geoPrefix A i.succ = geoMul (geoPrefix A i.castSucc) (A i) := by
  ext ⟨a,b⟩
  simp only [geoMemPrefix, geoMemMul, ← geoPath_step A i]
  exact geoPath_split A (Nat.zero_le _) (Nat.le_succ _) a b

theorem geoSuffix_step {n q : ℕ} (A : Fin n → GeoRel q) (i : Fin n) :
    geoSuffix A i.castSucc = geoMul (A i) (geoSuffix A i.succ) := by
  ext ⟨a,b⟩
  simp only [geoMemSuffix, geoMemMul, ← geoPath_step A i]
  exact geoPath_split A (Nat.le_succ _) (Nat.succ_le_of_lt i.isLt) a b

theorem geoPrefix_unique {n q : ℕ} (A : Fin n → GeoRel q) (P : Fin (n+1) → GeoRel q)
    (h0 : P 0 = geoOne) (hs : ∀ i : Fin n, P i.succ = geoMul (P i.castSucc) (A i)) :
    P = geoPrefix A := by
  funext j
  induction j using Fin.induction with
  | zero => rw [h0, geoPrefix_zero]
  | succ i ih => rw [hs, geoPrefix_step, ih]

theorem geoSuffix_unique {n q : ℕ} (A : Fin n → GeoRel q) (S : Fin (n+1) → GeoRel q)
    (hn : S (Fin.last n) = geoOne)
    (hs : ∀ i : Fin n, S i.castSucc = geoMul (A i) (S i.succ)) : S = geoSuffix A := by
  funext j
  induction j using Fin.reverseInduction with
  | last => rw [hn, geoSuffix_last]
  | cast i ih => rw [hs, geoSuffix_step, ih]

theorem geoPrefix_suffix {n q : ℕ} (A : Fin n → GeoRel q) :
    geoPrefix A (Fin.last n) = geoSuffix A 0 := by
  ext ⟨a,b⟩
  simp only [geoMemPrefix, geoMemSuffix]

def geoClosed {n q : ℕ} (hn : 0 < n) (A : Fin n → GeoRel q) : Prop :=
  ∃ x : Fin n → Fin q, ∀ i : Fin n, (x i, x ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) ∈ A i

theorem geoClosed_iff_trace {n q : ℕ} (hn : 0 < n) (A : Fin n → GeoRel q) :
    geoClosed hn A ↔ ∃ a : Fin q, (a,a) ∈ geoPrefix A (Fin.last n) := by
  simp only [geoClosed, geoMemPrefix, geoPath]
  let z : Fin n := ⟨0, hn⟩
  constructor
  · rintro ⟨x,hx⟩
    let y : Fin (n+1) → Fin q := fun j => if h : j.val < n then x ⟨j.val,h⟩ else x z
    have h0 : y 0 = x z := by simp [y, z, hn]
    have hl : y (Fin.last n) = x z := by simp [y]
    refine ⟨x z, y, h0, hl, fun i _ _ => ?_⟩
    have hc : y i.castSucc = x i := by simp [y, i.isLt]
    have hs : y i.succ = x ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ := by
      by_cases h : i.val + 1 < n
      · simp [y, h, Nat.mod_eq_of_lt h]
      · have he : i.val + 1 = n := by have := i.isLt; omega
        simp [y, z, he]
    simpa only [hc, hs] using hx i
  · rintro ⟨a,y,h0,hl,hy⟩
    refine ⟨fun i => y i.castSucc, fun i => ?_⟩
    have hs : y (Fin.castSucc ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) = y i.succ := by
      by_cases h : i.val + 1 < n
      · congr 1
        exact Fin.ext (Nat.mod_eq_of_lt h)
      · have he : i.val + 1 = n := by have := i.isLt; omega
        have hz : Fin.castSucc (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = 0 :=
          Fin.ext (by simp [he])
        have ht : i.succ = Fin.last n := Fin.ext he
        rw [hz, ht, h0, hl]
    simpa only [hs] using hy i (Nat.zero_le _) i.isLt

theorem geoNotClosed_iff_trace_zero {n q : ℕ} (hn : 0 < n) (A : Fin n → GeoRel q) :
    ¬ geoClosed hn A ↔ ∀ a : Fin q, (a,a) ∉ geoPrefix A (Fin.last n) := by
  rw [geoClosed_iff_trace, not_exists]

theorem geoClosed_iff_cut {n q : ℕ} (hn : 0 < n) (A : Fin n → GeoRel q) (i : Fin n) :
    geoClosed hn A ↔ ∃ u v : Fin q, (u,v) ∈ A i ∧
      (v,u) ∈ geoMul (geoSuffix A i.succ) (geoPrefix A i.castSucc) := by
  rw [geoClosed_iff_trace]
  simp only [geoMemPrefix, geoMemMul, geoMemSuffix]
  constructor
  · rintro ⟨a,h⟩
    obtain ⟨u, hu, h⟩ := (geoPath_split A (lo := 0) (mid := i.castSucc) (hi := Fin.last n)
      (Nat.zero_le _) (Nat.le_of_lt i.isLt) a a).mp h
    obtain ⟨v, hv, hv'⟩ := (geoPath_split A (lo := i.castSucc) (mid := i.succ)
      (hi := Fin.last n) (Nat.le_succ _) (Nat.succ_le_of_lt i.isLt) u a).mp h
    exact ⟨u,v,(geoPath_step A i u v).mp hv,a,hv',hu⟩
  · rintro ⟨u,v,huv,a,hv,hu⟩
    refine ⟨a,(geoPath_split A (lo := 0) (mid := i.castSucc) (hi := Fin.last n)
      (Nat.zero_le _) (Nat.le_of_lt i.isLt) a a).mpr ⟨u,hu,?_⟩⟩
    exact (geoPath_split A (lo := i.castSucc) (mid := i.succ) (hi := Fin.last n)
      (Nat.le_succ _) (Nat.succ_le_of_lt i.isLt) u a).mpr ⟨v,(geoPath_step A i u v).mpr huv,hv⟩

theorem geoPrefix_update {n q : ℕ} (A : Fin n → GeoRel q) (i : Fin n) (B : GeoRel q) :
    geoPrefix (Function.update A i B) i.castSucc = geoPrefix A i.castSucc := by
  ext ⟨a,b⟩
  simp only [geoMemPrefix]
  apply geoPath_congr
  intro j _ hj
  rw [Function.update_of_ne]
  intro h
  subst j
  exact Nat.lt_irrefl _ hj

theorem geoSuffix_update {n q : ℕ} (A : Fin n → GeoRel q) (i : Fin n) (B : GeoRel q) :
    geoSuffix (Function.update A i B) i.succ = geoSuffix A i.succ := by
  ext ⟨a,b⟩
  simp only [geoMemSuffix]
  apply geoPath_congr
  intro j hj _
  rw [Function.update_of_ne]
  intro h
  subst j
  exact Nat.not_succ_le_self _ hj

theorem geoClosed_insert_iff {n q : ℕ} {hn : 0 < n} {A : Fin n → GeoRel q}
    (hA : ¬ geoClosed hn A) (i : Fin n) (e : Fin q × Fin q) :
    geoClosed hn (Function.update A i (insert e (A i))) ↔
      (e.2,e.1) ∈ geoMul (geoSuffix A i.succ) (geoPrefix A i.castSucc) := by
  rw [geoClosed_iff_cut hn _ i, Function.update_self, geoSuffix_update, geoPrefix_update]
  constructor
  · rintro ⟨u,v,huv,hm⟩
    obtain hh | hh := Finset.mem_insert.mp huv
    · rw [← hh]
      exact hm
    · exact (hA ((geoClosed_iff_cut hn A i).mpr ⟨u,v,hh,hm⟩)).elim
  · intro hm
    exact ⟨e.1,e.2,Finset.mem_insert_self _ _,hm⟩

def geoAllowed {q : ℕ} (p s : GeoRel q) : GeoRel q :=
  Finset.univ.filter fun edge => (edge.2,edge.1) ∉ geoMul s p

theorem geoAllowed_iff {n q : ℕ} {hn : 0 < n} {A : Fin n → GeoRel q}
    (hA : ¬ geoClosed hn A) (i : Fin n) (e : Fin q × Fin q) :
    e ∈ geoAllowed (geoPrefix A i.castSucc) (geoSuffix A i.succ) ↔
      ¬ geoClosed hn (Function.update A i (insert e (A i))) := by
  simp only [geoAllowed, Finset.mem_filter, Finset.mem_univ, true_and, geoClosed_insert_iff hA]

theorem geoAllowed_eq_iff {n q : ℕ} {hn : 0 < n} {A : Fin n → GeoRel q}
    (hA : ¬ geoClosed hn A) (i : Fin n) :
    A i = geoAllowed (geoPrefix A i.castSucc) (geoSuffix A i.succ) ↔
      ∀ e : Fin q × Fin q, e ∉ A i → geoClosed hn (Function.update A i (insert e (A i))) := by
  constructor
  · intro h e he
    by_contra hc
    rw [h] at he
    exact he ((geoAllowed_iff hA i e).mpr hc)
  · intro h
    ext e
    rw [geoAllowed_iff hA]
    constructor
    · intro he
      rwa [Finset.insert_eq_of_mem he, Function.update_eq_self]
    · intro he
      by_contra he'
      exact he (h e he')

end Geometry

section Bridge
variable {q n : ℕ}

private abbrev State (q : ℕ) := GeoRel q × GeoRel q
private abbrev Walk (q n : ℕ) := Fin (n + 1) → State q
private abbrev Table (q n : ℕ) := Finset (Fin n × (Fin q × Fin q))

private def accept (hn : 0 < n) (T : Table q n) : Prop := geoClosed hn (rowOf T)

private theorem accept_mono (hn : 0 < n) : Monotone (accept (q := q) hn) := by
  intro T U hTU
  rintro ⟨x, hx⟩
  exact ⟨x, fun i => (mem_rowOf _ _ _).mpr (hTU ((mem_rowOf _ _ _).mp (hx i)))⟩

private theorem accept_iff (hn : 0 < n) (a : (Fin n × (Fin q × Fin q)) → Bool) :
    accept hn (tableOf a) ↔ ∃ x : Fin n → Fin q, ∀ i : Fin n,
      a (i, x i, x ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) = true := by
  simp only [accept, geoClosed, mem_rowOf, mem_tableOf]

private def diagFree (q : ℕ) : Finset (GeoRel q) :=
  Finset.univ.filter (fun rel => ∀ j : Fin q, (j,j) ∉ rel)

private def allowed (s t : State q) : GeoRel q := geoAllowed s.1 t.2
private abbrev valid (s t : State q) : Prop :=
  t.1 = geoMul s.1 (allowed s t) ∧ s.2 = geoMul (allowed s t) t.2
private noncomputable def weight (s t : State q) : Polynomial ℕ := Polynomial.X ^ (q*q - (allowed s t).card)
private noncomputable def spectrum (q n : ℕ) : Polynomial ℕ :=
  let M := Matrix.of (fun s t : State q => if valid s t then weight s t else 0)
  ∑ r ∈ diagFree q, (M ^ n) (geoOne, r) (r, geoOne)

private noncomputable def fromTable (T : Table q n) : Walk q n :=
  fun i => (geoPrefix (rowOf T) i, geoSuffix (rowOf T) i)
private def walkRows (p : Walk q n) (i : Fin n) : GeoRel q := allowed (p i.castSucc) (p i.succ)
private def toTable (p : Walk q n) : Table q n := flatten (walkRows p)

private def good (p : Walk q n) : Prop :=
  (∃ r ∈ diagFree q, p 0 = (geoOne,r) ∧ p (Fin.last n) = (r,geoOne)) ∧
    ∀ i : Fin n, valid (p i.castSucc) (p i.succ)

private theorem maxReject_iff (hn : 0 < n) (T : Table q n) :
    MaxReject (accept hn) T ↔
      ¬ geoClosed hn (rowOf T) ∧
      ∀ i : Fin n, rowOf T i = walkRows (fromTable T) i := by
  constructor
  · rintro ⟨hnc, hr⟩
    refine ⟨hnc, fun i => (geoAllowed_eq_iff hnc i).mpr ?_⟩
    intro e he
    have hh := hr (i,e) (fun h => he ((mem_rowOf _ _ _).mpr h))
    simpa only [accept, rowOf_insert] using hh
  · rintro ⟨hnc, hr⟩
    refine ⟨hnc, ?_⟩
    rintro ⟨i, e⟩ he
    have hh := (geoAllowed_eq_iff hnc i).mp (hr i) e (fun h => he ((mem_rowOf _ _ _).mp h))
    simpa only [accept, rowOf_insert] using hh

private theorem fromTable_good (hn : 0 < n) {T : Table q n} (hT : MaxReject (accept hn) T) :
    good (fromTable T) := by
  obtain ⟨hno, hrows⟩ := (maxReject_iff hn T).mp hT
  let A := rowOf T
  refine ⟨⟨geoPrefix A (Fin.last n), ?_, ?_, ?_⟩, ?_⟩
  · simpa [diagFree] using (geoNotClosed_iff_trace_zero hn A).mp hno
  · exact Prod.ext (geoPrefix_zero A) (geoPrefix_suffix A).symm
  · exact Prod.ext rfl (geoSuffix_last A)
  · intro i
    change geoPrefix A i.succ = geoMul (geoPrefix A i.castSucc) (walkRows (fromTable T) i) ∧
      geoSuffix A i.castSucc = geoMul (walkRows (fromTable T) i) (geoSuffix A i.succ)
    rw [← hrows i]
    exact ⟨geoPrefix_step A i, geoSuffix_step A i⟩

private theorem toTable_fromTable (hn : 0 < n) {T : Table q n} (hT : MaxReject (accept hn) T) :
    toTable (fromTable T) = T := by
  have hh := funext ((maxReject_iff hn T).mp hT).2
  rw [toTable, ← hh, flatten_rowOf]

private theorem fromTable_toTable {p : Walk q n} (hp : good p) : fromTable (toTable p) = p := by
  obtain ⟨⟨r, _, h0, hl⟩, hs⟩ := hp
  let A := walkRows p
  have hP := geoPrefix_unique A (fun i => (p i).1) (congrArg Prod.fst h0) (fun i => (hs i).1)
  have hS := geoSuffix_unique A (fun i => (p i).2) (congrArg Prod.snd hl) (fun i => (hs i).2)
  funext i
  simp only [fromTable, toTable, rowOf_flatten]
  exact Prod.ext (congrFun hP i).symm (congrFun hS i).symm

private theorem toTable_reject (hn : 0 < n) {p : Walk q n} (hp : good p) :
    MaxReject (accept hn) (toTable p) := by
  have hrt := fromTable_toTable hp
  obtain ⟨⟨r, hr, _, hl⟩, _⟩ := hp
  refine (maxReject_iff hn _).mpr ⟨?_, ?_⟩
  · apply (geoNotClosed_iff_trace_zero hn _).mpr
    have hP : geoPrefix (rowOf (toTable p)) (Fin.last n) = r :=
      congrArg Prod.fst ((congrFun hrt _).trans hl)
    simpa [hP, diagFree] using hr
  · intro i
    rw [hrt]
    simp only [toTable, rowOf_flatten]

private theorem walk_weight (p : Walk q n) :
    (∏ i : Fin n, weight (p i.castSucc) (p i.succ)) =
      Polynomial.X ^ (missing (toTable p)).card := by
  rw [toTable, missing_card_flatten]
  exact Finset.prod_pow_eq_pow_sum _ _ _

private theorem spectrum_eq (q n : ℕ) (hn : 0 < n) :
    spectrum q n = ∑ T ∈ rejects (accept (q := q) hn), Polynomial.X ^ (missing T).card := by
  classical
  rw [spectrum, matrix_pow_sum_valid_walks valid weight n (diagFree q)
    (fun r => (geoOne, r)) (fun r => (r, geoOne)) (fun _ _ h => congrArg (fun st => st.1.2) h)]
  apply Finset.sum_bij (fun p _ => toTable p)
  · intro p hp
    exact (mem_rejects _ _).mpr (toTable_reject hn (Finset.mem_filter.mp hp).2)
  · intro p hp p' hp' he
    exact (fromTable_toTable (Finset.mem_filter.mp hp).2).symm.trans
      ((congrArg fromTable he).trans (fromTable_toTable (Finset.mem_filter.mp hp').2))
  · intro T hT
    have hmr := (mem_rejects _ _).mp hT
    exact ⟨fromTable T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fromTable_good hn hmr⟩,
      toTable_fromTable hn hmr⟩
  · intro p _
    exact walk_weight p

private theorem spectrum_coeff (q n : ℕ) (hn : 0 < n) (k : ℕ) :
    (spectrum q n).coeff k = ((canon (accept (q := q) hn)).filter (fun C => C.card = k)).card := by
  rw [spectrum_eq q n hn, canon_width, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro T _
  rw [Polynomial.coeff_X_pow]
  by_cases h : (missing T).card = k
  · simp [h]
  · simp [h, Ne.symm h]

end Bridge
end PEqualNP.Outside.L_pcx_238_aux

open PEqualNP.Outside.L_pcx_238_aux
theorem PEqualNP.Outside.L_pcx_238 :
∀ (q : ℕ), 0 < q →
  let E := Fin q × Fin q
  let R := Finset E
  let mul := fun (a b : R) => Finset.univ.filter (fun e : E =>
    ∃ k : Fin q, (e.1, k) ∈ a ∧ (k, e.2) ∈ b)
  let one := Finset.univ.filter (fun d : E => d.1 = d.2)
  let M : Matrix (R × R) (R × R) (Polynomial ℕ) := fun s t =>
    let allowed := Finset.univ.filter (fun edge : E => (edge.2, edge.1) ∉ mul t.2 s.1)
    if t.1 = mul s.1 allowed ∧ s.2 = mul allowed t.2 then
      Polynomial.X ^ (q * q - allowed.card) else 0
  ∀ (n : ℕ) (hn : 0 < n),
    let V := Fin n × E
    let closed := fun (a : V → Bool) => ∃ x : Fin n → Fin q, ∀ i : Fin n,
      a (i, x i, x ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) = true
    let enc := fun F : Finset (PEqualNP.ProofComplexity.Clause V) =>
      ∀ a : V → Bool, closed a ↔ PEqualNP.ProofComplexity.Satisfies a (↑F : Set _)
    let spectrum : Polynomial ℕ := ∑ r ∈ Finset.univ.filter
      (fun rel : R => ∀ j : Fin q, (j, j) ∉ rel), (M ^ n) (one, r) (r, one)
    ∃ F : Finset (PEqualNP.ProofComplexity.Clause V),
      enc F ∧ (∀ C ∈ F, ∀ l ∈ C, l.2 = true) ∧
      (∀ k : ℕ, (F.filter (fun C => C.card = k)).card = spectrum.coeff k) ∧
      ∀ G : Finset (PEqualNP.ProofComplexity.Clause V), enc G →
        (∀ C ∈ F, ∃ B ∈ G, B.filter (fun l => l.2 = true) = C) ∧
        ∀ k : ℕ, (F.filter (fun C => k ≤ C.card)).card ≤
          (G.filter (fun B => k ≤ B.card)).card := by
  classical
  intro q _
  dsimp only
  intro n hn
  have he (a : (Fin n × (Fin q × Fin q)) → Bool) := accept_iff hn a
  refine ⟨canon (accept (q := q) hn), ?_, canon_pos _, ?_, ?_⟩
  · intro a
    exact (he a).symm.trans (canon_enc _ (accept_mono hn) a)
  · intro k
    exact (spectrum_coeff q n hn k).symm
  · intro G hG
    have hf := canon_forced (accept (q := q) hn) G (fun a => (he a).trans (hG a))
    exact ⟨hf, canon_bound _ _ hf⟩
