import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_1411
def Ideal {n : Nat} (R : Fin n → Fin n → Prop) (A : Finset (Fin n)) : Prop :=
  ∀ i j, j ∈ A → R i j → i ∈ A
def Mono {n r : Nat} (R : Fin n → Fin n → Prop) (E : Finset (Fin n) → Finset (Fin r)) : Prop :=
  ∀ A B, Ideal R A → Ideal R B → A ⊆ B → E A ⊆ E B
def Recovers {n r : Nat} (R : Fin n → Fin n → Prop) (a f : Nat)
    (E : Finset (Fin n) → Finset (Fin r)) : Prop :=
  ∃ D : Finset (Fin r) → Finset (Fin n), (∀ X Y, X ⊆ Y → D X ⊆ D Y) ∧
    ∀ A, Ideal R A → ∀ Y, (E A \ Y).card ≤ a → (Y \ E A).card ≤ f → D Y = A
def Wit {n r : Nat} (R : Fin n → Fin n → Prop) (a f : Nat)
    (E : Finset (Fin n) → Finset (Fin r)) : Prop :=
  ∃ C : Fin n → Finset (Fin r),
    (∀ i, a+f+1 ≤ (C i).card) ∧ (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
    ∀ i v, v ∈ C i → ∀ A, Ideal R A → (v ∈ E A ↔ i ∈ A)
def cc_blk (n r t : Nat) (i : Fin n) : Finset (Fin r) :=
  Finset.univ.filter (fun v : Fin r => i.val * t ≤ v.val ∧ v.val < i.val * t + t)
theorem cc_mem_blk {n r t : Nat} {i : Fin n} {v : Fin r} :
    v ∈ cc_blk n r t i ↔ i.val * t ≤ v.val ∧ v.val < i.val * t + t := by
  unfold cc_blk
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
theorem cc_eq_of_block {t i j v : Nat} (h1 : i * t ≤ v) (h2 : v < i * t + t)
    (h3 : j * t ≤ v) (h4 : v < j * t + t) : i = j := by
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exfalso
    have h5 : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right t (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h5
    omega
  · exact hij
  · exfalso
    have h5 : (j + 1) * t ≤ i * t := Nat.mul_le_mul_right t (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h5
    omega
theorem cc_card_blk {n r t : Nat} (h : n * t ≤ r) (i : Fin n) :
    t ≤ (cc_blk n r t i).card := by
  have hi : i.val * t + t ≤ r := by
    have h1 : (i.val + 1) * t ≤ n * t := Nat.mul_le_mul_right t (by have := i.isLt; omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  let g : Fin t → Fin r := fun k => ⟨i.val * t + k.val, by have := k.isLt; omega⟩
  have hg : Function.Injective g := by
    intro x y hxy
    have hv : (g x).val = (g y).val := congrArg Fin.val hxy
    have hv2 : i.val * t + x.val = i.val * t + y.val := hv
    exact Fin.ext (by omega)
  calc t = (Finset.univ.image g).card := by
        rw [Finset.card_image_of_injective _ hg]
        simp
    _ ≤ (cc_blk n r t i).card := by
        apply Finset.card_le_card
        intro v hv
        rw [Finset.mem_image] at hv
        obtain ⟨k, _, rfl⟩ := hv
        rw [cc_mem_blk]
        have hk := k.isLt
        have hgk : (g k).val = i.val * t + k.val := rfl
        rw [hgk]
        omega
theorem bwd {n r : Nat} (a f : Nat) (R : Fin n → Fin n → Prop)
    (E : Finset (Fin n) → Finset (Fin r)) (hw : Wit R a f E) : Recovers R a f E := by
  obtain ⟨C, hcard, hdisj, hagree⟩ := hw
  refine ⟨fun Y => Finset.univ.filter (fun i => f + 1 ≤ (C i ∩ Y).card), ?_, ?_⟩
  · intro X Y hXY i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, le_trans hi.2 (Finset.card_le_card (Finset.inter_subset_inter_left hXY))⟩
  · intro A hA Y ha hf
    ext i
    rw [Finset.mem_filter]
    constructor
    · intro hi
      by_contra hiA
      have hsub : C i ∩ Y ⊆ Y \ E A := by
        intro v hv
        rw [Finset.mem_inter] at hv
        rw [Finset.mem_sdiff]
        refine ⟨hv.2, ?_⟩
        intro hvE
        exact hiA ((hagree i v hv.1 A hA).1 hvE)
      have h1 := Finset.card_le_card hsub
      have h2 := hi.2
      omega
    · intro hiA
      refine ⟨Finset.mem_univ _, ?_⟩
      have hsub : C i \ Y ⊆ E A \ Y := by
        intro v hv
        rw [Finset.mem_sdiff] at hv ⊢
        exact ⟨(hagree i v hv.1 A hA).2 hiA, hv.2⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_inter_add_card_sdiff (C i) Y
      have h3 := hcard i
      omega
theorem cnt {n r : Nat} (a f : Nat) (R : Fin n → Fin n → Prop)
    (E : Finset (Fin n) → Finset (Fin r)) (hw : Wit R a f E) : n*(a+f+1) ≤ r := by
  obtain ⟨C, hcard, hdisj, -⟩ := hw
  have hpd : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint C := by
    intro i _ j _ hij
    exact hdisj i j hij
  calc n * (a+f+1) = ∑ _i : Fin n, (a+f+1) := by simp
    _ ≤ ∑ i, (C i).card := Finset.sum_le_sum (fun i _ => hcard i)
    _ = (Finset.univ.biUnion C).card := (Finset.card_biUnion hpd).symm
    _ ≤ Fintype.card (Fin r) := Finset.card_le_univ _
    _ = r := Fintype.card_fin r
theorem cons {n r : Nat} (a f : Nat) (R : Fin n → Fin n → Prop) (h : n*(a+f+1) ≤ r) :
    ∃ E : Finset (Fin n) → Finset (Fin r), Mono R E ∧ Wit R a f E := by
  refine ⟨fun A => A.biUnion (cc_blk n r (a+f+1)), ?_, cc_blk n r (a+f+1), ?_, ?_, ?_⟩
  · intro A B _ _ hAB
    exact Finset.biUnion_subset_biUnion_of_subset_left _ hAB
  · intro i
    exact cc_card_blk h i
  · intro i j hij
    rw [Finset.disjoint_left]
    intro v hvi hvj
    rw [cc_mem_blk] at hvi hvj
    exact hij (Fin.ext (cc_eq_of_block hvi.1 hvi.2 hvj.1 hvj.2))
  · intro i v hv A _
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨k, hk, hvk⟩
      rw [cc_mem_blk] at hv hvk
      have hki : k = i := Fin.ext (cc_eq_of_block hvk.1 hvk.2 hv.1 hv.2)
      rw [← hki]
      exact hk
    · intro hi
      exact ⟨i, hi, hv⟩
theorem fw_split {r : Nat} (C : Finset (Fin r)) (a f : Nat) (h : C.card ≤ a + f) :
    ∃ S, S ⊆ C ∧ S.card ≤ a ∧ (C \ S).card ≤ f := by
  obtain ⟨S, hS, hc⟩ := Finset.exists_subset_card_eq (min_le_right a C.card)
  refine ⟨S, hS, ?_, ?_⟩
  · rw [hc]
    exact min_le_left _ _
  · rw [Finset.card_sdiff_of_subset hS, hc]
    rcases le_total a C.card with h1 | h1
    · rw [min_eq_left h1]
      omega
    · rw [min_eq_right h1]
      omega
theorem fw_le {r : Nat} (X Y Z : Finset (Fin r)) (m : Nat) (hZ : Z.card ≤ m)
    (h : ∀ x, x ∈ X → x ∉ Y → x ∈ Z) : (X \ Y).card ≤ m := by
  refine le_trans (Finset.card_le_card ?_) hZ
  intro x hx
  rw [Finset.mem_sdiff] at hx
  exact h x hx.1 hx.2
theorem fw_idealL {n : Nat} (R : Fin n → Fin n → Prop)
    (htrans : ∀ i j k, R i j → R j k → R i k) (i : Fin n) (L : Finset (Fin n))
    (hL : ∀ k, k ∈ L ↔ R k i) : Ideal R L := by
  intro x y hy hxy
  rw [hL] at hy ⊢
  exact htrans x y i hxy hy
theorem fw_idealU {n : Nat} (R : Fin n → Fin n → Prop)
    (htrans : ∀ i j k, R i j → R j k → R i k) (i : Fin n) (U : Finset (Fin n))
    (hU : ∀ k, k ∈ U ↔ ¬ R i k) : Ideal R U := by
  intro x y hy hxy
  rw [hU] at hy ⊢
  exact fun hix => hy (htrans i x y hix hxy)
theorem fw_agree {n r : Nat} (R : Fin n → Fin n → Prop)
    (E : Finset (Fin n) → Finset (Fin r)) (hE : Mono R E) (i : Fin n)
    (L U : Finset (Fin n)) (hLi : Ideal R L) (hUi : Ideal R U)
    (hL : ∀ k, k ∈ L ↔ R k i) (hU : ∀ k, k ∈ U ↔ ¬ R i k)
    (v : Fin r) (hv : v ∈ E L \ E U) (A : Finset (Fin n)) (hA : Ideal R A) :
    v ∈ E A ↔ i ∈ A := by
  rw [Finset.mem_sdiff] at hv
  constructor
  · intro hvA
    by_contra hiA
    have hsub : A ⊆ U := by
      intro k hk
      rw [hU]
      intro hik
      exact hiA (hA i k hk hik)
    exact hv.2 (hE A U hA hUi hsub hvA)
  · intro hiA
    have hsub : L ⊆ A := by
      intro k hk
      rw [hL] at hk
      exact hA k i hiA hk
    exact hE L A hLi hA hsub hv.1
theorem fw_card {n r : Nat} (a f : Nat) (R : Fin n → Fin n → Prop)
    (hrefl : ∀ i, R i i)
    (E : Finset (Fin n) → Finset (Fin r)) (hrec : Recovers R a f E) (i : Fin n)
    (L U : Finset (Fin n)) (hLi : Ideal R L) (hUi : Ideal R U)
    (hL : ∀ k, k ∈ L ↔ R k i) (hU : ∀ k, k ∈ U ↔ ¬ R i k) :
    a + f + 1 ≤ (E L \ E U).card := by
  obtain ⟨D, hDm, hD⟩ := hrec
  by_contra hlt
  have hle : (E L \ E U).card ≤ a + f := by omega
  obtain ⟨S, hS, hSa, hSf⟩ := fw_split (E L \ E U) a f hle
  have h1 : D (E L \ S) = L :=
    hD L hLi (E L \ S)
      (fw_le (E L) (E L \ S) S a hSa (fun x hx hx' => by
        by_contra hxS
        exact hx' (Finset.mem_sdiff.mpr ⟨hx, hxS⟩)))
      (fw_le (E L \ S) (E L) ∅ f (by simp) (fun x hx hx' =>
        absurd (Finset.mem_sdiff.mp hx).1 hx'))
  have h2 : D (E U ∪ ((E L \ E U) \ S)) = U :=
    hD U hUi (E U ∪ ((E L \ E U) \ S))
      (fw_le (E U) (E U ∪ ((E L \ E U) \ S)) ∅ a (by simp) (fun x hx hx' =>
        absurd (Finset.mem_union_left ((E L \ E U) \ S) hx) hx'))
      (fw_le (E U ∪ ((E L \ E U) \ S)) (E U) ((E L \ E U) \ S) f hSf (fun x hx hx' => by
        rcases Finset.mem_union.mp hx with h | h
        · exact absurd h hx'
        · exact h))
  have hsub : E L \ S ⊆ E U ∪ ((E L \ E U) \ S) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    by_cases hxU : x ∈ E U
    · exact Finset.mem_union_left _ hxU
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hx.1, hxU⟩, hx.2⟩)
  have hLU : L ⊆ U := by
    have h3 := hDm _ _ hsub
    rw [h1, h2] at h3
    exact h3
  have hiU : i ∈ U := hLU ((hL i).mpr (hrefl i))
  exact (hU i).mp hiU (hrefl i)
theorem fwd {n r : Nat} (a f : Nat) (R : Fin n → Fin n → Prop)
    (hrefl : ∀ i, R i i) (htrans : ∀ i j k, R i j → R j k → R i k)
    (hanti : ∀ i j, R i j → R j i → i = j)
    (E : Finset (Fin n) → Finset (Fin r)) (hE : Mono R E) (hrec : Recovers R a f E) :
    Wit R a f E := by
  have hLex : ∀ i : Fin n, ∃ L : Finset (Fin n), ∀ k, k ∈ L ↔ R k i := by
    intro i
    classical
    exact ⟨Finset.univ.filter (fun k => R k i), fun k => by simp⟩
  have hUex : ∀ i : Fin n, ∃ U : Finset (Fin n), ∀ k, k ∈ U ↔ ¬ R i k := by
    intro i
    classical
    exact ⟨Finset.univ.filter (fun k => ¬ R i k), fun k => by simp⟩
  choose L hL using hLex
  choose U hU using hUex
  have hLi : ∀ i, Ideal R (L i) := fun i => fw_idealL R htrans i (L i) (hL i)
  have hUi : ∀ i, Ideal R (U i) := fun i => fw_idealU R htrans i (U i) (hU i)
  refine ⟨fun i => E (L i) \ E (U i), ?_, ?_, ?_⟩
  · intro i
    exact fw_card a f R hrefl E hrec i (L i) (U i) (hLi i) (hUi i) (hL i) (hU i)
  · intro i j hij
    rw [Finset.disjoint_left]
    intro v hvi hvj
    have h1 := (fw_agree R E hE i (L i) (U i) (hLi i) (hUi i) (hL i) (hU i) v hvi
      (L j) (hLi j)).mp (Finset.mem_sdiff.mp hvj).1
    have h2 := (fw_agree R E hE j (L j) (U j) (hLi j) (hUi j) (hL j) (hU j) v hvj
      (L i) (hLi i)).mp (Finset.mem_sdiff.mp hvi).1
    exact hij (hanti i j ((hL j i).mp h1) ((hL i j).mp h2))
  · intro i v hv A hA
    exact fw_agree R E hE i (L i) (U i) (hLi i) (hUi i) (hL i) (hU i) v hv A hA
end PEqualNP.Outside.L_lib_1411
theorem PEqualNP.Outside.L_lib_1411 : ∀ (n r a f : Nat) (R : Fin n → Fin n → Prop),
  (∀ i, R i i) → (∀ i j k, R i j → R j k → R i k) → (∀ i j, R i j → R j i → i = j) →
  let ideal := fun (A : Finset (Fin n)) => ∀ i j, j ∈ A → R i j → i ∈ A
  let mono := fun (E : Finset (Fin n) → Finset (Fin r)) =>
    ∀ A B, ideal A → ideal B → A ⊆ B → E A ⊆ E B
  let recovers := fun (E : Finset (Fin n) → Finset (Fin r)) =>
    ∃ D : Finset (Fin r) → Finset (Fin n), (∀ X Y, X ⊆ Y → D X ⊆ D Y) ∧
      ∀ A, ideal A → ∀ Y, (E A \ Y).card ≤ a → (Y \ E A).card ≤ f → D Y = A
  let t := a+f+1
  (∀ E, mono E → (recovers E ↔ ∃ C : Fin n → Finset (Fin r),
    (∀ i, t ≤ (C i).card) ∧ (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
    ∀ i v, v ∈ C i → ∀ A, ideal A → (v ∈ E A ↔ i ∈ A))) ∧
  ((∃ E, mono E ∧ recovers E) ↔ n*t ≤ r) := by
  intro n r a f R hrefl htrans hanti ideal mono recovers t
  refine ⟨fun E hE => ⟨fun h => PEqualNP.Outside.L_lib_1411.fwd a f R hrefl htrans hanti E hE h,
      fun h => PEqualNP.Outside.L_lib_1411.bwd a f R E h⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨E, hE, hr⟩
    exact PEqualNP.Outside.L_lib_1411.cnt a f R E
      (PEqualNP.Outside.L_lib_1411.fwd a f R hrefl htrans hanti E hE hr)
  · intro h
    obtain ⟨E, hE, hw⟩ := PEqualNP.Outside.L_lib_1411.cons a f R h
    exact ⟨E, hE, PEqualNP.Outside.L_lib_1411.bwd a f R E hw⟩
