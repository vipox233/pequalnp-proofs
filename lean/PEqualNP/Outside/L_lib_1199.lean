import Mathlib

namespace PEqualNP.Outside.L_lib_1199.Core

open scoped BigOperators
open Finset

abbrev K := ZMod 2

noncomputable def bit (b : Bool) : K := if b then 1 else 0

lemma bit_inj : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> simp [bit] at h ⊢

lemma bit_xor (a b : Bool) : bit (xor a b) = bit a + bit b := by
  cases a <;> cases b <;> decide

lemma bit_surj : Function.Surjective bit := by
  intro k
  fin_cases k
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

lemma add_self (k : K) : k + k = 0 := by
  obtain ⟨b, rfl⟩ := bit_surj k
  cases b <;> decide

variable {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

noncomputable def v (F : Finset α) (e : α) : K := if e ∈ F then 1 else 0

noncomputable def edges (l r : α → V) (A : Finset V) : Finset α :=
  univ.filter (fun e => l e ∈ A ∧ r e ∈ A)

noncomputable def sols (l r : α → V) (s : α → Bool) (A : Finset V) : Finset (V → Bool) :=
  univ.filter (fun f => (∀ i, i ∉ A → f i = false) ∧
    ∀ e, l e ∈ A → r e ∈ A → xor (f (l e)) (f (r e)) = s e)

noncomputable def incidence (l r : α → V) (A : Finset V) : (V → K) →ₗ[K] (↥(edges l r A) → K) where
  toFun f e := f (l e) + f (r e)
  map_add' f g := by ext e; simp only [Pi.add_apply]; abel
  map_smul' a f := by ext e; simp [mul_add]

noncomputable def pairing {ι : Type*} [Fintype ι] : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K :=
  dotProductBilin K K

lemma pairing_inj {ι : Type*} [Fintype ι] : Function.Injective (pairing (ι := ι)) := by
  classical
  intro f g h
  funext i
  have hh := congrArg (fun H : (ι → K) →ₗ[K] K => H (Pi.single i 1)) h
  change dotProduct f (Pi.single i 1) = dotProduct g (Pi.single i 1) at hh
  simpa only [dotProduct_single_one] using hh

lemma solvable_dual (l r : α → V) (A : Finset V) (z : ↥(edges l r A) → K) :
    (∃ f, incidence l r A f = z) ↔
      ∀ y : ↥(edges l r A) → K, (∀ f, pairing y (incidence l r A f) = 0) → pairing y z = 0 := by
  constructor
  · rintro ⟨f, rfl⟩ y hy
    exact hy f
  · intro h
    let B : (V → K) →ₗ[K] (↥(edges l r A) → K) →ₗ[K] K :=
      (pairing (ι := ↥(edges l r A))).comp (incidence l r A)
    have hz : pairing z ∈ (LinearMap.ker B.flip).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro y hy
      have hh := h y (fun f => by
        have hh := DFunLike.congr_fun (LinearMap.mem_ker.mp hy) f
        change dotProduct (incidence l r A f) y = 0 at hh
        exact (dotProduct_comm _ _).trans hh)
      change dotProduct y z = 0 at hh
      exact (dotProduct_comm _ _).trans hh
    rw [LinearMap.dualAnnihilator_ker_eq_range_flip, LinearMap.flip_flip] at hz
    obtain ⟨f, hf⟩ := LinearMap.mem_range.mp hz
    exact ⟨f, pairing_inj hf⟩

lemma local_solvable (l r : α → V) (s : α → Bool) (A : Finset V) :
    (sols l r s A).Nonempty ↔ ∃ f, incidence l r A f = fun e : ↥(edges l r A) => bit (s e) := by
  constructor
  · rintro ⟨f, hf⟩
    have hs := ((Finset.mem_filter.mp hf).2).2
    refine ⟨bit ∘ f, ?_⟩
    funext e
    have he := (Finset.mem_filter.mp e.property).2
    exact (bit_xor _ _).symm.trans (congrArg bit (hs e he.1 he.2))
  · rintro ⟨f, hf⟩
    choose g hg using fun i => bit_surj (f i)
    let g' := fun i => if i ∈ A then g i else false
    refine ⟨g', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
    · intro i hi
      simp [g', hi]
    · intro e hl hr
      apply bit_inj
      rw [bit_xor]
      let e' : ↥(edges l r A) := ⟨e, Finset.mem_filter.mpr ⟨mem_univ _, hl, hr⟩⟩
      have he : f (l e) + f (r e) = bit (s e) := congrFun hf e'
      simpa [g', hl, hr, hg] using he

lemma same_positive_count (l r : α → V) (s t : α → Bool) (A : Finset V)
    (hs : (sols l r s A).Nonempty) (ht : (sols l r t A).Nonempty) :
    (sols l r s A).card = (sols l r t A).card := by
  obtain ⟨f, hf⟩ := hs
  obtain ⟨g, hg⟩ := ht
  have hf' := (mem_filter.mp hf).2
  have hg' := (mem_filter.mp hg).2
  let shift (u : V → Bool) i := xor (u i) (xor (f i) (g i))
  have invol (u : V → Bool) : shift (shift u) = u := by
    funext i
    change xor (xor (u i) (xor (f i) (g i))) (xor (f i) (g i)) = u i
    cases u i <;> cases (xor (f i) (g i)) <;> rfl
  have maps (u : V → Bool) (hu : u ∈ sols l r s A) : shift u ∈ sols l r t A := by
    have hu' := (mem_filter.mp hu).2
    refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
    · intro i hi
      simp [shift, hu'.1 i hi, hf'.1 i hi, hg'.1 i hi]
    · intro e hl hr
      apply bit_inj
      simp only [shift, bit_xor]
      have h₁ := congrArg bit (hu'.2 e hl hr)
      have h₂ := congrArg bit (hf'.2 e hl hr)
      have h₃ := congrArg bit (hg'.2 e hl hr)
      rw [bit_xor] at h₁ h₂ h₃
      calc
        _ = (bit (u (l e)) + bit (u (r e))) + (bit (f (l e)) + bit (f (r e))) +
              (bit (g (l e)) + bit (g (r e))) := by abel
        _ = _ := by rw [h₁, h₂, h₃, add_self, zero_add]
  have reverse (u : V → Bool) (hu : u ∈ sols l r t A) : shift u ∈ sols l r s A := by
    have hu' := (mem_filter.mp hu).2
    refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
    · intro i hi
      simp [shift, hu'.1 i hi, hf'.1 i hi, hg'.1 i hi]
    · intro e hl hr
      apply bit_inj
      simp only [shift, bit_xor]
      have h₁ := congrArg bit (hu'.2 e hl hr)
      have h₂ := congrArg bit (hf'.2 e hl hr)
      have h₃ := congrArg bit (hg'.2 e hl hr)
      rw [bit_xor] at h₁ h₂ h₃
      calc
        _ = (bit (u (l e)) + bit (u (r e))) + (bit (g (l e)) + bit (g (r e))) +
              (bit (f (l e)) + bit (f (r e))) := by abel
        _ = _ := by rw [h₁, h₂, h₃, add_self, zero_add]
  exact Finset.card_bij' (fun u _ => shift u) (fun u _ => shift u) maps reverse (fun u _ => invol u) (fun u _ => invol u)

lemma dot_v (F : Finset α) (z : α → K) : pairing (v F) z = ∑ e ∈ F, z e := by
  classical
  change (∑ e, (if e ∈ F then 1 else 0) * z e) = _
  calc
    _ = ∑ e, if e ∈ F then z e else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : e ∈ F <;> simp [h]
    _ = _ := by rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

lemma dot_local (S F : Finset α) (hF : F ⊆ S) (z : α → K) :
    pairing (fun e : ↥S => v F e) (fun e : ↥S => z e) = ∑ e ∈ F, z e := by
  classical
  change (∑ e : ↥S, v F e * z e) = _
  rw [← Finset.sum_subtype S (fun _ => Iff.rfl) (fun e => v F e * z e)]
  have hfilter : S.filter (fun e => e ∈ F) = F := by
    ext e
    exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨hF h, h⟩⟩
  calc
    _ = ∑ e ∈ S, if e ∈ F then z e else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : e ∈ F <;> simp [v, h]
    _ = _ := by rw [← Finset.sum_filter, hfilter]

lemma degree_sum (l r : α → V) (hn : ∀ e, l e ≠ r e) (F : Finset α) (f : V → K) :
    (∑ e ∈ F, (f (l e) + f (r e))) =
      ∑ i, (((F.filter fun e => l e = i ∨ r e = i).card : ℕ) : K) * f i := by
  classical
  have hrow (e : α) :
      f (l e) + f (r e) = ∑ i, (if l e = i ∨ r e = i then (1 : K) else 0) * f i := by
    calc
      _ = (∑ i, (if l e = i then f i else 0)) + ∑ i, (if r e = i then f i else 0) := by simp
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hl : l e = i <;> by_cases hr : r e = i
        · exact (hn e (hl.trans hr.symm)).elim
        · simp [hl, hr]
        · simp [hl, hr]
        · simp [hl, hr]
  simp_rw [hrow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, Finset.sum_boole]

lemma even_iff (l r : α → V) (hn : ∀ e, l e ≠ r e) (F : Finset α) :
    (∀ f : V → K, (∑ e ∈ F, (f (l e) + f (r e))) = 0) ↔
      ∀ i, Even ((F.filter fun e => l e = i ∨ r e = i).card) := by
  classical
  simp_rw [degree_sum l r hn, ← ZMod.natCast_eq_zero_iff_even]
  constructor
  · intro h i
    have hi := h (Pi.single i 1)
    change dotProduct (fun j => ((F.filter fun e => l e = j ∨ r e = j).card : K))
      (Pi.single i 1) = 0 at hi
    simpa only [dotProduct_single_one] using hi
  · intro h f
    simp [h]

lemma characterization (l r : α → V) (hn : ∀ e, l e ≠ r e) (s : α → Bool) (A : Finset V) :
    (sols l r s A).Nonempty ↔
      ∀ F ⊆ edges l r A, (∀ i, Even ((F.filter fun e => l e = i ∨ r e = i).card)) →
        pairing (v F) (bit ∘ s) = 0 := by
  classical
  rw [local_solvable, solvable_dual]
  have he (F : Finset α) (hF : F ⊆ edges l r A) :
      (∀ f, pairing (fun e : ↥(edges l r A) => v F e) (incidence l r A f) = 0) ↔
        ∀ i, Even ((F.filter fun e => l e = i ∨ r e = i).card) := by
    have hh (f : V → K) : pairing (fun e : ↥(edges l r A) => v F e) (incidence l r A f) =
        ∑ e ∈ F, (f (l e) + f (r e)) :=
      dot_local _ _ hF (fun e => f (l e) + f (r e))
    simp_rw [hh]
    exact even_iff l r hn F
  constructor
  · intro h F hF hEven
    rw [dot_v, ← dot_local _ _ hF]
    exact h _ ((he F hF).2 hEven)
  · intro h y hy
    let F := (edges l r A).filter (fun e => ∃ he : e ∈ edges l r A, y ⟨e, he⟩ = 1)
    have hF : F ⊆ edges l r A := Finset.filter_subset _ _
    have hyF : y = fun e : ↥(edges l r A) => v F e := by
      funext e
      obtain ⟨b, hb⟩ := bit_surj (y e)
      cases b <;> simp [v, F, e.property, ← hb, bit]
    rw [hyF] at hy ⊢
    exact (dot_local _ _ hF (bit ∘ s)).trans ((dot_v F (bit ∘ s)).symm.trans
      (h F hF ((he F hF).1 hy)))

lemma counts_eq_iff (l r : α → V) (s t : α → Bool) (A : Finset V) :
    (sols l r s A).card = (sols l r t A).card ↔
      ((sols l r s A).Nonempty ↔ (sols l r t A).Nonempty) := by
  constructor
  · intro h
    simpa only [← Finset.card_pos, h]
  · intro h
    by_cases hs : (sols l r s A).Nonempty
    · exact same_positive_count l r s t A hs (h.mp hs)
    · have ht : ¬ (sols l r t A).Nonempty := mt h.mpr hs
      simp [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.not_nonempty_iff_eq_empty.mp ht]

end PEqualNP.Outside.L_lib_1199.Core

namespace PEqualNP.Outside.L_lib_1199.Trace

noncomputable def bits {S Q I : Type*} (ask : I → List Nat → Q) (count : S → Q → Nat)
    (s : S) : List I → List Nat → List Bool
  | [], _ => []
  | i :: l, h =>
    let a := count s (ask i h)
    decide (a ≠ 0) :: bits ask count s l (h ++ [a])

lemma bits_length {S Q I : Type*} (ask : I → List Nat → Q) (count : S → Q → Nat)
    (s : S) (l : List I) (h : List Nat) : (bits ask count s l h).length = l.length := by
  induction l generalizing h with
  | nil => rfl
  | cons i l ih => simp [bits, ih]

lemma bits_sound {S Q I : Type*} (ask : I → List Nat → Q) (count : S → Q → Nat)
    (s t : S) (hc : ∀ q, (count s q ≠ 0 ↔ count t q ≠ 0) → count s q = count t q)
    (l : List I) (h : List Nat) (he : bits ask count s l h = bits ask count t l h) :
    l.foldl (fun h i => h ++ [count s (ask i h)]) h =
      l.foldl (fun h i => h ++ [count t (ask i h)]) h := by
  induction l generalizing h with
  | nil => rfl
  | cons i l ih =>
    simp only [bits, List.cons.injEq, decide_eq_decide] at he
    have ha := hc (ask i h) he.1
    simp only [List.foldl_cons, ha]
    apply ih
    simpa only [ha] using he.2

lemma lower {S Q : Type*} {d r : ℕ} (ask : Fin d → List Nat → Q) (count : S → Q → Nat)
    (hc : ∀ s t q, (count s q ≠ 0 ↔ count t q ≠ 0) → count s q = count t q)
    (sign : (Fin r → ZMod 2) → S)
    (hdet : ∀ a b, (List.finRange d).foldl (fun h i => h ++ [count (sign a) (ask i h)]) [] =
      (List.finRange d).foldl (fun h i => h ++ [count (sign b) (ask i h)]) [] → a = b) :
    2 ^ r ≤ 2 ^ d := by
  let L := fun a => bits ask count (sign a) (List.finRange d) []
  have hlen (a) : (L a).length = d := by simp [L, bits_length]
  let code : (Fin r → ZMod 2) → (Fin d → Bool) := fun a i => (L a)[i.val]'(by rw [hlen]; exact i.isLt)
  have hinj : Function.Injective code := by
    intro a b h
    apply hdet
    apply bits_sound ask count (sign a) (sign b) (hc _ _)
    change L a = L b
    apply List.ext_getElem ((hlen a).trans (hlen b).symm)
    intro j hj hj'
    exact congrFun h ⟨j, (hlen a) ▸ hj⟩
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective code hinj

end PEqualNP.Outside.L_lib_1199.Trace

namespace PEqualNP.Outside.L_lib_1199.Rank

open scoped BigOperators
open Module

variable {E : Type*} [DecidableEq E]

abbrev F₂ := ZMod 2

private theorem binary (a : F₂) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

def vec (F : Finset E) (e : E) : F₂ := if e ∈ F then 1 else 0

def span (small : Finset (Finset E)) : Submodule F₂ (E → F₂) :=
  Submodule.span F₂ (vec '' (small : Set (Finset E)))

theorem mem_span_iff (small : Finset (Finset E)) (F : Finset E) :
    vec F ∈ span small ↔
      ∃ J : Finset (Finset E), J ⊆ small ∧
        ∀ e : E, e ∈ F ↔ Odd ((J.filter (fun K => e ∈ K)).card) := by
  classical
  have key (J : Finset (Finset E)) (e : E) :
      (∑ K ∈ J, vec K e) = ((J.filter (fun K => e ∈ K)).card : F₂) := by
    calc
      (∑ K ∈ J, vec K e) = ∑ K ∈ J.filter (fun K => e ∈ K), (1 : F₂) := by
        rw [Finset.sum_filter]
        rfl
      _ = _ := by simp
  change vec F ∈ Submodule.span F₂ (vec '' (small : Set (Finset E))) ↔ _
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' F₂).mp h
    let J := small.filter (fun K => c K = 1)
    refine ⟨J, Finset.filter_subset _ _, fun e => ?_⟩
    have he : (∑ K ∈ J, vec K e) = vec F e := by
      calc
        _ = ∑ K ∈ small, c K * vec K e := by
          change (∑ K ∈ small.filter (fun K => c K = 1), vec K e) = _
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro K _
          rcases binary (c K) with hK | hK <;> simp [hK]
        _ = vec F e := by
          simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hc e
    rw [← ZMod.natCast_eq_one_iff_odd, ← key, he]
    by_cases hF : e ∈ F <;> simp [vec, hF]
  · rintro ⟨J, hJ, h⟩
    have hs : (∑ K ∈ J, vec K) ∈ span small :=
      (span small).sum_mem (fun K hK => Submodule.subset_span ⟨K, hJ hK, rfl⟩)
    suffices he : (∑ K ∈ J, vec K) = vec F by rwa [← he]
    funext e
    rw [Finset.sum_apply, key]
    by_cases hF : e ∈ F
    · simpa [vec, hF] using (ZMod.natCast_eq_one_iff_odd.mpr ((h e).mp hF))
    · have hn : ¬ Odd ((J.filter (fun K => e ∈ K)).card) := fun ho => hF ((h e).mpr ho)
      have hz : ((J.filter (fun K => e ∈ K)).card : F₂) = 0 := by
        rcases binary ((J.filter (fun K => e ∈ K)).card : F₂) with hz | ho
        · exact hz
        · exact (hn (ZMod.natCast_eq_one_iff_odd.mp ho)).elim
      simpa [vec, hF] using hz

noncomputable def spanSet [Fintype E] (small : Finset (Finset E)) : Finset (Finset E) :=
  open Classical in
  Finset.univ.filter (fun F => ∃ J : Finset (Finset E), J ⊆ small ∧
    ∀ e : E, e ∈ F ↔ Odd ((J.filter (fun K => e ∈ K)).card))

theorem spanSet_card [Fintype E] (small : Finset (Finset E)) {r : Nat}
    (b : Basis (Fin r) F₂ (span small)) : (spanSet small).card = 2 ^ r := by
  classical
  let f : ↥(spanSet small) → span small := fun F =>
    ⟨vec F, (mem_span_iff small F).mpr (Finset.mem_filter.mp F.property).2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro F G h
      apply Subtype.ext
      apply Finset.ext
      intro e
      have h' := congrFun (congrArg Subtype.val h) e
      change vec F e = vec G e at h'
      by_cases hF : e ∈ F.val <;> by_cases hG : e ∈ G.val <;> simp_all [vec]
    · intro x
      let F := Finset.univ.filter (fun e => x.val e = 1)
      have hx : vec F = x.val := by
        funext e
        rcases binary (x.val e) with he | he <;> simp [vec, F, he]
      refine ⟨⟨F, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_span_iff small F).mp ?_⟩⟩, ?_⟩
      · exact hx.symm ▸ x.property
      · exact Subtype.ext hx
  have h := Nat.card_congr ((Equiv.ofBijective f hf).trans b.equivFun.toEquiv)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_eq_fintype_card] at h
  simpa [Fintype.card_fun] using h

theorem exists_basis [Fintype E] (small : Finset (Finset E))
    (G : Set (E → F₂)) (hG : Submodule.span F₂ G = span small) :
    ∃ r : Nat, ∃ b : Basis (Fin r) F₂ (span small), ∀ i, (b i).val ∈ G := by
  classical
  let U := span small
  let T : Set U := U.subtype ⁻¹' G
  have himage : U.subtype '' T = G := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hU : x ∈ U := by
        change x ∈ span small
        rw [← hG]
        exact Submodule.subset_span hx
      exact ⟨⟨x, hU⟩, hx, rfl⟩
  have htop : Submodule.span F₂ T = ⊤ := by
    apply Submodule.map_injective_of_injective U.injective_subtype
    rw [Submodule.map_span, himage, U.map_subtype_top]
    exact hG
  have hind := linearIndepOn_empty F₂ (id : U → U)
  let hsub : (∅ : Set U) ⊆ T := Set.empty_subset T
  let b := Basis.extendLe hind hsub htop.ge
  let _ : Fintype (hind.extend hsub) := Fintype.ofFinite _
  let e := Fintype.equivFin (hind.extend hsub)
  refine ⟨_, b.reindex e, fun i => ?_⟩
  rw [Basis.reindex_apply, Basis.extendLe_apply_self]
  exact hind.extend_subset hsub (e.symm i).property

variable [Fintype E]

def dot (s : E → F₂) : (E → F₂) →ₗ[F₂] F₂ where
  toFun x := ∑ e, x e * s e
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_assoc, Finset.mul_sum]

theorem dot_vec (s : E → F₂) (F : Finset E) : dot s (vec F) = ∑ e ∈ F, s e := by
  change (∑ e, vec F e * s e) = _
  calc
    (∑ e, vec F e * s e) = ∑ e, if e ∈ F then s e else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : e ∈ F <;> simp [vec, he]
    _ = _ := by rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem realize {U : Submodule F₂ (E → F₂)} {ι : Type*} (b : Basis ι F₂ U)
    (a : ι → F₂) : ∃ s : E → F₂, ∀ i, dot s (b i).val = a i := by
  classical
  obtain ⟨g, hg⟩ := (b.constr F₂ a).exists_extend
  let s : E → F₂ := fun e => g (Pi.single e 1)
  have hdot (x : E → F₂) : dot s x = g x := by
    change (∑ e, x e * g (Pi.single e 1)) = g x
    calc
      _ = ∑ e, g (Pi.single e (x e)) := by
        apply Finset.sum_congr rfl
        intro e _
        have he : Pi.single e (x e) = x e • (Pi.single e 1 : E → F₂) := by
          funext j
          by_cases hj : j = e <;> simp [hj]
        rw [he, map_smul, smul_eq_mul]
      _ = g x := by rw [← map_sum, Finset.univ_sum_single]
  refine ⟨s, fun i => ?_⟩
  rw [hdot]
  change (g.comp U.subtype) (b i) = a i
  rw [hg, Basis.constr_basis]

end PEqualNP.Outside.L_lib_1199.Rank

namespace PEqualNP.Outside.L_lib_1199.Cycles

open Classical
open scoped BigOperators

variable {V E : Type*} [LinearOrder V] [Fintype E] [DecidableEq E]
variable (l r : E → V)

def verts (F : Finset E) : Finset V := F.image l ∪ F.image r

def induced (A : Finset V) : Finset E := Finset.univ.filter fun e => l e ∈ A ∧ r e ∈ A

def IsEven (F : Finset E) : Prop :=
  ∀ i : V, Even ((F.filter (fun e => l e = i ∨ r e = i)).card)

def vec (F : Finset E) : E → ZMod 2 := fun e => if e ∈ F then 1 else 0

def Atom (C : Finset E) : Prop :=
  C.Nonempty ∧ IsEven l r C ∧ (∀ K ⊆ C, IsEven l r K → K = ∅ ∨ K = C) ∧
  C = induced l r (verts l r C)

@[simp] theorem mem_induced {A : Finset V} {e : E} :
    e ∈ induced l r A ↔ l e ∈ A ∧ r e ∈ A := by
  simp [induced]

theorem mem_verts {F : Finset E} {i : V} :
    i ∈ verts l r F ↔ ∃ e ∈ F, l e = i ∨ r e = i := by
  rw [verts, Finset.mem_union]
  constructor
  · rintro (h | h)
    · obtain ⟨e, he, hi⟩ := Finset.mem_image.mp h
      exact ⟨e, he, Or.inl hi⟩
    · obtain ⟨e, he, hi⟩ := Finset.mem_image.mp h
      exact ⟨e, he, Or.inr hi⟩
  · rintro ⟨e, he, hi | hi⟩
    · exact Or.inl (Finset.mem_image.mpr ⟨e, he, hi⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨e, he, hi⟩)

theorem verts_subset_iff {F : Finset E} {A : Finset V} :
    verts l r F ⊆ A ↔ F ⊆ induced l r A := by
  constructor
  · intro h e he
    exact (mem_induced l r).2
      ⟨h ((mem_verts l r).2 ⟨e, he, Or.inl rfl⟩), h ((mem_verts l r).2 ⟨e, he, Or.inr rfl⟩)⟩
  · intro h i hi
    obtain ⟨e, he, hi | hi⟩ := (mem_verts l r).1 hi
    · exact hi ▸ ((mem_induced l r).1 (h he)).1
    · exact hi ▸ ((mem_induced l r).1 (h he)).2

@[simp] theorem vec_empty : vec (∅ : Finset E) = 0 := by
  funext e
  simp [vec]

theorem vec_injective : Function.Injective (vec (E := E)) := by
  intro F K h
  ext e
  have he := congrFun h e
  by_cases hF : e ∈ F <;> by_cases hK : e ∈ K <;> simp_all [vec]

private def edgeXor (F K : Finset E) : Finset E := (F \ K) ∪ (K \ F)

private theorem edgeXor_subset {F K X : Finset E} (hF : F ⊆ X) (hK : K ⊆ X) :
    edgeXor F K ⊆ X := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hF (Finset.mem_sdiff.mp he).1
  · exact hK (Finset.mem_sdiff.mp he).1

private theorem vec_edgeXor (F K : Finset E) : vec (edgeXor F K) = vec F + vec K := by
  funext e
  by_cases hF : e ∈ F <;> by_cases hK : e ∈ K <;>
    simp [vec, edgeXor, hF, hK, CharTwo.add_self_eq_zero]

private theorem vec_sdiff {F K : Finset E} (h : K ⊆ F) : vec (F \ K) = vec F + vec K := by
  have hx : edgeXor F K = F \ K := by
    ext e
    by_cases hK : e ∈ K
    · simp [edgeXor, hK, h hK]
    · simp [edgeXor, hK]
  rw [← hx, vec_edgeXor]

private theorem vec_partition {F K : Finset E} (h : K ⊆ F) : vec F = vec (F \ K) + vec K := by
  rw [vec_sdiff h]
  funext e
  change vec F e = (vec F e + vec K e) + vec K e
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem vec_insert {F : Finset E} {e : E} (h : e ∉ F) :
    vec (insert e F) = vec {e} + vec F := by
  have hx : edgeXor {e} F = insert e F := by
    ext f
    rcases eq_or_ne f e with rfl | hne
    · simp [edgeXor, h]
    · simp [edgeXor, hne]
  rw [← hx, vec_edgeXor]

def boundary (x : E → ZMod 2) : V → ZMod 2 := fun i =>
  ∑ e, if l e = i ∨ r e = i then x e else 0

private theorem boundary_add (x y : E → ZMod 2) :
    boundary l r (x + y) = boundary l r x + boundary l r y := by
  funext i
  change (∑ e, if l e = i ∨ r e = i then x e + y e else 0) =
    (∑ e, if l e = i ∨ r e = i then x e else 0) + (∑ e, if l e = i ∨ r e = i then y e else 0)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (by intro e _; split <;> simp_all)

@[simp] private theorem boundary_zero : boundary l r (0 : E → ZMod 2) = 0 := by
  funext i
  simp [boundary]

theorem boundary_vec (F : Finset E) (i : V) :
    boundary l r (vec F) i = ((F.filter (fun e => l e = i ∨ r e = i)).card : ZMod 2) := by
  unfold boundary
  calc
    _ = ∑ e ∈ F, if l e = i ∨ r e = i then vec F e else 0 :=
      (Finset.sum_subset (Finset.subset_univ F) (by intro e _ he; simp [vec, he])).symm
    _ = ∑ e ∈ F, if l e = i ∨ r e = i then (1 : ZMod 2) else 0 :=
      Finset.sum_congr rfl (by intro e he; simp [vec, he])
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem isEven_iff_boundary (F : Finset E) : IsEven l r F ↔ boundary l r (vec F) = 0 := by
  constructor
  · intro h
    funext i
    exact (boundary_vec l r F i).trans ((ZMod.natCast_eq_zero_iff_even).2 (h i))
  · intro h i
    apply ZMod.natCast_eq_zero_iff_even.mp
    rw [← boundary_vec l r, h]
    rfl

private def pulse (a : V) : V → ZMod 2 := fun i => if a = i then 1 else 0

private theorem pulse_pair_apply {a b : V} (h : a ≠ b) (i : V) :
    (pulse a + pulse b) i = if a = i ∨ b = i then 1 else 0 := by
  by_cases ha : a = i
  · have hb : b ≠ i := fun hb => h (ha.trans hb.symm)
    simp [pulse, ha, hb]
  · by_cases hb : b = i <;> simp [pulse, ha, hb]

private theorem pulse_pair_ne_zero {a b : V} (h : a ≠ b) : pulse a + pulse b ≠ 0 := by
  intro hz
  have hi := congrFun hz a
  rw [pulse_pair_apply h] at hi
  simp at hi

private theorem boundary_singleton (hord : ∀ e, l e < r e) (e : E) :
    boundary l r (vec {e}) = pulse (l e) + pulse (r e) := by
  funext i
  rw [boundary_vec, pulse_pair_apply (ne_of_lt (hord e))]
  by_cases hi : l e = i ∨ r e = i <;> simp [Finset.filter_singleton, hi]

private theorem edge_eq_of_pair (hord : ∀ e, l e < r e)
    (hinj : Function.Injective (fun e => (l e, r e))) {e f : E}
    (h : pulse (l e) + pulse (r e) = pulse (l f) + pulse (r f)) : e = f := by
  have hmem (i : V) (hi : l e = i ∨ r e = i) : l f = i ∨ r f = i := by
    have hh := congrFun h i
    rw [pulse_pair_apply (ne_of_lt (hord e)), pulse_pair_apply (ne_of_lt (hord f)), ite_eq_left hi] at hh
    by_contra hn
    simp [hn] at hh
  rcases hmem (l e) (Or.inl rfl) with hll | hrl <;>
    rcases hmem (r e) (Or.inr rfl) with hlr | hrr
  · exact (ne_of_lt (hord e) (hll.symm.trans hlr)).elim
  · exact hinj (Prod.ext hll.symm hrr.symm)
  · have hf := hord f
    rw [hlr, hrl] at hf
    exact (not_lt_of_ge (hord e).le hf).elim
  · exact (ne_of_lt (hord e) (hrl.symm.trans hrr)).elim

private def Joins (F : Finset E) (a b : V) : Prop :=
  ∃ K ⊆ F, boundary l r (vec K) = pulse a + pulse b

private theorem joins_refl (F : Finset E) (a : V) : Joins l r F a a := by
  refine ⟨∅, Finset.empty_subset _, ?_⟩
  rw [vec_empty, boundary_zero]
  funext i
  exact (CharTwo.add_self_eq_zero (pulse a i)).symm

private theorem joins_symm {F : Finset E} {a b : V} (h : Joins l r F a b) : Joins l r F b a := by
  obtain ⟨K, hK, h⟩ := h
  exact ⟨K, hK, h.trans (add_comm _ _)⟩

private theorem joins_trans {F : Finset E} {a b c : V} (h₁ : Joins l r F a b)
    (h₂ : Joins l r F b c) : Joins l r F a c := by
  obtain ⟨K, hK, hK'⟩ := h₁
  obtain ⟨L, hL, hL'⟩ := h₂
  refine ⟨edgeXor K L, edgeXor_subset hK hL, ?_⟩
  rw [vec_edgeXor, boundary_add, hK', hL']
  funext i
  change (pulse a i + pulse b i) + (pulse b i + pulse c i) = pulse a i + pulse c i
  calc
    _ = pulse a i + (pulse b i + pulse b i) + pulse c i := by ac_rfl
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

private theorem joins_step (hord : ∀ e, l e < r e) {F : Finset E} {e : E} (he : e ∈ F)
    (a : V) : Joins l r F a (l e) ↔ Joins l r F a (r e) := by
  have hj : Joins l r F (l e) (r e) :=
    ⟨{e}, Finset.singleton_subset_iff.2 he, boundary_singleton l r hord e⟩
  exact ⟨fun h => joins_trans l r h hj, fun h => joins_trans l r h (joins_symm l r hj)⟩

private theorem class_contains_support {F : Finset E} (hF : IsEven l r F)
    (hmin : ∀ K ⊆ F, IsEven l r K → K = ∅ ∨ K = F) (P : V → Prop)
    (hside : ∀ e ∈ F, P (l e) ↔ P (r e)) {a b : V}
    (ha : a ∈ verts l r F) (hPa : P a) (hb : b ∈ verts l r F) : P b := by
  let K := F.filter fun e => P (l e)
  have side {e : E} (he : e ∈ F) {v : V} (hv : l e = v ∨ r e = v) :
      P (l e) ↔ P v := by
    rcases hv with h | h
    · rw [h]
    · rw [← h]
      exact hside e he
  have hKeven : IsEven l r K := by
    intro v
    by_cases hv : P v
    · have hh : K.filter (fun e => l e = v ∨ r e = v) = F.filter (fun e => l e = v ∨ r e = v) := by
        ext e
        simp only [K, Finset.mem_filter]
        exact ⟨fun ⟨⟨he, _⟩, hi⟩ => ⟨he, hi⟩, fun ⟨he, hi⟩ => ⟨⟨he, (side he hi).2 hv⟩, hi⟩⟩
      rw [hh]
      exact hF v
    · have hh : K.filter (fun e => l e = v ∨ r e = v) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        obtain ⟨⟨he, hj⟩, hi⟩ := by simpa only [K, Finset.mem_filter] using he
        exact hv ((side he hi).1 hj)
      rw [hh]
      simp
  have hKne : K ≠ ∅ := by
    obtain ⟨e, he, hi⟩ := (mem_verts l r).1 ha
    exact Finset.nonempty_iff_ne_empty.1 ⟨e, Finset.mem_filter.mpr ⟨he, (side he hi).2 hPa⟩⟩
  have hK : K = F := (hmin K (Finset.filter_subset _ _) hKeven).resolve_left hKne
  obtain ⟨e, he, hi⟩ := (mem_verts l r).1 hb
  have heK : e ∈ K := hK.symm ▸ he
  exact (side he hi).1 (Finset.mem_filter.mp heK).2

private theorem joins_of_minimal_even (hord : ∀ e, l e < r e) {F : Finset E}
    (hF : IsEven l r F) (hmin : ∀ K ⊆ F, IsEven l r K → K = ∅ ∨ K = F)
    {a b : V} (ha : a ∈ verts l r F) (hb : b ∈ verts l r F) : Joins l r F a b :=
  class_contains_support l r hF hmin (Joins l r F a)
    (fun _ he => joins_step l r hord he a) ha (joins_refl l r F a) hb

private theorem partner_card (hord : ∀ e, l e < r e)
    (hinj : Function.Injective (fun e => (l e, r e))) {F : Finset E} {e : E} (he : e ∉ F)
    (h : boundary l r (vec F) = pulse (l e) + pulse (r e)) : 1 < F.card := by
  by_contra hn
  have hpos : 0 < F.card := by
    by_contra hn'
    have hF : F = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hF, vec_empty, boundary_zero] at h
    exact pulse_pair_ne_zero (ne_of_lt (hord e)) h.symm
  obtain ⟨f, rfl⟩ := Finset.card_eq_one.mp (show F.card = 1 by omega)
  have hfe := edge_eq_of_pair l r hord hinj ((boundary_singleton l r hord f).symm.trans h)
  exact he (by simp [hfe])

private theorem even_insert_partner (hord : ∀ e, l e < r e) {F : Finset E} {e : E}
    (he : e ∉ F) (h : boundary l r (vec F) = pulse (l e) + pulse (r e)) :
    IsEven l r (insert e F) := by
  rw [isEven_iff_boundary, vec_insert he, boundary_add, boundary_singleton l r hord e, h]
  funext i
  exact CharTwo.add_self_eq_zero ((pulse (l e) + pulse (r e)) i)

private theorem even_sdiff (F K : Finset E) (hKF : K ⊆ F) (hF : IsEven l r F) (hK : IsEven l r K) :
    IsEven l r (F \ K) := by
  rw [isEven_iff_boundary, vec_sdiff hKF, boundary_add,
    (isEven_iff_boundary l r F).1 hF, (isEven_iff_boundary l r K).1 hK, add_zero]

set_option maxHeartbeats 1000000 in
/-- Every even edge set on at most `w` vertices lies in the span of the induced minimal
nonempty even edge sets on at most `w` vertices. -/
theorem span_of_even (hord : ∀ e, l e < r e) (hinj : Function.Injective (fun e => (l e, r e)))
    (w : ℕ) (F : Finset E) (hsize : (verts l r F).card ≤ w) (hF : IsEven l r F) :
    vec F ∈ Submodule.span (ZMod 2) {v | ∃ C, Atom l r C ∧ (verts l r C).card ≤ w ∧ vec C = v} := by
  by_cases hF0 : F = ∅
  · rw [hF0, vec_empty]
    exact Submodule.zero_mem _
  have hFi : F ⊆ induced l r (verts l r F) := (verts_subset_iff l r).1 (fun _ h => h)
  have bound {X : Finset E} (hX : X ⊆ induced l r (verts l r F)) : (verts l r X).card ≤ w :=
    (Finset.card_le_card ((verts_subset_iff l r).2 hX)).trans hsize
  by_cases hmin : ∀ K ⊆ F, IsEven l r K → K = ∅ ∨ K = F
  · by_cases hind : F = induced l r (verts l r F)
    · exact Submodule.subset_span ⟨F, ⟨Finset.nonempty_iff_ne_empty.2 hF0, hF, hmin, hind⟩, hsize, rfl⟩
    have hex : ∃ e ∈ induced l r (verts l r F), e ∉ F := by
      by_contra! h
      exact hind (Finset.Subset.antisymm hFi h)
    obtain ⟨e, hei, he⟩ := hex
    obtain ⟨K, hKF, hK⟩ := joins_of_minimal_even l r hord hF hmin
      ((mem_induced l r).1 hei).1 ((mem_induced l r).1 hei).2
    let D := F \ K
    have hDF : D ⊆ F := Finset.sdiff_subset
    have heK : e ∉ K := fun h => he (hKF h)
    have heD : e ∉ D := fun h => he (hDF h)
    have hD : boundary l r (vec D) = pulse (l e) + pulse (r e) := by
      dsimp only [D]
      rw [vec_sdiff hKF, boundary_add, (isEven_iff_boundary l r F).1 hF, hK, zero_add]
    have hKcard := partner_card l r hord hinj heK hK
    have hDcard := partner_card l r hord hinj heD hD
    have hcards : D.card + K.card = F.card := Finset.card_sdiff_add_card_eq_card hKF
    have hKsmall : (insert e K).card < F.card := by
      rw [Finset.card_insert_of_notMem heK]
      omega
    have hDsmall : (insert e D).card < F.card := by
      rw [Finset.card_insert_of_notMem heD]
      omega
    have hKbound := bound (Finset.insert_subset_iff.mpr ⟨hei, hKF.trans hFi⟩)
    have hDbound := bound (Finset.insert_subset_iff.mpr ⟨hei, hDF.trans hFi⟩)
    have hKm := span_of_even hord hinj w (insert e K) hKbound (even_insert_partner l r hord heK hK)
    have hDm := span_of_even hord hinj w (insert e D) hDbound (even_insert_partner l r hord heD hD)
    have hvec : vec F = vec (insert e K) + vec (insert e D) := by
      rw [vec_insert heK, vec_insert heD]
      funext f
      change vec F f = (vec {e} f + vec K f) + (vec {e} f + vec D f)
      calc
        _ = vec D f + vec K f := congrFun (vec_partition hKF) f
        _ = (vec D f + vec K f) + (vec {e} f + vec {e} f) := by simp [CharTwo.add_self_eq_zero]
        _ = _ := by ac_rfl
    rw [hvec]
    exact Submodule.add_mem _ hKm hDm
  · push Not at hmin
    obtain ⟨K, hKF, hKe, hK0, hKne⟩ := hmin
    let D := F \ K
    have hDF : D ⊆ F := Finset.sdiff_subset
    have hKsmall : K.card < F.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hKF, hKne⟩)
    have hDsmall : D.card < F.card := by
      have hp := Finset.card_pos.2 hK0
      have hc : D.card + K.card = F.card := Finset.card_sdiff_add_card_eq_card hKF
      omega
    have hKm := span_of_even hord hinj w K (bound (hKF.trans hFi)) hKe
    have hDm := span_of_even hord hinj w D (bound (hDF.trans hFi)) (even_sdiff l r F K hKF hF hKe)
    rw [vec_partition hKF]
    exact Submodule.add_mem _ hDm hKm
termination_by F.card
decreasing_by all_goals omega

end PEqualNP.Outside.L_lib_1199.Cycles
namespace PEqualNP.Outside.L_lib_1199

open Finset
open scoped BigOperators

lemma support_subset {V α : Type*} [Fintype α] [DecidableEq V] [DecidableEq α]
    (l r : α → V) (F : Finset α) (A : Finset V) (h : F ⊆ Core.edges l r A) :
    (F.image l ∪ F.image r) ⊆ A := by
  intro i hi
  rcases mem_union.mp hi with hi | hi
  · obtain ⟨e, he, rfl⟩ := mem_image.mp hi
    exact ((mem_filter.mp (h he)).2).1
  · obtain ⟨e, he, rfl⟩ := mem_image.mp hi
    exact ((mem_filter.mp (h he)).2).2

end PEqualNP.Outside.L_lib_1199

open PEqualNP.Outside.L_lib_1199

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.L_lib_1199 :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (n w : Nat) (E : Finset (Fin n × Fin n)), (∀ e ∈ E, e.1 < e.2) →
      let V := Fin n
      let M := ↥E → Bool
      let count := fun (s : M) (A : Finset V) =>
        ((Finset.univ : Finset (V → Bool)).filter (fun f =>
          (∀ i, i ∉ A → f i = false) ∧
          ∀ e : ↥E, e.val.1 ∈ A → e.val.2 ∈ A → xor (f e.val.1) (f e.val.2) = s e)).card
      let small := (Finset.univ : Finset (Finset ↥E)).filter (fun F =>
        (F.image (fun e => e.val.1) ∪ F.image (fun e => e.val.2)).card ≤ w ∧
        ∀ i : V, Even ((F.filter (fun e => e.val.1 = i ∨ e.val.2 = i)).card))
      let spanSet := (Finset.univ : Finset (Finset ↥E)).filter (fun F =>
        ∃ J : Finset (Finset ↥E), J ⊆ small ∧ ∀ e : ↥E, e ∈ F ↔ Odd ((J.filter (fun K => e ∈ K)).card))
      let same := fun (s t : M) => ∀ A : Finset V, A.card ≤ w → count s A = count t A
      ∀ d : Nat,
        let adaptive := ∃ ask : Fin d → List Nat → Finset V,
          (∀ i h, (ask i h).card ≤ w) ∧
          let trace := fun (s : M) => (List.finRange d).foldl (fun h i => h ++ [count s (ask i h)]) []
          ∀ s t, trace s = trace t → same s t
        let fixedList := ∃ ask : Fin d → Finset V, (∀ i, (ask i).card ≤ w) ∧
          ∀ s t, (∀ i, count s (ask i) = count t (ask i)) → same s t
        (adaptive → spanSet.card ≤ 2^d) ∧ (spanSet.card ≤ 2^d → fixedList) := by
  classical
  intro n w E hE V M count small spanSet same d adaptive fixedList
  let l : ↥E → Fin n := fun e => e.val.1
  let r : ↥E → Fin n := fun e => e.val.2
  have hord (e : ↥E) : l e < r e := hE e e.property
  have hn (e : ↥E) : l e ≠ r e := ne_of_lt (hord e)
  have hinj : Function.Injective (fun e => (l e, r e)) := by
    intro e f h
    exact Subtype.ext h
  change (adaptive → spanSet.card ≤ 2 ^ d) ∧ (spanSet.card ≤ 2 ^ d → fixedList)
  have hcount (s : M) (A : Finset V) : count s A = (Core.sols l r s A).card := by
    apply congrArg Finset.card
    ext f
    simp only [Core.sols, Finset.mem_filter, Finset.mem_univ, true_and, l, r]
    exact Iff.rfl
  have hsmall (F : Finset ↥E) : F ∈ small ↔ (Cycles.verts l r F).card ≤ w ∧ Cycles.IsEven l r F := by
    simp only [small, Finset.mem_filter, Finset.mem_univ, true_and, Cycles.verts, Cycles.IsEven, l, r]
    constructor <;> rintro ⟨hw, h⟩ <;> refine ⟨?_, fun i => ?_⟩
    all_goals first
      | (convert hw using 2 <;> ext i <;> simp only [Finset.mem_union, Finset.mem_image])
      | (convert h i using 2 <;> ext e <;> simp)
  let G : Set (↥E → ZMod 2) := {v | ∃ C, Cycles.Atom l r C ∧ (Cycles.verts l r C).card ≤ w ∧ Cycles.vec C = v}
  have hG : Submodule.span (ZMod 2) G = Rank.span small := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro v ⟨C, hC, hw, rfl⟩
      exact Submodule.subset_span ⟨C, (hsmall C).2 ⟨hw, hC.2.1⟩, rfl⟩
    · apply Submodule.span_le.mpr
      rintro v ⟨F, hF, rfl⟩
      exact Cycles.span_of_even l r hord hinj w F ((hsmall F).1 hF).1 ((hsmall F).1 hF).2
  obtain ⟨k, b, hb⟩ := Rank.exists_basis small G hG
  choose C hC hwC eqC using hb
  have hspan : spanSet = Rank.spanSet small := by
    ext F
    simp only [spanSet, Rank.spanSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨J, hJ, h⟩ <;> refine ⟨J, hJ, fun e => ?_⟩
    all_goals
      convert h e using 3
      ext K
      simp
  have hcard : spanSet.card = 2 ^ k := hspan ▸ Rank.spanSet_card small b
  let signature (s : M) (i : Fin k) : ZMod 2 := Rank.dot (Core.bit ∘ s) (b i).val
  have hdot (s : M) (F : Finset ↥E) :
      Rank.dot (Core.bit ∘ s) (Rank.vec F) = Core.pairing (Core.v F) (Core.bit ∘ s) := by
    rw [Rank.dot_vec, Core.dot_v]
  have cycle_query (s : M) (i : Fin k) : count s (Cycles.verts l r (C i)) ≠ 0 ↔ signature s i = 0 := by
    let A := Cycles.verts l r (C i)
    rw [hcount, ← Nat.pos_iff_ne_zero, Finset.card_pos, Core.characterization l r hn]
    change (∀ F ⊆ Core.edges l r A, _ → _) ↔ _
    have hi : C i = Core.edges l r A := (hC i).2.2.2
    have heq : signature s i = Core.pairing (Core.v (C i)) (Core.bit ∘ s) := by
      unfold signature
      rw [← eqC i]
      exact hdot s (C i)
    rw [heq]
    constructor
    · intro h
      exact h (C i) hi.le (hC i).2.1
    · intro h F hF hEven
      rw [← hi] at hF
      rcases (hC i).2.2.1 F hF hEven with h0 | h1
      · simp [h0, Core.dot_v]
      · exact h1 ▸ h
  have sig_of_same (s t : M) (h : same s t) : signature s = signature t := by
    funext i
    have hz : signature s i = 0 ↔ signature t i = 0 :=
      (cycle_query s i).symm.trans (h _ (hwC i) ▸ cycle_query t i)
    obtain ⟨a, ha⟩ := Core.bit_surj (signature s i)
    obtain ⟨a', ha'⟩ := Core.bit_surj (signature t i)
    cases a <;> cases a' <;> first | exact ha.symm.trans ha' | simp [← ha, ← ha', Core.bit] at hz
  have same_of_sig (s t : M) (h : signature s = signature t) : same s t := by
    have all_dot (F : Finset ↥E) (hF : F ∈ small) :
        Core.pairing (Core.v F) (Core.bit ∘ s) = Core.pairing (Core.v F) (Core.bit ∘ t) := by
      let x : Rank.span small := ⟨Rank.vec F, Submodule.subset_span ⟨F, hF, rfl⟩⟩
      let φ (u : M) := (Rank.dot (Core.bit ∘ u)).comp (Rank.span small).subtype
      have hbasis (i : Fin k) : φ s (b i) = φ t (b i) := congrFun h i
      have hx : φ s x = φ t x := by
        rw [← b.sum_repr x]
        simp only [map_sum, LinearMap.map_smul, hbasis]
      rw [← hdot, ← hdot]
      exact hx
    intro A hA
    rw [hcount, hcount, Core.counts_eq_iff, Core.characterization l r hn, Core.characterization l r hn]
    have hh F (hF : F ⊆ Core.edges l r A) (hEven : Cycles.IsEven l r F) : F ∈ small :=
      (hsmall F).2 ⟨(Finset.card_le_card (support_subset l r F A hF)).trans hA, hEven⟩
    constructor
    · intro h0 F hF hEven
      rw [← all_dot F (hh F hF hEven)]
      exact h0 F hF hEven
    · intro h0 F hF hEven
      rw [all_dot F (hh F hF hEven)]
      exact h0 F hF hEven
  have realize (z : Fin k → ZMod 2) : ∃ s : M, signature s = z := by
    obtain ⟨v, hv⟩ := Rank.realize b z
    choose s hs using fun e => Core.bit_surj (v e)
    have hv' : Core.bit ∘ s = v := funext hs
    exact ⟨s, funext fun i => by simpa only [signature, hv'] using hv i⟩
  constructor
  · rintro ⟨ask, hwask, hdet⟩
    choose sign hsign using realize
    rw [hcard]
    refine Trace.lower ask count ?_ sign ?_
    · intro s t A hst
      rw [hcount, hcount] at hst ⊢
      apply (Core.counts_eq_iff l r s t A).2
      simpa only [← Nat.pos_iff_ne_zero, Finset.card_pos] using hst
    · intro a b hab
      exact (hsign a).symm.trans ((sig_of_same _ _ (hdet _ _ hab)).trans (hsign b))
  · intro h
    rw [hcard] at h
    have hkd : k ≤ d := (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).1 h
    let ask (i : Fin d) : Finset V := if hi : i.val < k then Cycles.verts l r (C ⟨i.val, hi⟩) else ∅
    refine ⟨ask, ?_, ?_⟩
    · intro i
      by_cases hi : i.val < k <;> simp [ask, hi, hwC]
    · intro s t he
      apply same_of_sig
      funext i
      have eq := he (Fin.castLE hkd i)
      have eq' : count s (Cycles.verts l r (C i)) = count t (Cycles.verts l r (C i)) := by
        simpa [ask, i.isLt] using eq
      have hz : signature s i = 0 ↔ signature t i = 0 :=
        (cycle_query s i).symm.trans (eq' ▸ cycle_query t i)
      obtain ⟨a, ha⟩ := Core.bit_surj (signature s i)
      obtain ⟨a', ha'⟩ := Core.bit_surj (signature t i)
      cases a <;> cases a' <;> first | exact ha.symm.trans ha' | simp [← ha, ← ha', Core.bit] at hz
