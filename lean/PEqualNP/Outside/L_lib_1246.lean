import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.ByContra

namespace PEqualNP.Outside.L_lib_1246

open scoped BigOperators

private def named {n m : Nat} (a b c d : Fin m → Finset (Fin n))
    (lost last : Finset (Fin n)) (js : List (Fin m)) : Prop :=
  List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
      a j \ lost ⊆ u ∧ u ⊆ b j \ lost ∧ c j \ lost ⊆ v ∧ v ⊆ d j \ lost)
    js (last \ lost)

private def realizes (m k e n : Nat) : Prop :=
    ∃ (a b c d : Fin m → Finset (Fin n))
      (ends : Finset (Fin m) → Finset (Fin n)),
      Monotone ends ∧ ∀ lost : Finset (Fin n), lost.card ≤ e →
        (∀ js, named a b c d lost Finset.univ js ↔ js.length ≤ 1) ∧
        ∀ J : Finset (Fin m), J.card ≤ k → ∀ js,
          named a b c d lost (ends J) js ↔ js = [] ∨ ∃ i ∈ J, js = [i]

private def coverFree (m k e n : Nat) : Prop :=
  ∃ S : Fin m → Finset (Fin n), ∀ (i : Fin m) (J : Finset (Fin m)),
    J.card ≤ k → i ∉ J → e < ((S i) \ J.biUnion S).card

private theorem singleton {n m : Nat} {a b c d : Fin m → Finset (Fin n)}
    {lost y : Finset (Fin n)} {i : Fin m}
    (h : named a b c d lost Finset.univ [i]) :
    named a b c d lost y [i] ↔ (a i ∪ c i) \ lost ⊆ y \ lost := by
  classical
  change (∃ u v, True ∧ u ⊆ v ∧ v ⊆ y \ lost ∧
      a i \ lost ⊆ u ∧ u ⊆ b i \ lost ∧ c i \ lost ⊆ v ∧ v ⊆ d i \ lost) ↔ _
  constructor
  · rintro ⟨u, v, _, huv, hvy, hau, _, hcv, _⟩ x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx
    exact hx.1.elim (fun hxa => hvy (huv (hau (Finset.mem_sdiff.mpr ⟨hxa, hx.2⟩))))
      (fun hxc => hvy (hcv (Finset.mem_sdiff.mpr ⟨hxc, hx.2⟩)))
  · intro hs
    obtain ⟨u, v, _, huv, _, hau, hub, hcv, hvd⟩ := h
    refine ⟨a i \ lost, (a i ∪ c i) \ lost, trivial, ?_, hs, Finset.Subset.rfl,
      hau.trans hub, ?_, ?_⟩
    · intro x hx
      obtain ⟨ha, hl⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ ha, hl⟩
    · intro x hx
      obtain ⟨hc, hl⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hc, hl⟩
    · intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_union] at hx
      exact hx.1.elim (fun hxa => hvd (huv (hau (Finset.mem_sdiff.mpr ⟨hxa, hx.2⟩))))
        (fun hxc => hvd (hcv (Finset.mem_sdiff.mpr ⟨hxc, hx.2⟩)))

private theorem equivCover (m k e n : Nat) : realizes m k e n ↔ coverFree m k e n := by
  classical
  constructor
  · rintro ⟨a,b,c,d,ends,-,H⟩
    let S := fun i => a i ∪ c i
    refine ⟨S, ?_⟩
    intro i J hJ hi
    have hsup : J.biUnion S ⊆ ends J := by
      intro x hx
      obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
      have hh := H ∅ (by simp)
      have hv : named a b c d ∅ (ends J) [j] := (hh.2 J hJ [j]).mpr (Or.inr ⟨j,hj,rfl⟩)
      have hsub := (singleton ((hh.1 [j]).mpr (by simp))).mp hv
      simpa using hsub (by simpa [S] using hxj : x ∈ (a j ∪ c j) \ ∅)
    by_contra! hn
    let lost := S i \ J.biUnion S
    have hh := H lost hn
    have hx : named a b c d lost (ends J) [i] := by
      apply (singleton ((hh.1 [i]).mpr (by simp))).mpr
      intro x hx
      obtain ⟨hS, hL⟩ := Finset.mem_sdiff.mp hx
      refine Finset.mem_sdiff.mpr ⟨hsup ?_, hL⟩
      by_contra hU
      exact hL (Finset.mem_sdiff.mpr ⟨hS,hU⟩)
    have hc := (hh.2 J hJ [i]).mp hx
    simpa [hi] using hc
  · rintro ⟨S,H⟩
    let a : Fin m → Finset (Fin n) := fun _ => ∅
    let z : Fin m → Finset (Fin n) := fun _ => Finset.univ
    let ends : Finset (Fin m) → Finset (Fin n) := fun J => J.biUnion S
    refine ⟨a,a,S,z,ends,⟨?_,?_⟩⟩
    · intro A B h x hx
      obtain ⟨i, hi, hs⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_biUnion.mpr ⟨i,h hi,hs⟩
    · intro lost hl
      have hn (i : Fin m) : (S i \ lost).Nonempty := by
        have h := H i ∅ (by simp) (by simp)
        have hs : e < (S i).card := by simpa using h
        by_contra hc
        have he : S i \ lost = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
        have ht : S i ⊆ lost := Finset.sdiff_eq_empty_iff_subset.mp he
        exact (Nat.not_lt_of_ge ((Finset.card_le_card ht).trans hl)) hs
      have nil (y : Finset (Fin n)) : named a a S z lost y [] := trivial
      have one (i : Fin m) (y : Finset (Fin n)) :
          named a a S z lost y [i] ↔ S i \ lost ⊆ y \ lost := by
        change (∃ u v, True ∧ u ⊆ v ∧ v ⊆ y \ lost ∧
          a i \ lost ⊆ u ∧ u ⊆ a i \ lost ∧ S i \ lost ⊆ v ∧ v ⊆ z i \ lost) ↔ _
        constructor
        · rintro ⟨u,v,_,_,hvy,_,_,hsv,_⟩
          exact hsv.trans hvy
        · intro h
          exact ⟨∅, S i \ lost, trivial, by simp, h, by simp [a], by simp,
            Finset.Subset.rfl, by simp [z,Finset.subset_iff,Finset.mem_sdiff]⟩
      have none (i j : Fin m) (js : List (Fin m)) (y : Finset (Fin n)) :
          ¬ named a a S z lost y (i :: j :: js) := by
        rintro ⟨u,v,⟨u',v',_,_,hvu,_,_,hs,_⟩,_,_,_,hu,_⟩
        obtain ⟨x,hx⟩ := hn j
        have hxu := hvu (hs hx)
        simpa [a] using hu hxu
      constructor
      · intro js
        rcases js with _ | ⟨i, _ | ⟨j, js⟩⟩
        · simp [nil]
        · simp [one, Finset.subset_iff, Finset.mem_sdiff]
        · simpa using none i j js Finset.univ
      · intro J hJ js
        rcases js with _ | ⟨i, _ | ⟨j, js⟩⟩
        · simp [nil]
        · rw [one]
          simp only [List.cons_ne_nil, List.cons.injEq, and_true, false_or]
          constructor
          · intro hi
            refine ⟨i, ?_, rfl⟩
            by_contra hj
            have h := H i J hJ hj
            have hsub : S i \ J.biUnion S ⊆ lost := by
              intro x hx
              obtain ⟨hS,hU⟩ := Finset.mem_sdiff.mp hx
              by_contra hxL
              exact hU (Finset.mem_sdiff.mp (hi (Finset.mem_sdiff.mpr ⟨hS,hxL⟩))).1
            exact (Nat.not_lt_of_ge ((Finset.card_le_card hsub).trans hl)) h
          · rintro ⟨j,hj,heq⟩
            subst j
            intro x hx
            obtain ⟨hS,hL⟩ := Finset.mem_sdiff.mp hx
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨i,hj,hS⟩,hL⟩
        · simp [none]


private theorem singletonWidth {m n : Nat} (hm : 2 ≤ m) :
    coverFree m 1 0 n ↔ m ≤ n.choose (n/2) := by
  classical
  constructor
  · rintro ⟨S,H⟩
    have horder (i j : Fin m) (hij : i ≠ j) : ¬ S i ⊆ S j := by
      have h := H i {j} (by simp) (by simpa using hij)
      intro hsub
      simpa [Finset.sdiff_eq_empty_iff_subset.mpr hsub] using h
    have hinj : Function.Injective S := by
      intro i j h
      by_contra hn
      exact horder i j hn (h ▸ Finset.Subset.rfl)
    let F := Finset.univ.image S
    have hcard : F.card = m := by
      simp [F, Finset.card_image_of_injective _ hinj]
    have ha : IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n))) := by
      intro A hA B hB hne hab
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
      exact horder i j (fun h => hne (congrArg S h)) hab
    simpa [hcard] using ha.sperner
  · intro h
    let F := (Finset.univ : Finset (Fin n)).powersetCard (n/2)
    have hcard : m ≤ Fintype.card F := by
      simpa [F, Finset.card_powersetCard] using h
    let f : Fin m ↪ F := Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hcard))
    let S : Fin m → Finset (Fin n) := fun i => (f i).val
    have hS (i : Fin m) : (S i).card = n/2 :=
      (Finset.mem_powersetCard.mp (f i).property).2
    have horder (i j : Fin m) (hij : i ≠ j) : ¬ S i ⊆ S j := by
      intro hsub
      have hEq := Finset.eq_of_subset_of_card_le hsub (by rw [hS,hS])
      exact hij (f.injective (Subtype.ext hEq))
    refine ⟨S, ?_⟩
    intro i J hJ hi
    have hsub : ¬ S i ⊆ J.biUnion S := by
      rcases Finset.card_le_one.mp hJ with R
      by_cases he : J = ∅
      · have exj : ∃ j : Fin m, j ≠ i := by
          let i0 : Fin m := ⟨0, by omega⟩
          let i1 : Fin m := ⟨1, by omega⟩
          by_cases hh : i0 = i
          · exact ⟨i1, fun h => by have eq := congrArg Fin.val (h.trans hh.symm); simp [i0,i1] at eq⟩
          · exact ⟨i0, hh⟩
        obtain ⟨j,hj⟩ := exj
        intro H
        exact horder i j (Ne.symm hj) (by simpa [he] using H.trans (show J.biUnion S ⊆ S j from by simp [he]))
      · obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr he
        have hEq : J = {j} := by
          ext x
          simp only [Finset.mem_singleton]
          exact ⟨fun hx => R x hx j hj, fun hx => hx ▸ hj⟩
        exact fun hs => horder i j (by simpa [hEq] using hi) (by simpa [hEq] using hs)
    exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr
      (mt Finset.sdiff_eq_empty_iff_subset.mp hsub))


private theorem construction {m k e p s L : Nat} (hp : Nat.Prime p) (hs : 1 ≤ s)
    (hL : L ≤ p) (hm : m ≤ p^s) (hke : k*(s-1)+e < L) :
    coverFree m k e (p*L) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let t : Fin L ↪ ZMod p :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa [ZMod.card] using hL))
  let A : Fin m ↪ (Fin s → ZMod p) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa [ZMod.card] using hm))
  let U : (Fin L × ZMod p) ↪ Fin (p*L) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simp [ZMod.card,Nat.mul_comm]))
  let Q (i : Fin m) : Polynomial (ZMod p) :=
    ∑ r : Fin s, Polynomial.monomial r.val (A i r)
  have hcoeff (i : Fin m) (r : Fin s) : (Q i).coeff r.val = A i r := by
    classical
    dsimp only [Q]
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single r]
    · simp
    · intro r' _ h
      exact Polynomial.coeff_monomial_of_ne _ (fun hval => h (Fin.ext hval.symm))
    · simp
  have hQi : Function.Injective Q := by
    intro i j h
    apply A.injective
    funext r
    simpa only [hcoeff] using congrArg (fun q : Polynomial (ZMod p) => q.coeff r.val) h
  have hdeg (i : Fin m) : (Q i).natDegree ≤ s-1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro r _
    exact
      (Polynomial.natDegree_monomial_le _).trans (by have := r.isLt; omega)
  let G (i : Fin m) : Fin L ↪ Fin (p*L) :=
    ⟨fun x => U (x, (Q i).eval (t x)), fun _ _ h => congrArg Prod.fst (U.injective h)⟩
  let S (i : Fin m) := Finset.univ.map (G i)
  have hS (i : Fin m) : (S i).card = L := by simp [S]
  refine ⟨S, ?_⟩
  intro i J hJ hi
  have hpair (j : Fin m) (hj : j ∈ J) : ((S i) ∩ S j).card ≤ s-1 := by
    let C := (Finset.univ : Finset (Fin L)).filter (fun x => (Q i).eval (t x) = (Q j).eval (t x))
    have hsub : S i ∩ S j ⊆ C.map (G i) := by
      intro y hy
      obtain ⟨a,_,ha⟩ := Finset.mem_map.mp (Finset.mem_inter.mp hy).1
      obtain ⟨b,_,hb⟩ := Finset.mem_map.mp (Finset.mem_inter.mp hy).2
      have h : (a,(Q i).eval (t a)) = (b,(Q j).eval (t b)) := U.injective (ha.trans hb.symm)
      have hab : a = b := congrArg Prod.fst h
      subst b
      exact Finset.mem_map.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg Prod.snd h⟩,ha⟩
    have hn : Q i - Q j ≠ 0 :=
      sub_ne_zero.mpr (fun he => hi (hQi he ▸ hj))
    have hroots : (C.map t).val ⊆ (Q i - Q j).roots := by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp (Finset.mem_def.mpr hx)
      rw [Polynomial.mem_roots hn, Polynomial.IsRoot.def, Polynomial.eval_sub, sub_eq_zero]
      exact (Finset.mem_filter.mp ha).2
    calc
      ((S i) ∩ S j).card ≤ (C.map (G i)).card := Finset.card_le_card hsub
      _ = (C.map t).card := by simp
      _ ≤ (Q i - Q j).natDegree := Polynomial.card_le_degree_of_subset_roots hroots
      _ ≤ s-1 := by simpa using Polynomial.natDegree_sub_le_of_le (hdeg i) (hdeg j)
  have hI : (S i ∩ J.biUnion S).card ≤ k*(s-1) := by
    have sub : S i ∩ J.biUnion S ⊆ J.biUnion (fun j => S i ∩ S j) := by
      intro x hx
      obtain ⟨ha,hb⟩ := Finset.mem_inter.mp hx
      obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp hb
      exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_inter.mpr ⟨ha,hxj⟩⟩
    exact (Finset.card_le_card sub).trans
      ((Finset.card_biUnion_le_card_mul _ _ _ hpair).trans (Nat.mul_le_mul_right _ hJ))
  have hh := Finset.card_sdiff_add_card_inter (S i) (J.biUnion S)
  rw [hS] at hh
  omega

private theorem decEqFin (n : Nat) :
    (fun a b : Fin n => Classical.propDecidable (a = b)) = instDecidableEqFin n := by
  funext a b
  exact Subsingleton.elim _ _

private theorem dif (n : Nat) (s t : Finset (Fin n)) :
    @SDiff.sdiff _ (@Finset.instSDiff _ (fun a b => Classical.propDecidable (a = b))) s t =
      s \ t := by
  rw [decEqFin n]

private theorem uni (n : Nat) {α : Type} (s : Finset α) (t : α → Finset (Fin n)) :
    @Finset.biUnion _ _ (fun a b => Classical.propDecidable (a = b)) s t =
      s.biUnion t := by
  rw [decEqFin n]

end PEqualNP.Outside.L_lib_1246

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_lib_1246 : (
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let named := fun (n m : Nat) (a b c d : Fin m → Finset (Fin n))
    (lost last : Finset (Fin n)) (js : List (Fin m)) =>
  List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
      a j \ lost ⊆ u ∧ u ⊆ b j \ lost ∧ c j \ lost ⊆ v ∧ v ⊆ d j \ lost)
    js (last \ lost)
∀ (m k e : Nat),
  let realizes := fun n =>
    ∃ (a b c d : Fin m → Finset (Fin n))
      (ends : Finset (Fin m) → Finset (Fin n)),
      Monotone ends ∧ ∀ lost : Finset (Fin n), lost.card ≤ e →
        (∀ js, named n m a b c d lost Finset.univ js ↔ js.length ≤ 1) ∧
        ∀ J : Finset (Fin m), J.card ≤ k → ∀ js,
          named n m a b c d lost (ends J) js ↔ js = [] ∨ ∃ i ∈ J, js = [i]
  (∀ n, realizes n ↔ ∃ S : Fin m → Finset (Fin n),
    ∀ (i : Fin m) (J : Finset (Fin m)), J.card ≤ k → i ∉ J →
      e < ((S i) \ J.biUnion S).card) ∧
  ((2 ≤ m ∧ k = 1 ∧ e = 0) → ∀ n, realizes n ↔ m ≤ Nat.choose n (n/2)) ∧
  ∀ (p s L : Nat), Nat.Prime p → 1 ≤ s → L ≤ p → m ≤ p^s →
    k*(s-1)+e < L → realizes (p*L)
) := by
  intro nm m k e R
  constructor
  · intro n
    simpa only [R, nm, PEqualNP.Outside.L_lib_1246.dif, PEqualNP.Outside.L_lib_1246.uni, PEqualNP.Outside.L_lib_1246.realizes,
      PEqualNP.Outside.L_lib_1246.named, PEqualNP.Outside.L_lib_1246.coverFree] using
      PEqualNP.Outside.L_lib_1246.equivCover m k e n
  · constructor
    · rintro ⟨hm,rfl,rfl⟩ n
      simpa only [R, nm, PEqualNP.Outside.L_lib_1246.dif, PEqualNP.Outside.L_lib_1246.uni, PEqualNP.Outside.L_lib_1246.realizes,
        PEqualNP.Outside.L_lib_1246.named] using
        (PEqualNP.Outside.L_lib_1246.equivCover m 1 0 n).trans
          (PEqualNP.Outside.L_lib_1246.singletonWidth hm)
    · intro p s L hp hs hL hm hke
      simpa only [R, nm, PEqualNP.Outside.L_lib_1246.dif, PEqualNP.Outside.L_lib_1246.uni, PEqualNP.Outside.L_lib_1246.realizes,
        PEqualNP.Outside.L_lib_1246.named] using
        (PEqualNP.Outside.L_lib_1246.equivCover m k e _).mpr
          (PEqualNP.Outside.L_lib_1246.construction hp hs hL hm hke)
