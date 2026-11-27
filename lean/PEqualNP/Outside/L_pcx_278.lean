import Mathlib
import PEqualNP.Defs

open PEqualNP.ProofComplexity
open scoped BigOperators

namespace PEqualNP.Outside.L_pcx_278_aux

private def pcx278Inr {R : Type} {a : ℕ} : Literal (Fin a) ↪ Literal (Sum R (Fin a)) :=
  ⟨fun l => (Sum.inr l.1, l.2), by
    rintro ⟨i,s⟩ ⟨j,t⟩ h
    simp_all⟩

private noncomputable def pcx278Hidden {R : Type} {a : ℕ}
    (C : Clause (Sum R (Fin a))) : Clause (Fin a) := by
  classical
  exact Finset.univ.filter fun l => pcx278Inr l ∈ C

private theorem pcx278MemHidden {R : Type} {a : ℕ} (C : Clause (Sum R (Fin a)))
    (l : Literal (Fin a)) : l ∈ pcx278Hidden C ↔ pcx278Inr l ∈ C := by
  classical
  simp [pcx278Hidden]

private noncomputable def pcx278Raw {R : Type} {a : ℕ}
    (C : Clause (Sum R (Fin a))) : Clause (Sum R (Fin a)) := by
  classical
  exact C.filter fun l => ∃ r : R, l.1 = Sum.inl r

private theorem pcx278Partition {R : Type} {a : ℕ} (C : Clause (Sum R (Fin a))) :
    (pcx278Raw C).card + (pcx278Hidden C).card = C.card := by
  classical
  have hdis : Disjoint (pcx278Raw C) ((pcx278Hidden C).map pcx278Inr) := by
    rw [Finset.disjoint_left]
    intro l hl hr
    obtain ⟨r, hre⟩ := (Finset.mem_filter.mp hl).2
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hr
    cases hre
  have heq : pcx278Raw C ∪ (pcx278Hidden C).map pcx278Inr = C := by
    ext l
    constructor
    · intro hl
      rcases Finset.mem_union.mp hl with hl | hl
      · exact (Finset.mem_filter.mp hl).1
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hl
        exact (pcx278MemHidden C j).1 hj
    · rintro hl
      rcases l with ⟨r|i,s⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hl,r,rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨(i,s),(pcx278MemHidden C (i,s)).2 hl,rfl⟩)
  simpa using (Finset.card_union_of_disjoint hdis).symm.trans (congrArg Finset.card heq)

private theorem pcx278Layers (ι : Type) (G : Finset ι) (v : ι → ℕ) (W : ℕ) :
    (∑ C ∈ G, (W - v C)) = ∑ j ∈ Finset.range W, (G.filter fun C => v C ≤ j).card := by
  induction W with
  | zero => simp
  | succ W ih =>
    rw [Finset.sum_range_succ, Finset.card_filter, ← ih, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro C _
    split_ifs <;> omega

private theorem pcx278Weighted (f : ℕ → ℕ) (W : ℕ) :
    (∑ j ∈ Finset.range W, ∑ q ∈ Finset.range (j+1), f q) =
      ∑ q ∈ Finset.range W, (W-q) * f q := by
  induction W with
  | zero => simp
  | succ W ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ f]
    rw [Finset.sum_range_succ (fun q => (W+1-q) * f q)]
    simp only [Nat.add_sub_self_left, one_mul]
    rw [← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    have hq' := Finset.mem_range.mp hq
    have he : W + 1 - q = (W - q) + 1 := by omega
    rw [he, Nat.add_mul, one_mul]

set_option maxHeartbeats 1000000 in
private theorem pcx278Core {R B : Type} [Fintype B] (r : B ↪ R) (a W : ℕ)
    (F : Finset (Clause (Sum R (Fin a)))) (hW : ∀ C ∈ F, C.card ≤ W)
    (T : R → Bool) (hbad : ¬ ∃ z : Fin a → Bool, Satisfies (Sum.elim T z) (↑F : Set _))
    (hgood : ∀ b : B, ∃ (T' : R → Bool) (z : Fin a → Bool),
      (∀ v, v ≠ r b → T' v = T v) ∧ Satisfies (Sum.elim T' z) (↑F : Set _))
    (hdim : ∀ G : Finset (Clause (Fin a)),
      (∀ C ∈ G, ∃ z : Fin a → Bool, (¬ ∃ l ∈ C, z l.1 = l.2) ∧
        ∀ D ∈ G, D ≠ C → ∃ l ∈ D, z l.1 = l.2) →
      ∀ j : ℕ, (G.filter fun C => C.card ≤ j).card ≤ ∑ q ∈ Finset.range (j+1), Nat.choose a q) :
    Fintype.card B ≤ ∑ j ∈ Finset.range W, (W-j) * Nat.choose a j := by
  classical
  let A := F.filter fun C => ∀ v : R, ∀ s : Bool, (Sum.inl v,s) ∈ C → T v ≠ s
  let G₀ := A.image pcx278Hidden
  let unsat : Finset (Clause (Fin a)) → Prop := fun G => ¬ ∃ z : Fin a → Bool, ∀ C ∈ G, ClauseSat z C
  have h₀ : unsat G₀ := by
    rintro ⟨z, hz⟩
    apply hbad
    refine ⟨z, ?_⟩
    intro C hC
    change C ∈ F at hC
    by_cases hC' : C ∈ A
    · obtain ⟨l, hl, he⟩ := hz _ (Finset.mem_image_of_mem _ hC')
      exact ⟨pcx278Inr l, (pcx278MemHidden _ _).1 hl, he⟩
    · have hex : ∃ (v : R) (s : Bool), (Sum.inl v,s) ∈ C ∧ T v = s := by
        simpa only [A, Finset.mem_filter, hC, true_and, not_forall, not_imp, not_not, exists_prop] using hC'
      obtain ⟨v, s, hs, hv⟩ := hex
      exact ⟨(Sum.inl v,s), hs, hv⟩
  let bad := G₀.powerset.filter unsat
  obtain ⟨G, hG, hmin⟩ := Finset.exists_min_image bad Finset.card
    ⟨G₀, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), h₀⟩⟩
  have hGG₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hG).1
  have hunsat : unsat G := (Finset.mem_filter.mp hG).2
  have hpriv : ∀ C ∈ G, ∃ z : Fin a → Bool, (¬ ∃ l ∈ C, z l.1 = l.2) ∧
      ∀ D ∈ G, D ≠ C → ∃ l ∈ D, z l.1 = l.2 := by
    intro C hC
    have hnot : G.erase C ∉ bad := by
      intro he
      have hn := hmin _ he
      have hl := Finset.card_erase_lt_of_mem hC
      omega
    have hs := (Finset.erase_subset C G).trans hGG₀
    have hh : ¬ unsat (G.erase C) := fun hz => hnot (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs, hz⟩)
    obtain ⟨z, hz⟩ := not_not.mp hh
    refine ⟨z, ?_, fun D hD hne => hz D (Finset.mem_erase.mpr ⟨hne,hD⟩)⟩
    intro hc
    apply hunsat
    refine ⟨z, fun D hD => ?_⟩
    by_cases he : D = C
    · subst D; exact hc
    · exact hz D (Finset.mem_erase.mpr ⟨he,hD⟩)
  have hlift : ∀ C : ↥G, ∃ D ∈ A, pcx278Hidden D = C.val :=
    fun C => Finset.mem_image.mp (hGG₀ C.property)
  choose lift hliftA hliftEq using hlift
  let raw (C : Clause (Fin a)) := if h : C ∈ G then pcx278Raw (lift ⟨C,h⟩) else ∅
  let L := G.biUnion raw
  have hhit : ∀ b : B, ∃ s : Bool, (Sum.inl (r b),s) ∈ L := by
    intro b
    obtain ⟨T', z, hT', hz⟩ := hgood b
    have hno : ¬ ∀ C ∈ G, ClauseSat z C := fun hh => hunsat ⟨z, hh⟩
    obtain ⟨C, hC, hfail⟩ := by simpa only [not_forall, not_imp] using hno
    let D := lift ⟨C,hC⟩
    have hDA : D ∈ A := hliftA ⟨C,hC⟩
    have hDF : D ∈ F := (Finset.mem_filter.mp hDA).1
    obtain ⟨⟨v|i,s⟩, hm, hv⟩ := hz D (Finset.mem_coe.mpr hDF)
    · have he : v = r b := by
        by_contra hne
        exact (Finset.mem_filter.mp hDA).2 v s hm ((hT' v hne).symm.trans hv)
      subst v
      exact ⟨s, Finset.mem_biUnion.mpr ⟨C,hC,by
        simpa [raw,hC,pcx278Raw] using hm⟩⟩
    · apply False.elim (hfail ?_)
      refine ⟨(i,s), ?_, hv⟩
      have hEq : pcx278Hidden D = C := hliftEq ⟨C,hC⟩
      rw [← hEq]
      exact (pcx278MemHidden D (i,s)).2 hm
  choose s hs using hhit
  have hcard : Fintype.card B ≤ L.card := by
    rw [← Fintype.card_coe]
    apply Fintype.card_le_of_injective (fun b => (⟨(Sum.inl (r b),s b),hs b⟩ : ↥L))
    intro b b' he
    apply r.injective
    exact Sum.inl.inj (congrArg (fun q : ↥L => q.val.1) he)
  calc
    Fintype.card B ≤ L.card := hcard
    _ ≤ ∑ C ∈ G, (raw C).card := Finset.card_biUnion_le
    _ ≤ ∑ C ∈ G, (W-C.card) := by
      apply Finset.sum_le_sum
      intro C hC
      have he := pcx278Partition (lift ⟨C,hC⟩)
      rw [hliftEq ⟨C,hC⟩] at he
      have hh := hW _ (Finset.mem_filter.mp (hliftA ⟨C,hC⟩)).1
      change _ + C.card = _ at he
      simp only [raw, dite_eq_left hC]
      omega
    _ = ∑ j ∈ Finset.range W, (G.filter fun C => C.card ≤ j).card := pcx278Layers _ _ _ _
    _ ≤ ∑ j ∈ Finset.range W, ∑ q ∈ Finset.range (j+1), Nat.choose a q :=
      Finset.sum_le_sum fun j _ => hdim G hpriv j
    _ = _ := pcx278Weighted _ _

private abbrev pcx278RawType (n w : ℕ) := Fin n × (Fin (w+1) → Bool)

private def pcx278Accept (n w : ℕ) (hn : 0 < n) (T : pcx278RawType n w → Bool) : Prop :=
  ∃ x : Fin n → Bool, ∀ i : Fin n,
    T (i, fun j : Fin (w+1) => x ⟨(i.val+j.val)%n, Nat.mod_lt _ hn⟩) = true

private def pcx278Enc (n w : ℕ) (hn : 0 < n) (a W : ℕ)
    (F : Finset (Clause (Sum (pcx278RawType n w) (Fin a)))) : Prop :=
  (∀ C ∈ F, C.card ≤ W) ∧ ∀ T : pcx278RawType n w → Bool,
    pcx278Accept n w hn T ↔ ∃ z : Fin a → Bool, Satisfies (Sum.elim T z) (↑F : Set _)

private noncomputable def pcx278Enable {R : Type} (T : R → Bool) (r : R) : R → Bool := by
  classical
  exact fun v => if v = r then true else T v

private theorem pcx278Slice (n w m : ℕ) (hn : 0 < n) (hmn : m ≤ n) (hmw : m ≤ w+1) :
    ∃ (r : (Fin m → Bool) ↪ pcx278RawType n w) (T : pcx278RawType n w → Bool),
      (¬ pcx278Accept n w hn T) ∧ ∀ b, pcx278Accept n w hn (pcx278Enable T (r b)) := by
  classical
  let i₀ : Fin n := ⟨0,hn⟩
  let x (b : Fin m → Bool) (i : Fin n) := if h : i.val < m then b ⟨i.val,h⟩ else false
  let p (b : Fin m → Bool) := fun j : Fin (w+1) =>
    x b ⟨(i₀.val+j.val)%n, Nat.mod_lt _ hn⟩
  let r : (Fin m → Bool) ↪ pcx278RawType n w := ⟨fun b => (i₀,p b), by
    intro b c he
    funext j
    let q : Fin (w+1) := ⟨j.val, j.isLt.trans_le hmw⟩
    have hp := congrFun (congrArg Prod.snd he) q
    have hmod : (i₀.val+q.val)%n = j.val := by
      change (0+j.val)%n = j.val
      rw [Nat.zero_add, Nat.mod_eq_of_lt (j.isLt.trans_le hmn)]
    simpa [p, x, hmod, j.isLt] using hp⟩
  let T : pcx278RawType n w → Bool := fun v => if v.1 = i₀ then false else true
  refine ⟨r, T, ?_, ?_⟩
  · rintro ⟨y,hy⟩
    simpa [T] using hy i₀
  · intro b
    refine ⟨x b, fun i => ?_⟩
    by_cases hi : i = i₀
    · subst i
      change pcx278Enable T (r b) (r b) = true
      simp [pcx278Enable]
    · simp [pcx278Enable, T, hi]

private def pcx278Maj (a b c : Bool) : Bool := if a = b then a else c

private theorem pcx278MajPair (a b c s : Bool) :
    (a = s ∧ b = s) ∨ (a = s ∧ c = s) ∨ (b = s ∧ c = s) → pcx278Maj a b c = s := by
  cases a <;> cases b <;> cases c <;> cases s <;> decide

private theorem pcx278MajClosed {V : Type} (F : Finset (Clause V)) (hF : ∀ C ∈ F, C.card ≤ 2)
    (a b c : V → Bool) (ha : Satisfies a (↑F : Set _)) (hb : Satisfies b (↑F : Set _))
    (hc : Satisfies c (↑F : Set _)) : Satisfies (fun v => pcx278Maj (a v) (b v) (c v)) (↑F : Set _) := by
  classical
  intro C hC
  obtain ⟨l₁,h₁,e₁⟩ := ha C hC
  obtain ⟨l₂,h₂,e₂⟩ := hb C hC
  obtain ⟨l₃,h₃,e₃⟩ := hc C hC
  by_cases e₁₂ : l₁ = l₂
  · subst l₂
    exact ⟨l₁,h₁,pcx278MajPair _ _ _ _ (.inl ⟨e₁,e₂⟩)⟩
  by_cases e₁₃ : l₁ = l₃
  · subst l₃
    exact ⟨l₁,h₁,pcx278MajPair _ _ _ _ (.inr (.inl ⟨e₁,e₃⟩))⟩
  by_cases e₂₃ : l₂ = l₃
  · subst l₃
    exact ⟨l₂,h₂,pcx278MajPair _ _ _ _ (.inr (.inr ⟨e₂,e₃⟩))⟩
  have hs : ({l₁,l₂,l₃} : Finset _) ⊆ C := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl|rfl|rfl <;> assumption
  have hcard := Finset.card_le_card hs
  rw [Finset.card_triple_eq_three_iff.mpr ⟨e₁₂,e₁₃,e₂₃⟩] at hcard
  exact False.elim (by have := hF C hC; omega)

private theorem pcx278MajEnabled {R B : Type} (r : B ↪ R) (T : R → Bool) (b₀ b₁ b₂ : B)
    (h01 : b₀ ≠ b₁) (h02 : b₀ ≠ b₂) (h12 : b₁ ≠ b₂) (v : R) :
    pcx278Maj (pcx278Enable T (r b₀) v) (pcx278Enable T (r b₁) v) (pcx278Enable T (r b₂) v) = T v := by
  classical
  have ne {x y : B} (hne : x ≠ y) : r x ≠ r y := fun he => hne (r.injective he)
  apply pcx278MajPair
  by_cases h₀ : v = r b₀
  · right; right
    simp [pcx278Enable, h₀, ne h01, ne h02]
  by_cases h₁ : v = r b₁
  · right; left
    simp [pcx278Enable, h₁, ne h01.symm, ne h12]
  · left
    simp [pcx278Enable, h₀, h₁]

private theorem pcx278WidthTwo (n w : ℕ) (hn : 0 < n) :
    (∃ a F, pcx278Enc n w hn a 2 F) ↔ n = 1 ∨ w = 0 := by
  classical
  constructor
  · rintro ⟨a,F,hW,henc⟩
    by_contra hnw
    have hmn : 2 ≤ n := by omega
    have hmw : 2 ≤ w+1 := by omega
    obtain ⟨r,T,hbad,hgood⟩ := pcx278Slice n w 2 hn hmn hmw
    let b₀ : Fin 2 → Bool := fun _ => false
    let b₁ : Fin 2 → Bool := fun i => decide (i = 0)
    let b₂ : Fin 2 → Bool := fun i => decide (i = 1)
    have h01 : b₀ ≠ b₁ := fun h => by simpa [b₀,b₁] using congrFun h 0
    have h02 : b₀ ≠ b₂ := fun h => by simpa [b₀,b₂] using congrFun h 1
    have h12 : b₁ ≠ b₂ := fun h => by simpa [b₁,b₂] using congrFun h 0
    obtain ⟨z₀,hz₀⟩ := (henc _).mp (hgood b₀)
    obtain ⟨z₁,hz₁⟩ := (henc _).mp (hgood b₁)
    obtain ⟨z₂,hz₂⟩ := (henc _).mp (hgood b₂)
    let z := fun i => pcx278Maj (z₀ i) (z₁ i) (z₂ i)
    apply hbad ((henc T).mpr ⟨z, ?_⟩)
    have hm := pcx278MajClosed F hW _ _ _ hz₀ hz₁ hz₂
    convert hm using 1
    funext v
    rcases v with v|i
    · exact (pcx278MajEnabled r T b₀ b₁ b₂ h01 h02 h12 v).symm
    · rfl
  · intro hcase
    have hpat (x : Fin n → Bool) (i : Fin n) :
        (fun j : Fin (w+1) => x ⟨(i.val+j.val)%n, Nat.mod_lt _ hn⟩) = (fun _ => x i) := by
      funext j
      congr 1
      apply Fin.ext
      rcases hcase with h | h
      · have hi : i.val = 0 := by have := i.isLt; omega
        simp [h,hi,Nat.mod_one]
      · have hj : j.val = 0 := by have := j.isLt; omega
        simp [hj, Nat.mod_eq_of_lt i.isLt]
    let lit (i : Fin n) (b : Bool) : Literal (Sum (pcx278RawType n w) (Fin 0)) :=
      (Sum.inl (i,fun _ => b), true)
    let cl (i : Fin n) : Clause (Sum (pcx278RawType n w) (Fin 0)) := {lit i false, lit i true}
    let F := Finset.univ.image cl
    refine ⟨0,F,?_,fun T => ?_⟩
    · intro C hC
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hC
      exact Finset.card_le_two
    · constructor
      · rintro ⟨x,hx⟩
        refine ⟨Fin.elim0, fun C hC => ?_⟩
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hC)
        refine ⟨lit i (x i), ?_, ?_⟩
        · cases x i <;> simp [cl]
        · have hi := hx i
          rw [hpat] at hi
          exact hi
      · rintro ⟨z,hz⟩
        have hex (i : Fin n) : ∃ b : Bool, T (i,fun _ => b) = true := by
          obtain ⟨l,hl,hlt⟩ := hz (cl i) (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
          simp only [cl, Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl|rfl
          · exact ⟨false,hlt⟩
          · exact ⟨true,hlt⟩
        choose x hx using hex
        exact ⟨x, fun i => by rw [hpat]; exact hx i⟩

private abbrev Pcx278CubeFun (a : ℕ) := (Fin a → Bool) → ℚ

private def pcx278Supports (a j : ℕ) : Finset (Finset (Fin a)) :=
  (Finset.range (j + 1)).biUnion fun q => (Finset.univ : Finset (Fin a)).powersetCard q

private theorem pcx278Supports_mem {a j : ℕ} {S : Finset (Fin a)} :
    S ∈ pcx278Supports a j ↔ S.card ≤ j := by
  constructor
  · intro h
    obtain ⟨q, hq, hS⟩ := Finset.mem_biUnion.mp h
    rw [(Finset.mem_powersetCard.mp hS).2]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hq)
  · intro h
    exact Finset.mem_biUnion.mpr ⟨S.card, Finset.mem_range.mpr (Nat.lt_succ_of_le h),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩

private def pcx278Coord {a : ℕ} (i : Fin a) : Pcx278CubeFun a :=
  fun z => if z i = true then 1 else 0

-- On Boolean points, the squarefree monomial is the indicator that its support is all true.
private noncomputable def pcx278Monomial {a : ℕ} (S : Finset (Fin a)) : Pcx278CubeFun a := by
  classical
  exact fun z => if ∀ i ∈ S, z i = true then 1 else 0

private theorem pcx278Coord_mul_monomial {a : ℕ} (i : Fin a) (S : Finset (Fin a)) :
    pcx278Coord i * pcx278Monomial S = pcx278Monomial (insert i S) := by
  funext z
  simp only [Pi.mul_apply, pcx278Coord, pcx278Monomial, Finset.forall_mem_insert]
  by_cases hi : z i = true <;> by_cases hS : ∀ k ∈ S, z k = true <;> simp [hi, hS]

private noncomputable abbrev pcx278Span {a : ℕ} (j : ℕ) : Submodule ℚ (Pcx278CubeFun a) :=
  Submodule.span ℚ (Set.range (fun S : ↥(pcx278Supports a j) => pcx278Monomial S.val))

private theorem pcx278Monomial_mem {a j : ℕ} (S : Finset (Fin a)) (hS : S.card ≤ j) :
    pcx278Monomial S ∈ pcx278Span j :=
  Submodule.subset_span ⟨⟨S, pcx278Supports_mem.mpr hS⟩, rfl⟩

private theorem pcx278Span_mono {a m n : ℕ} (h : m ≤ n) :
    pcx278Span (a := a) m ≤ pcx278Span n := by
  apply Submodule.span_mono
  rintro _ ⟨S, rfl⟩
  exact ⟨⟨S.val, pcx278Supports_mem.mpr ((pcx278Supports_mem.mp S.property).trans h)⟩, rfl⟩

private theorem pcx278Span_coord_mul {a j : ℕ} (i : Fin a) {f : Pcx278CubeFun a}
    (hf : f ∈ pcx278Span j) : pcx278Coord i * f ∈ pcx278Span (j + 1) := by
  refine Submodule.span_induction (p := fun g _ => pcx278Coord i * g ∈ pcx278Span (j + 1))
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S, rfl⟩
    rw [pcx278Coord_mul_monomial]
    exact pcx278Monomial_mem _ ((Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ (pcx278Supports_mem.mp S.property)))
  · rw [mul_zero]
    exact Submodule.zero_mem _
  · intro g k _ _ hg hk
    rw [mul_add]
    exact Submodule.add_mem _ hg hk
  · intro c g _ hg
    have heq : pcx278Coord i * (c • g) = c • (pcx278Coord i * g) := by
      funext z
      change pcx278Coord i z * (c * g z) = c * (pcx278Coord i z * g z)
      exact mul_left_comm _ _ _
    rw [heq]
    exact Submodule.smul_mem _ c hg

private def pcx278Factor {a : ℕ} (l : Literal (Fin a)) : Pcx278CubeFun a :=
  fun z => if z l.1 = l.2 then 0 else 1

private theorem pcx278Factor_eq {a : ℕ} (l : Literal (Fin a)) :
    pcx278Factor l = if l.2 = true then 1 - pcx278Coord l.1 else pcx278Coord l.1 := by
  obtain ⟨i, b⟩ := l
  funext z
  cases b <;> cases hz : z i <;> simp [pcx278Factor, pcx278Coord, hz]

private def pcx278Indicator {a : ℕ} (C : Clause (Fin a)) : Pcx278CubeFun a :=
  ∏ l ∈ C, pcx278Factor l

private theorem pcx278Indicator_mem {a : ℕ} (C : Clause (Fin a)) :
    pcx278Indicator C ∈ pcx278Span C.card := by
  classical
  induction C using Finset.induction_on with
  | empty =>
    have hone : pcx278Monomial (∅ : Finset (Fin a)) = 1 := by
      funext z
      simp [pcx278Monomial]
    simpa only [hone, pcx278Indicator, Finset.prod_empty] using
      (pcx278Monomial_mem (j := (∅ : Clause (Fin a)).card) (∅ : Finset (Fin a)) (by simp))
  | @insert l C hl ih =>
    rw [Finset.card_insert_of_notMem hl, pcx278Indicator, Finset.prod_insert hl]
    change pcx278Factor l * pcx278Indicator C ∈ pcx278Span (C.card + 1)
    have hmul := pcx278Span_coord_mul l.1 ih
    by_cases hs : l.2 = true
    · rw [pcx278Factor_eq, ite_eq_left hs, sub_mul, one_mul]
      exact Submodule.sub_mem _ (pcx278Span_mono (Nat.le_succ C.card) ih) hmul
    · rw [pcx278Factor_eq, ite_eq_right hs]
      exact hmul

private theorem pcx278Indicator_one {a : ℕ} {C : Clause (Fin a)} {z : Fin a → Bool}
    (h : ¬ ∃ l ∈ C, z l.1 = l.2) : pcx278Indicator C z = 1 := by
  rw [pcx278Indicator, Finset.prod_apply]
  calc
    _ = ∏ _l ∈ C, (1 : ℚ) :=
      Finset.prod_congr rfl fun l hl => ite_eq_right (fun heq => h ⟨l, hl, heq⟩)
    _ = 1 := Finset.prod_const_one

private theorem pcx278Indicator_zero {a : ℕ} {C : Clause (Fin a)} {z : Fin a → Bool}
    (h : ∃ l ∈ C, z l.1 = l.2) : pcx278Indicator C z = 0 := by
  obtain ⟨l, hl, hz⟩ := h
  rw [pcx278Indicator, Finset.prod_apply]
  exact Finset.prod_eq_zero hl (ite_eq_left hz)

private theorem pcx278Dimension (a j : ℕ) (G : Finset (Clause (Fin a)))
    (hprivate : ∀ C ∈ G, ∃ z : Fin a → Bool,
      (¬ ∃ l ∈ C, z l.1 = l.2) ∧ ∀ D ∈ G, D ≠ C → ∃ l ∈ D, z l.1 = l.2) :
    (G.filter fun C => C.card ≤ j).card ≤ ∑ q ∈ Finset.range (j + 1), Nat.choose a q := by
  classical
  let H := G.filter fun C => C.card ≤ j
  have hli : LinearIndependent ℚ (fun C : ↥H => pcx278Indicator C.val) := by
    rw [linearIndependent_iff']
    intro s g hg C hC
    obtain ⟨z, hz, hother⟩ := hprivate C.val (Finset.mem_filter.mp C.property).1
    have heval : (∑ D ∈ s, g D * pcx278Indicator D.val z) = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
        congrArg (fun f : Pcx278CubeFun a => f z) hg
    have hzero : ∀ D ∈ s, D ≠ C → g D * pcx278Indicator D.val z = 0 := by
      intro D _ hDC
      have hsat := hother D.val (Finset.mem_filter.mp D.property).1
        (fun heq => hDC (Subtype.ext heq))
      rw [pcx278Indicator_zero hsat, mul_zero]
    rw [Finset.sum_eq_single_of_mem C hC hzero, pcx278Indicator_one hz, mul_one] at heval
    exact heval
  let v (C : ↥H) : pcx278Span (a := a) j :=
    ⟨pcx278Indicator C.val,
      pcx278Span_mono (Finset.mem_filter.mp C.property).2 (pcx278Indicator_mem C.val)⟩
  have hli' : LinearIndependent ℚ v :=
    LinearIndependent.of_comp (pcx278Span (a := a) j).subtype hli
  let : Module.Finite ℚ (pcx278Span (a := a) j) :=
    Module.Finite.span_of_finite ℚ
      (Set.finite_range fun S : ↥(pcx278Supports a j) => pcx278Monomial S.val)
  calc
    H.card = Fintype.card ↥H := (Fintype.card_coe H).symm
    _ ≤ Module.finrank ℚ (pcx278Span (a := a) j) := hli'.fintype_card_le_finrank
    _ ≤ Fintype.card ↥(pcx278Supports a j) :=
      finrank_range_le_card (R := ℚ) (fun S : ↥(pcx278Supports a j) => pcx278Monomial S.val)
    _ = (pcx278Supports a j).card := Fintype.card_coe _
    _ ≤ ∑ q ∈ Finset.range (j + 1), Nat.choose a q := by
      unfold pcx278Supports
      calc
        _ ≤ ∑ q ∈ Finset.range (j + 1), ((Finset.univ : Finset (Fin a)).powersetCard q).card :=
          Finset.card_biUnion_le
        _ = _ := by simp

private theorem pcx278Lower (n w : ℕ) (hn : 0 < n) (k a : ℕ)
    (F : Finset (Clause (Sum (pcx278RawType n w) (Fin a)))) (henc : pcx278Enc n w hn a (k+1) F) :
    2^(if n ≤ w+1 then n else w) ≤ ∑ j ∈ Finset.range (k+1), (k+1-j) * Nat.choose a j := by
  classical
  let d := if n ≤ w+1 then n else w
  have hd₁ : d ≤ n := by dsimp [d]; split_ifs <;> omega
  have hd₂ : d ≤ w+1 := by dsimp [d]; split_ifs <;> omega
  obtain ⟨r,T,hbad,hgood⟩ := pcx278Slice n w d hn hd₁ hd₂
  have hc := pcx278Core r a (k+1) F henc.1 T (fun h => hbad ((henc.2 T).2 h))
    (fun b => by
      obtain ⟨z,hz⟩ := (henc.2 _).1 (hgood b)
      exact ⟨pcx278Enable T (r b),z,fun v hv => by simp [pcx278Enable,hv],hz⟩)
    (fun G hG j => pcx278Dimension a j G hG)
  change 2^d ≤ _
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hc

private def pcx278ListSat {V : Type} (v : V → Bool) (L : List (Literal V)) : Prop :=
  ∃ l ∈ L, v l.1 = l.2

private theorem pcx278ListSat_nil {V : Type} (v : V → Bool) :
    ¬ pcx278ListSat v [] := by
  simp [pcx278ListSat]

private theorem pcx278ListSat_cons {V : Type} {v : V → Bool} {l : Literal V}
    {L : List (Literal V)} :
    pcx278ListSat v (l :: L) ↔ v l.1 = l.2 ∨ pcx278ListSat v L := by
  constructor
  · rintro ⟨a, ha, hv⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Or.inl hv
    · exact Or.inr ⟨a, ha, hv⟩
  · rintro (h | ⟨a, ha, hv⟩)
    · exact ⟨l, List.mem_cons_self, h⟩
    · exact ⟨a, List.mem_cons_of_mem _ ha, hv⟩

private theorem pcx278ListSat_ofFn {V : Type} {v : V → Bool} {d : ℕ}
    {f : Fin d → Literal V} :
    pcx278ListSat v (List.ofFn f) ↔ ∃ j, v (f j).1 = (f j).2 := by
  constructor
  · rintro ⟨a, ha, hv⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact ⟨j, hv⟩
  · rintro ⟨j, hj⟩
    exact ⟨f j, List.mem_ofFn.mpr ⟨j, rfl⟩, hj⟩

private theorem pcx278BoolFalse (b : Bool) : b = false ↔ ¬ b = true := by
  cases b <;> simp

-- Render an indexed family of signed lists as clauses, renaming only the auxiliary variables.
private theorem pcx278Render {R A I : Type} [Fintype A] [Fintype I]
    (width : ℕ) (L : I → List (Literal (Sum R A))) (hL : ∀ j, (L j).length ≤ width) :
    ∃ F : Finset (Clause (Sum R (Fin (Fintype.card A)))),
      (∀ C ∈ F, C.card ≤ width) ∧ ∀ T : R → Bool,
        (∃ s : A → Bool, ∀ j, pcx278ListSat (Sum.elim T s) (L j)) ↔
          ∃ z : Fin (Fintype.card A) → Bool, Satisfies (Sum.elim T z) (↑F : Set _) := by
  classical
  let e := Fintype.equivFin A
  let ren : Literal (Sum R A) → Literal (Sum R (Fin (Fintype.card A))) :=
    fun l => (Sum.map id e l.1, l.2)
  let C : I → Clause (Sum R (Fin (Fintype.card A))) := fun j => ((L j).map ren).toFinset
  refine ⟨Finset.univ.image C, ?_, ?_⟩
  · intro c hc
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
    exact ((L j).map ren).toFinset_card_le.trans (by simpa using hL j)
  intro T
  have sat (z : Fin (Fintype.card A) → Bool) (j : I) :
      ClauseSat (Sum.elim T z) (C j) ↔ pcx278ListSat (Sum.elim T (z ∘ e)) (L j) := by
    have eval (l : Literal (Sum R A)) :
        Sum.elim T z (ren l).1 = Sum.elim T (z ∘ e) l.1 := by
      rcases l with ⟨v, b⟩
      cases v <;> rfl
    constructor
    · rintro ⟨a, ha, hv⟩
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact ⟨l, hl, (eval l).symm.trans hv⟩
    · rintro ⟨l, hl, hv⟩
      exact ⟨ren l, List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, hl, rfl⟩),
        (eval l).trans hv⟩
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s ∘ e.symm, ?_⟩
    intro c hc
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
    apply (sat _ _).mpr
    have he : (s ∘ e.symm) ∘ e = s := by funext x; simp [Function.comp_def]
    simpa only [he] using hs j
  · rintro ⟨z, hz⟩
    exact ⟨z ∘ e, fun j => (sat z j).mp (hz (C j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))⟩

private abbrev pcx278Aux (H G : Type) (q : ℕ) := Sum H (Bool × (G × Fin q))

private abbrev pcx278Guard {R H G : Type} {q : ℕ} (s : G) (j : Fin q) :
    Sum R (pcx278Aux H G q) := .inr (.inr (true, s, j))

private abbrev pcx278Prefix {R H G : Type} {q : ℕ} (s : G) (j : Fin q) :
    Sum R (pcx278Aux H G q) := .inr (.inr (false, s, j))

private def pcx278AuxVal {H G : Type} {q : ℕ} (y : H → Bool)
    (g p : G → Fin q → Bool) : pcx278Aux H G q → Bool :=
  Sum.elim y fun b => if b.1 then g b.2.1 b.2.2 else p b.2.1 b.2.2

private def pcx278Chain {V G : Type} {q : ℕ} (hq : 0 < q) (g p : G → Fin q → V) :
    G × Option (Fin q) → List (Literal V)
  | (s, none) => [(p s ⟨q - 1, by omega⟩, true)]
  | (s, some j) => (p s j, false) :: (g s j, true) ::
      (if h : 0 < j.val then [(p s ⟨j.val - 1, by omega⟩, true)] else [])

private theorem pcx278Chain_width {V G : Type} {q : ℕ} (hq : 0 < q)
    (g p : G → Fin q → V) (a : G × Option (Fin q)) :
    (pcx278Chain hq g p a).length ≤ 3 := by
  rcases a with ⟨s, _ | j⟩
  · simp [pcx278Chain]
  · by_cases h : 0 < j.val <;> simp [pcx278Chain, h]

private theorem pcx278Chain_sound {V G : Type} {q : ℕ} (hq : 0 < q)
    (g p : G → Fin q → V) (v : V → Bool)
    (h : ∀ a, pcx278ListSat v (pcx278Chain hq g p a)) (s : G) :
    ∃ j, v (g s j) = true := by
  have descend (j : Fin q) : v (p s j) = true → ∃ r, v (g s r) = true := by
    refine Fin.strong_induction_on
      (motive := fun a => v (p s a) = true → ∃ r, v (g s r) = true) ?_ j
    intro j ih hp
    have hj := h (s, some j)
    by_cases hjpos : 0 < j.val
    · simp only [pcx278Chain, dite_eq_left hjpos, pcx278ListSat_cons, hp,
        Bool.true_eq_false, false_or, pcx278ListSat_nil, or_false] at hj
      rcases hj with hg | hp'
      · exact ⟨j, hg⟩
      · exact ih ⟨j.val - 1, by omega⟩ (show j.val - 1 < j.val by omega) hp'
    · simp only [pcx278Chain, dite_eq_right hjpos, pcx278ListSat_cons, hp,
        Bool.true_eq_false, false_or, pcx278ListSat_nil, or_false] at hj
      exact ⟨j, hj⟩
  apply descend ⟨q - 1, by omega⟩
  simpa [pcx278Chain, pcx278ListSat] using h (s, none)

private theorem pcx278Chain_complete {V G : Type} {q : ℕ} (hq : 0 < q)
    (g p : G → Fin q → V) (v : V → Bool)
    (h : ∀ s, ∃ r, v (g s r) = true)
    (hp : ∀ s j, v (p s j) = true ↔ ∃ r : Fin q, r.val ≤ j.val ∧ v (g s r) = true) :
    ∀ a, pcx278ListSat v (pcx278Chain hq g p a) := by
  rintro ⟨s, _ | j⟩
  · obtain ⟨r, hr⟩ := h s
    have he := (hp s ⟨q - 1, by omega⟩).mpr ⟨r, by change r.val ≤ q - 1; omega, hr⟩
    simpa [pcx278Chain, pcx278ListSat] using he
  · simp only [pcx278Chain, pcx278ListSat_cons]
    by_cases hg : v (p s j) = true
    · obtain ⟨r, hr, hval⟩ := (hp s j).mp hg
      by_cases he : r = j
      · exact Or.inr (Or.inl (he ▸ hval))
      · have hne : r.val ≠ j.val := fun h => he (Fin.ext h)
        have hjpos : 0 < j.val := by omega
        rw [dite_eq_left hjpos]
        refine Or.inr (Or.inr ?_)
        have he' := (hp s ⟨j.val - 1, by omega⟩).mpr ⟨r, by change r.val ≤ j.val - 1; omega, hval⟩
        simpa [pcx278ListSat] using he'
    · exact Or.inl ((pcx278BoolFalse _).mpr hg)

private def pcx278Row {R H G D : Type} {q k : ℕ}
    (group : D → Fin k → G) (key : D → (Fin k → Fin q) → R)
    (a : D × (Fin k → Fin q)) : List (Literal (Sum R (pcx278Aux H G q))) :=
  (Sum.inl (key a.1 a.2), true) ::
    List.ofFn (fun t : Fin k => (pcx278Guard (group a.1 t) (a.2 t), false))

-- Compile shared guard groups, consistency clauses, and permission clauses.
private theorem pcx278Compile {R H G D I : Type} [Fintype H] [Fintype G] [Fintype D]
    [Fintype I] {q k : ℕ} (hq : 0 < q) (hk : 2 ≤ k)
    (group : D → Fin k → G) (key : D → (Fin k → Fin q) → R)
    (extra : I → List (Literal (Sum R (pcx278Aux H G q))))
    (hwidth : ∀ j, (extra j).length ≤ 3)
    (P : (H → Bool) → (G → Fin q → Bool) → Prop)
    (hP : ∀ T y g p, (∀ j, pcx278ListSat (Sum.elim T (pcx278AuxVal y g p)) (extra j)) ↔ P y g) :
    ∃ F : Finset (Clause (Sum R (Fin (Fintype.card (pcx278Aux H G q))))),
      (∀ C ∈ F, C.card ≤ k + 1) ∧ ∀ T : R → Bool,
        (∃ y g, (∀ s, ∃ j, g s j = true) ∧ P y g ∧
          (∀ i L, (∀ t, g (group i t) (L t) = true) → T (key i L) = true)) ↔
        ∃ z : Fin (Fintype.card (pcx278Aux H G q)) → Bool, Satisfies (Sum.elim T z) (↑F : Set _) := by
  classical
  let chain := pcx278Chain (V := Sum R (pcx278Aux H G q)) hq pcx278Guard pcx278Prefix
  let rows := pcx278Row (H := H) group key
  let all := Sum.elim chain (Sum.elim extra rows)
  have hw (j : Sum (G × Option (Fin q)) (Sum I (D × (Fin k → Fin q)))) :
      (all j).length ≤ k + 1 := by
    rcases j with j | (j | j)
    · have hchain : (chain j).length ≤ 3 := pcx278Chain_width hq pcx278Guard pcx278Prefix j
      exact hchain.trans (by omega)
    · exact (hwidth j).trans (by omega)
    · simp [all, rows, pcx278Row, List.length_ofFn]
  obtain ⟨F, hF, hsem⟩ := pcx278Render (k + 1) all hw
  refine ⟨F, hF, fun T => ?_⟩
  rw [← hsem T]
  have rowSat (y : H → Bool) (g p : G → Fin q → Bool) (i : D) (L : Fin k → Fin q) :
      pcx278ListSat (Sum.elim T (pcx278AuxVal y g p)) (rows (i, L)) ↔
        ((∀ t, g (group i t) (L t) = true) → T (key i L) = true) := by
    simp only [rows, pcx278Row, pcx278ListSat_cons, pcx278ListSat_ofFn]
    change (T (key i L) = true ∨ ∃ t, g (group i t) (L t) = false) ↔ _
    simp only [pcx278BoolFalse, ← Classical.not_forall]
    rw [Classical.or_iff_not_imp_right, not_not]
  constructor
  · rintro ⟨y, g, hg, hy, hrows⟩
    let p : G → Fin q → Bool := fun s j => decide (∃ r : Fin q, r.val ≤ j.val ∧ g s r = true)
    let v := Sum.elim T (pcx278AuxVal y g p)
    refine ⟨pcx278AuxVal y g p, ?_⟩
    have hp (s : G) (j : Fin q) :
        v (pcx278Prefix s j) = true ↔ ∃ r : Fin q, r.val ≤ j.val ∧ v (pcx278Guard s r) = true := by
      simp [v, pcx278Prefix, pcx278Guard, pcx278AuxVal, p]
    have hguard (s : G) : ∃ j : Fin q, v (pcx278Guard s j) = true := hg s
    intro j
    rcases j with j | (j | ⟨i, L⟩)
    · exact pcx278Chain_complete hq pcx278Guard pcx278Prefix v hguard hp j
    · exact (hP T y g p).mpr hy j
    · exact (rowSat y g p i L).mpr (hrows i L)
  · rintro ⟨s, hs⟩
    let y : H → Bool := fun j => s (.inl j)
    let g : G → Fin q → Bool := fun i j => s (.inr (true, i, j))
    let p : G → Fin q → Bool := fun i j => s (.inr (false, i, j))
    have he : pcx278AuxVal y g p = s := by
      funext a
      rcases a with i | ⟨b, i, j⟩
      · rfl
      · cases b <;> rfl
    refine ⟨y, g, ?_, ?_, ?_⟩
    · intro i
      exact pcx278Chain_sound hq pcx278Guard pcx278Prefix (Sum.elim T s) (fun j => hs (.inl j)) i
    · apply (hP T y g p).mp
      intro j
      rw [he]
      exact hs (.inr (.inl j))
    · intro i L
      apply (rowSat y g p i L).mp
      rw [he]
      exact hs (.inr (.inr (i, L)))

private theorem pcx278Ceil {d k : ℕ} (hd : 0 < d) (hk : 0 < k) :
    0 < (d + k - 1) / k ∧ d ≤ k * ((d + k - 1) / k) := by
  let m := (d + k - 1) / k
  have h := Nat.lt_mul_div_succ (d + k - 1) hk
  change d + k - 1 < k * (m + 1) at h
  rw [Nat.mul_add, Nat.mul_one] at h
  have hc : d ≤ k * m := by omega
  refine ⟨?_, hc⟩
  change 0 < m
  by_contra! hz
  have hm : m = 0 := Nat.eq_zero_of_le_zero hz
  simp [hm] at hc
  omega

private def pcx278Block {d k m : ℕ} (hm : 0 < m) (hc : d ≤ k * m) (j : Fin d) : Fin k :=
  ⟨j.val / m, (Nat.div_lt_iff_lt_mul hm).mpr (j.isLt.trans_le hc)⟩

private def pcx278Offset {d m : ℕ} (hm : 0 < m) (j : Fin d) : Fin m :=
  ⟨j.val % m, Nat.mod_lt _ hm⟩

private theorem pcx278Parts {d k m : ℕ} (hm : 0 < m) (hc : d ≤ k * m) (j : Fin d) :
    (pcx278Block hm hc j).val * m + (pcx278Offset hm j).val = j.val := by
  exact (Nat.add_comm _ _).trans (Nat.mod_add_div' _ _)

private def pcx278Shift {n : ℕ} (hn : 0 < n) (i : Fin n) (j : ℕ) : Fin n :=
  ⟨(i.val + j) % n, Nat.mod_lt _ hn⟩

private noncomputable def pcx278Labels (m : ℕ) : (Fin m → Bool) ≃ Fin (2 ^ m) :=
  Fintype.equivFinOfCardEq (by simp)

private theorem pcx278Small (n w : ℕ) (hn : 0 < n) (k : ℕ) (hk : 2 ≤ k) :
    ∃ (a : ℕ) (F : Finset (Clause (Sum (Fin n × (Fin (w + 1) → Bool)) (Fin a)))),
      ((∀ C ∈ F, C.card ≤ k + 1) ∧ ∀ T,
        (∃ x : Fin n → Bool, ∀ i : Fin n,
          T (i, fun j : Fin (w + 1) => x (pcx278Shift hn i j.val)) = true) ↔
        ∃ z : Fin a → Bool, Satisfies (Sum.elim T z) (↑F : Set _)) ∧
      a ≤ 2 * k * 2 ^ ((n + k - 1) / k) := by
  let m := (n + k - 1) / k
  obtain ⟨hm, hc⟩ : 0 < m ∧ n ≤ k * m := pcx278Ceil hn (by omega)
  let e := pcx278Labels m
  let decode (L : Fin k → Fin (2 ^ m)) (j : Fin n) :=
    e.symm (L (pcx278Block hm hc j)) (pcx278Offset hm j)
  let chunk (x : Fin n → Bool) (t : Fin k) (b : Fin m) :=
    if h : t.val * m + b.val < n then x ⟨t.val * m + b.val, h⟩ else false
  let key (i : Fin n) (L : Fin k → Fin (2 ^ m)) : Fin n × (Fin (w + 1) → Bool) :=
    (i, fun j => decode L (pcx278Shift hn i j.val))
  have hdecode (x : Fin n → Bool) : decode (fun t => e (chunk x t)) = x := by
    funext j
    have he := pcx278Parts hm hc j
    have hj : (pcx278Block hm hc j).val * m + (pcx278Offset hm j).val < n := by
      rw [he]
      exact j.isLt
    simp only [decode, Equiv.symm_apply_apply, chunk, dite_eq_left hj]
    exact congrArg x (Fin.ext he)
  obtain ⟨F, hF, hsem⟩ := pcx278Compile (H := Fin 0) (I := Fin 0) (Nat.two_pow_pos m) hk
    (fun (_ : Fin n) (t : Fin k) => t) key (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
    (fun _ _ => True) (fun _ _ _ _ => ⟨fun _ => trivial, fun _ j => Fin.elim0 j⟩)
  refine ⟨_, F, ⟨hF, fun T => ?_⟩, ?_⟩
  · rw [← hsem T]
    constructor
    · rintro ⟨x, hx⟩
      let pick : Fin k → Fin (2 ^ m) := fun t => e (chunk x t)
      refine ⟨fun j => Fin.elim0 j, fun t j => decide (j = pick t), ?_, trivial, ?_⟩
      · intro t
        exact ⟨pick t, by simp⟩
      · intro i L hL
        have heL : L = pick := funext fun t => of_decide_eq_true (hL t)
        subst L
        simpa only [key, pick, hdecode x] using hx i
    · rintro ⟨_, g, hg, _, hr⟩
      choose L hL using hg
      exact ⟨decode L, fun i => hr i L hL⟩
  · simp [pcx278Aux, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, m, Nat.mul_assoc]

private theorem pcx278Large (n w : ℕ) (hn : 0 < n) (k : ℕ) (hk : 2 ≤ k) :
    ∃ (a : ℕ) (F : Finset (Clause (Sum (Fin n × (Fin (w + 1) → Bool)) (Fin a)))),
      ((∀ C ∈ F, C.card ≤ k + 1) ∧ ∀ T,
        (∃ x : Fin n → Bool, ∀ i : Fin n,
          T (i, fun j : Fin (w + 1) => x (pcx278Shift hn i j.val)) = true) ↔
        ∃ z : Fin a → Bool, Satisfies (Sum.elim T z) (↑F : Set _)) ∧
      a ≤ n + 2 * n * 2 ^ ((w + 1 + k - 1) / k) := by
  let m := (w + 1 + k - 1) / k
  obtain ⟨hm, hc⟩ : 0 < m ∧ w + 1 ≤ k * m := pcx278Ceil (by omega) (by omega)
  let e := pcx278Labels m
  let group (i : Fin n) (t : Fin k) := pcx278Shift hn i (t.val * m)
  let chunk (x : Fin n → Bool) (s : Fin n) (b : Fin m) := x (pcx278Shift hn s b.val)
  let pattern (L : Fin k → Fin (2 ^ m)) (j : Fin (w + 1)) :=
    e.symm (L (pcx278Block hm hc j)) (pcx278Offset hm j)
  let key (i : Fin n) (L : Fin k → Fin (2 ^ m)) : Fin n × (Fin (w + 1) → Bool) :=
    (i, pattern L)
  let extra (a : (Fin n × Fin (2 ^ m)) × Fin m) :
      List (Literal (Sum (Fin n × (Fin (w + 1) → Bool)) (pcx278Aux (Fin n) (Fin n) (2 ^ m)))) :=
    [(pcx278Guard a.1.1 a.1.2, false),
      (Sum.inr (Sum.inl (pcx278Shift hn a.1.1 a.2.val)), e.symm a.1.2 a.2)]
  let P (x : Fin n → Bool) (g : Fin n → Fin (2 ^ m) → Bool) :=
    ∀ s l, g s l = true → ∀ b, x (pcx278Shift hn s b.val) = e.symm l b
  have hP (T : Fin n × (Fin (w + 1) → Bool) → Bool) (x : Fin n → Bool)
      (g p : Fin n → Fin (2 ^ m) → Bool) :
      (∀ a, pcx278ListSat (Sum.elim T (pcx278AuxVal x g p)) (extra a)) ↔ P x g := by
    have hbinary (s : Fin n) (l : Fin (2 ^ m)) (b : Fin m) :
        pcx278ListSat (Sum.elim T (pcx278AuxVal x g p)) (extra ((s, l), b)) ↔
          (g s l = true → x (pcx278Shift hn s b.val) = e.symm l b) := by
      simp only [extra, pcx278ListSat_cons]
      change (g s l = false ∨ x (pcx278Shift hn s b.val) = e.symm l b ∨
        pcx278ListSat (Sum.elim T (pcx278AuxVal x g p)) []) ↔ _
      simp only [pcx278ListSat_nil, or_false, pcx278BoolFalse]
      rw [Classical.or_iff_not_imp_left, not_not]
    constructor
    · intro h s l hg b
      exact (hbinary s l b).mp (h ((s, l), b)) hg
    · rintro h ⟨⟨s, l⟩, b⟩
      exact (hbinary s l b).mpr (fun hgl => h s l hgl b)
  have hpattern (x : Fin n → Bool) (i : Fin n) (L : Fin k → Fin (2 ^ m))
      (hL : ∀ t b, e.symm (L t) b = chunk x (group i t) b) :
      pattern L = fun j : Fin (w + 1) => x (pcx278Shift hn i j.val) := by
    funext j
    change e.symm (L (pcx278Block hm hc j)) (pcx278Offset hm j) = _
    rw [hL]
    apply congrArg x
    apply Fin.ext
    change (((i.val + (pcx278Block hm hc j).val * m) % n) + (pcx278Offset hm j).val) % n =
      (i.val + j.val) % n
    rw [Nat.mod_add_mod, Nat.add_assoc, pcx278Parts]
  obtain ⟨F, hF, hsem⟩ := pcx278Compile (Nat.two_pow_pos m) hk group key extra
    (fun a => by simp [extra]) P hP
  refine ⟨_, F, ⟨hF, fun T => ?_⟩, ?_⟩
  · rw [← hsem T]
    constructor
    · rintro ⟨x, hx⟩
      let pick : Fin n → Fin (2 ^ m) := fun s => e (chunk x s)
      refine ⟨x, fun s l => decide (l = pick s), ?_, ?_, ?_⟩
      · intro s
        exact ⟨pick s, by simp⟩
      · intro s l hl b
        have he : l = pick s := of_decide_eq_true hl
        subst l
        simp [pick, chunk]
      · intro i L hL
        have he t : L t = pick (group i t) := of_decide_eq_true (hL t)
        have hp := hpattern x i L (fun t b => by rw [he t]; simp [pick])
        simpa only [key, hp] using hx i
    · rintro ⟨x, g, hg, hx, hrows⟩
      choose pick hpick using hg
      refine ⟨x, fun i => ?_⟩
      let L : Fin k → Fin (2 ^ m) := fun t => pick (group i t)
      have hL (t : Fin k) : g (group i t) (L t) = true := hpick _
      have hp := hpattern x i L (fun t b => (hx _ _ (hL t) b).symm)
      simpa only [key, hp] using hrows i L hL
  · simp [pcx278Aux, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, m, Nat.mul_assoc]

private theorem pcx278Upper (n w : ℕ) (hn : 0 < n) (k : ℕ) (hk : 2 ≤ k) :
    ∃ (a : ℕ) (F : Finset (Clause (Sum (Fin n × (Fin (w + 1) → Bool)) (Fin a)))),
      ((∀ C ∈ F, C.card ≤ k + 1) ∧ ∀ T,
        (∃ x : Fin n → Bool, ∀ i : Fin n,
          T (i, fun j : Fin (w + 1) => x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true) ↔
        ∃ z : Fin a → Bool, Satisfies (Sum.elim T z) (↑F : Set _)) ∧
      a ≤ (if n ≤ w + 1 then 2 * k * 2 ^ ((n + k - 1) / k)
        else n + 2 * n * 2 ^ ((w + 1 + k - 1) / k)) := by
  by_cases h : n ≤ w + 1
  · simpa only [ite_eq_left h, pcx278Shift] using pcx278Small n w hn k hk
  · simpa only [ite_eq_right h, pcx278Shift] using pcx278Large n w hn k hk

end PEqualNP.Outside.L_pcx_278_aux

open PEqualNP.Outside.L_pcx_278_aux

theorem PEqualNP.Outside.L_pcx_278 :
∀ (n w : ℕ) (hn : 0 < n),
  let Pat := Fin (w+1) → Bool
  let Raw := Fin n × Pat
  let accepts := fun T : Raw → Bool => ∃ x : Fin n → Bool, ∀ i : Fin n,
    T (i, fun j : Fin (w+1) => x ⟨(i.val+j.val)%n, Nat.mod_lt _ hn⟩) = true
  let enc := fun (a W : ℕ)
      (F : Finset (PEqualNP.ProofComplexity.Clause (Sum Raw (Fin a)))) =>
    (∀ C ∈ F, C.card ≤ W) ∧ ∀ T : Raw → Bool,
      accepts T ↔ ∃ z : Fin a → Bool,
        PEqualNP.ProofComplexity.Satisfies (Sum.elim T z) (↑F : Set _)
  let d := if n ≤ w+1 then n else w
  ((∃ a F, enc a 2 F) ↔ (n = 1 ∨ w = 0)) ∧
  ∀ k : ℕ, 2 ≤ k →
    (∀ a F, enc a (k+1) F →
      2^d ≤ ∑ j ∈ Finset.range (k+1), (k+1-j) * Nat.choose a j) ∧
    ∃ a F, enc a (k+1) F ∧
      a ≤ (if n ≤ w+1 then 2*k*2^((n+k-1)/k)
           else n + 2*n*2^((w+1+k-1)/k)) := by
  intro n w hn
  refine ⟨pcx278WidthTwo n w hn, fun k hk => ⟨pcx278Lower n w hn k, ?_⟩⟩
  exact pcx278Upper n w hn k hk
