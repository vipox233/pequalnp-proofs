import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_pcx_203
import PEqualNP.ProofComplexity.L069

namespace PEqualNP.Outside.L_pcx_204_aux

open PEqualNP.ProofComplexity PEqualNP.Expanders

theorem eval_mono (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add hp hq
  | monomial k a =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

abbrev KC (n : ℕ) : BipGraph (n + 1) n := fun _ => Finset.univ

def ι {n : ℕ} {G : BipGraph (n + 1) n} (w : GEdge G) : GEdge (KC n) := ⟨w.1, Finset.mem_univ _⟩

def ext {n : ℕ} (G : BipGraph (n + 1) n) (a : GEdge G → Bool) (v : GEdge (KC n)) : Bool :=
  if h : v.1.2 ∈ G v.1.1 then a ⟨v.1, h⟩ else false

def proj {n : ℕ} (G : BipGraph (n + 1) n) (q : LinEq (GEdge (KC n))) : LinEq (GEdge G) :=
  (Finset.univ.filter (fun w : GEdge G => ι w ∈ q.1), q.2)

theorem ext_ι {n : ℕ} (G : BipGraph (n + 1) n) (a : GEdge G → Bool) (w : GEdge G) :
    ext G a (ι w) = a w := by
  show (if h : w.1.2 ∈ G w.1.1 then a ⟨w.1, h⟩ else false) = a w
  rw [dif_pos w.2]

theorem sat_proj {n : ℕ} (G : BipGraph (n + 1) n) (a : GEdge G → Bool)
    (q : LinEq (GEdge (KC n))) : LinEqSat a (proj G q) ↔ LinEqSat (ext G a) q := by
  unfold LinEqSat
  have hc : ((proj G q).1.filter (fun w => a w = true)).card
      = (q.1.filter (fun v => ext G a v = true)).card := by
    apply Finset.card_bij (fun w _ => ι w)
    · intro w hw
      simp only [proj, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact ⟨hw.1, by rw [ext_ι]; exact hw.2⟩
    · intro w1 _ w2 _ h
      exact Subtype.ext (congrArg (fun v : GEdge (KC n) => v.1) h)
    · intro v hv
      simp only [Finset.mem_filter] at hv
      obtain ⟨hvq, hva⟩ := hv
      by_cases h : v.1.2 ∈ G v.1.1
      · have hv' : ι (⟨v.1, h⟩ : GEdge G) = v := Subtype.ext rfl
        refine ⟨⟨v.1, h⟩, ?_, hv'⟩
        simp only [proj, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hv']
        refine ⟨hvq, ?_⟩
        rw [← ext_ι G a, hv']
        exact hva
      · exfalso
        have : ext G a v = false := by
          show (if h : v.1.2 ∈ G v.1.1 then a ⟨v.1, h⟩ else false) = false
          rw [dif_neg h]
        rw [this] at hva
        exact Bool.false_ne_true hva
  rw [hc]
  exact Iff.rfl

theorem pig_mem {n : ℕ} (G : BipGraph (n + 1) n) (i : Fin (n + 1)) :
    (Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true))
      ∈ funGraphPHP G :=
  Or.inl (Or.inl ⟨i, rfl⟩)

theorem pair_case {n : ℕ} (G : BipGraph (n + 1) n) (e e' : GEdge (KC n))
    (hmem : ∀ (h : e.1.2 ∈ G e.1.1) (h' : e'.1.2 ∈ G e'.1.1),
      ({((⟨e.1, h⟩ : GEdge G), false), ((⟨e'.1, h'⟩ : GEdge G), false)} : Clause (GEdge G))
        ∈ funGraphPHP G) :
    ∃ D ∈ funGraphPHP G, ∀ a, ClauseSat a D →
      ClauseSat (ext G a) ({(e, false), (e', false)} : Clause (GEdge (KC n))) := by
  by_cases h : e.1.2 ∈ G e.1.1
  · by_cases h' : e'.1.2 ∈ G e'.1.1
    · refine ⟨_, hmem h h', fun a ⟨l, hl, hs⟩ => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · refine ⟨(e, false), by simp, ?_⟩
        show (if h : e.1.2 ∈ G e.1.1 then a ⟨e.1, h⟩ else false) = false
        rw [dif_pos h]; exact hs
      · refine ⟨(e', false), by simp, ?_⟩
        show (if h : e'.1.2 ∈ G e'.1.1 then a ⟨e'.1, h⟩ else false) = false
        rw [dif_pos h']; exact hs
    · refine ⟨_, pig_mem G 0, fun a _ => ⟨(e', false), by simp, ?_⟩⟩
      show (if h : e'.1.2 ∈ G e'.1.1 then a ⟨e'.1, h⟩ else false) = false
      rw [dif_neg h']
  · refine ⟨_, pig_mem G 0, fun a _ => ⟨(e, false), by simp, ?_⟩⟩
    show (if h : e.1.2 ∈ G e.1.1 then a ⟨e.1, h⟩ else false) = false
    rw [dif_neg h]

theorem hax {n : ℕ} (G : BipGraph (n + 1) n) :
    ∀ C ∈ funGraphPHP (KC n), ∃ D ∈ funGraphPHP G, ∀ a, ClauseSat a D →
      ClauseSat (ext G a) C := by
  intro C hC
  simp only [funGraphPHP, graphPHP, Set.mem_union, Set.mem_setOf_eq] at hC
  rcases hC with (⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩) | ⟨e, e', h1, h2, rfl⟩
  · refine ⟨_, pig_mem G i, fun a ⟨l, hl, hs⟩ => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    refine ⟨(ι l.1, true), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hl.1, trivial⟩
    · show ext G a (ι l.1) = true
      rw [ext_ι, hs, hl.2]
  · exact pair_case G e e' (fun h h' => Or.inl (Or.inr ⟨_, _, h1, h2, rfl⟩))
  · exact pair_case G e e' (fun h h' => Or.inr ⟨_, _, h1, h2, rfl⟩)

theorem one_line {n : ℕ} (G : BipGraph (n + 1) n) (i : Fin (n + 1)) (hi : G i = ∅) (k : ℕ) :
    IsLinKRefutation k (funGraphPHP G) [∅] := by
  have hC : (Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro l _ hl
    have h2 := l.1.2
    rw [hl.1, hi] at h2
    simp at h2
  refine ⟨IsLinKDerivation.ax IsLinKDerivation.nil
    ⟨_, pig_mem G i, ?_⟩ (by simp), List.mem_singleton_self _⟩
  simp only [hC, linKOfClause, linOfClause, Finset.image_empty]

theorem card_ge {n : ℕ} (G : BipGraph (n + 1) n) (hG : ∀ i, (G i).Nonempty) :
    n + 1 ≤ Fintype.card (GEdge G) := by
  let f : Fin (n + 1) → GEdge G := fun i => ⟨(i, (hG i).choose), (hG i).choose_spec⟩
  have hf : Function.Injective f := fun i j h => by
    have := congrArg (fun w : GEdge G => w.1.1) h
    simpa [f] using this
  simpa using Fintype.card_le_of_injective f hf

end PEqualNP.Outside.L_pcx_204_aux

open PEqualNP.Outside.L_pcx_204_aux in
theorem PEqualNP.Outside.L_pcx_204 : ∃ B : ℕ, 2 ≤ B ∧ ∀ p : Polynomial ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
  let K : PEqualNP.Expanders.BipGraph (n + 1) n := fun _ => Finset.univ
  ∀ (k : ℕ) (π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge K))),
    1 ≤ k → B ^ (2 * k) ≤ n →
    PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP K) π →
    p.eval ((n + 1) * n) < π.length := by
  obtain ⟨B, hB2, hL⟩ := PEqualNP.ProofComplexity.L069
  refine ⟨B, hB2, fun p => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hL (2 * p.comp (Polynomial.X ^ 2) + 1)
  refine ⟨n₀, fun n hn => ?_⟩
  intro K k π hk hBk hπ
  obtain ⟨G, hG⟩ := hn₀ n hn
  have hq : ∀ x : ℕ, (2 * p.comp (Polynomial.X ^ 2) + 1 : Polynomial ℕ).eval x
      = 2 * p.eval (x ^ 2) + 1 := by
    intro x
    simp [Polynomial.eval_comp]
  have hne : ∀ i, (G i).Nonempty := by
    intro i
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have h1 := hG k [∅] hk hBk (one_line G i h k)
    rw [hq] at h1
    simp only [List.length_singleton] at h1
    omega
  obtain ⟨τ, hτ, hlen⟩ := PEqualNP.Outside.L_pcx_203 (PEqualNP.Expanders.GEdge K)
    (PEqualNP.Expanders.GEdge G) k (PEqualNP.Expanders.funGraphPHP K)
    (PEqualNP.Expanders.funGraphPHP G) (ext G) (proj G) hk (fun _ => rfl) (sat_proj G)
    (hax G) π hπ
  have h1 := hG k τ hk hBk hτ
  rw [hq] at h1
  have hc := card_ge G hne
  have h2 : (n + 1) * n ≤ Fintype.card (PEqualNP.Expanders.GEdge G) ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul hc (by omega)
  have hm := eval_mono p h2
  omega
