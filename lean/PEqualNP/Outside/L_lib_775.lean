import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_775

lemma prefix_getD (a b : List Bool) (h : a <+: b) (i : ℕ) (hi : i<a.length) :
    b.getD i false=a.getD i false := by
  obtain ⟨t,ht⟩ := h
  rw [←ht]
  exact List.getD_append _ _ _ _ hi

lemma prefix_eq_of_ge (a b : List Bool) (h : a <+: b) (hlen : b.length≤a.length) :
    a=b := by
  obtain ⟨t,ht⟩ := h
  have hz : t.length=0 := by
    have hh := congrArg List.length ht
    simp only [List.length_append] at hh
    omega
  have ht0 : t=[] := List.length_eq_zero_iff.mp hz
  simpa [ht0] using ht

lemma prefix_block_card (L : ℕ) (a : List Bool) :
    ((Finset.univ : Finset (Fin L → Bool)).filter (fun x => a <+: List.ofFn x)).card
      ≤ 2^(L-a.length) := by
  classical
  let A := (Finset.univ : Finset (Fin L → Bool)).filter (fun x => a <+: List.ofFn x)
  let tail : (Fin L → Bool) → (Fin (L-a.length) → Bool) :=
    fun x j => x ⟨a.length+j.val,by omega⟩
  have hinj : Function.Injective (fun x : ↥A => tail x.val) := by
    intro x y h
    apply Subtype.ext
    funext i
    by_cases hi : i.val<a.length
    · have hx := prefix_getD a (List.ofFn x.val) (Finset.mem_filter.mp x.property).2 i.val hi
      have hy := prefix_getD a (List.ofFn y.val) (Finset.mem_filter.mp y.property).2 i.val hi
      have hh := hx.trans hy.symm
      simpa using hh
    · have hj : i.val-a.length<L-a.length := by omega
      have hh := congrFun h (⟨i.val-a.length,hj⟩ : Fin (L-a.length))
      change x.val ⟨a.length+(i.val-a.length),_⟩=
        y.val ⟨a.length+(i.val-a.length),_⟩ at hh
      have he : a.length+(i.val-a.length)=i.val := by omega
      simpa only [he] using hh
  have hh := Fintype.card_le_of_injective _ hinj
  change A.card ≤ _
  change Fintype.card ↥A ≤ Fintype.card (Fin (L-a.length) → Bool) at hh
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using hh

lemma kraft_budget {k : ℕ} (L : ℕ) (l : Fin k → ℕ) (hl : ∀ i, l i≤L)
    (h : ((1:ℚ)/2)^L+∑ i,((1:ℚ)/2)^(l i)≤1) :
    (∑ i,2^(L-l i))+1≤2^L := by
  have hscale (n : ℕ) (hn : n≤L) :
      (2:ℚ)^L*(((1:ℚ)/2)^n)=(2:ℚ)^(L-n) := by
    rw [div_pow,one_pow,mul_one_div]
    have hnz : (2:ℚ)^n≠0 := pow_ne_zero _ (by norm_num)
    apply (div_eq_iff hnz).mpr
    rw [←pow_add,Nat.sub_add_cancel hn]
  have hm := mul_le_mul_of_nonneg_left h (by positivity : 0≤(2:ℚ)^L)
  rw [mul_add,Finset.mul_sum,hscale L (by omega)] at hm
  simp_rw [hscale _ (hl _)] at hm
  simp only [Nat.sub_self,pow_zero,mul_one] at hm
  have hn : (∑ i,(2:ℚ)^(L-l i))+1≤(2:ℚ)^L := by linarith
  exact_mod_cast hn

lemma fresh_word {k : ℕ} (L : ℕ) (c : Fin k → List Bool)
    (h : (∑ i,2^(L-(c i).length))+1≤2^L) :
    ∃ w : List Bool, w.length=L ∧ ∀ i, ¬(c i <+: w) := by
  classical
  let A : Fin k → Finset (Fin L → Bool) :=
    fun i => Finset.univ.filter (fun x => c i <+: List.ofFn x)
  let bad := Finset.univ.biUnion A
  have hsum : ∑ i,(A i).card ≤ ∑ i,2^(L-(c i).length) := by
    apply Finset.sum_le_sum
    intro i hi
    exact prefix_block_card L (c i)
  have hb : bad.card<2^L := by
    have hu := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin k))) (t := A)
    dsimp [bad]
    omega
  have hex : ∃ x : Fin L → Bool, x∉bad := by
    by_contra hn
    push Not at hn
    have hi : (Finset.univ : Finset (Fin L → Bool))⊆bad := by intro x hx; exact hn x
    have hc := Finset.card_le_card hi
    simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hc
    omega
  obtain ⟨x,hx⟩ := hex
  refine ⟨List.ofFn x,by simp,?_⟩
  intro i hp
  apply hx
  apply Finset.mem_biUnion.mpr
  exact ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩

lemma construct : ∀ (k : ℕ) (l : Fin k → ℕ), (∑ i,((1:ℚ)/2)^(l i))≤1 →
    ∃ c : Fin k → List Bool, (∀ i,(c i).length=l i) ∧
      ∀ i j,i≠j → ¬(c i <+: c j) := by
  classical
  intro k
  induction k with
  | zero =>
    intro l h
    refine ⟨Fin.elim0,?_,?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  | succ k ih =>
    intro l h
    obtain ⟨m,hm,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (k+1))) l
      ⟨0,Finset.mem_univ _⟩
    let L := l m
    let rest : Fin k → ℕ := fun i => l (m.succAbove i)
    have hsplit := Fin.sum_univ_succAbove (fun i => ((1:ℚ)/2)^(l i)) m
    have hbudget : ((1:ℚ)/2)^L+∑ i,((1:ℚ)/2)^(rest i)≤1 := by
      dsimp [L,rest]
      linarith
    have hpos : 0≤((1:ℚ)/2)^L := by positivity
    have hrest : (∑ i,((1:ℚ)/2)^(rest i))≤1 := by linarith
    obtain ⟨c,hc,hpf⟩ := ih rest hrest
    have hlen : ∀ i, rest i≤L := fun i => hmax _ (Finset.mem_univ _)
    have hnat : (∑ i,2^(L-(c i).length))+1≤2^L := by
      simp_rw [hc]
      exact kraft_budget L rest hlen hbudget
    obtain ⟨w,hw,hfresh⟩ := fresh_word L c hnat
    let C : Fin (k+1) → List Bool := m.insertNth w c
    refine ⟨C,?_,?_⟩
    · refine (Fin.forall_iff_succAbove (P := fun i => (C i).length=l i) m).mpr ?_
      constructor
      · simpa [C,L] using hw
      · intro i
        simpa [C,rest] using hc i
    · intro i j hij hp
      rcases Fin.eq_self_or_eq_succAbove m i with hi|⟨u,hi⟩
      · rcases Fin.eq_self_or_eq_succAbove m j with hj|⟨v,hj⟩
        · exact hij (hi.trans hj.symm)
        · have hh : w <+: c v := by simpa [hi,hj,C] using hp
          have heq : w=c v := prefix_eq_of_ge w (c v) hh (by rw [hc v,hw]; exact hlen v)
          apply hfresh v
          rw [heq]
      · rcases Fin.eq_self_or_eq_succAbove m j with hj|⟨v,hj⟩
        · exact hfresh u (by simpa [hi,hj,C] using hp)
        · have huv : u≠v := by
            intro he
            apply hij
            exact hi.trans ((congrArg m.succAbove he).trans hj.symm)
          exact hpf u v huv (by simpa [hi,hj,C] using hp)

end PEqualNP.Outside.L_lib_775


theorem PEqualNP.Outside.L_lib_775 : ∀ (k : ℕ) (l : Fin k → ℕ), (∑ i, ((1 : ℚ) / 2) ^ (l i)) ≤ 1 →
  ∃ c : Fin k → List Bool, (∀ i, (c i).length = l i) ∧ ∀ i j, i ≠ j → ¬ (c i <+: c j) :=
  PEqualNP.Outside.L_lib_775.construct
