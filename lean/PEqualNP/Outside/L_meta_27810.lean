import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27810_aux

def ix (k : ℕ) (hk : 0 < k) (j : ℕ) : Fin k := ⟨j % k, Nat.mod_lt _ hk⟩

def back (k : ℕ) (hk : 0 < k) (S : Finset (Fin k)) : Finset (Fin k) :=
  Finset.univ.filter (fun p : Fin k =>
    ∃ i ∈ S, ∃ t : Fin 7, p = ix k hk (i.val + k - 2 % k + t.val))

def run (k : ℕ) (hk : 0 < k) (out : Fin k) (h : ℕ) : Finset (Fin k) :=
  (List.range h).foldl (fun S _ => back k hk S) {out}

theorem run_succ (k : ℕ) (hk : 0 < k) (out : Fin k) (h : ℕ) :
    run k hk out (h+1) = back k hk (run k hk out h) := by
  simp [run, List.range_succ, List.foldl_append]

theorem shift (k : ℕ) (hk : 0 < k) (b c : ℕ) : ∃ d, d < k ∧ ∀ e, (b + d + e) % k = (c + e) % k := by
  refine ⟨(c + k - b % k) % k, Nat.mod_lt _ hk, fun e => ?_⟩
  have hb : b % k < k := Nat.mod_lt _ hk
  have h1 : (b + (c + k - b % k) % k) % k = c % k := by
    rw [Nat.add_mod_mod, ← Nat.mod_add_mod, show b % k + (c + k - b % k) = c + k by omega,
      Nat.add_mod_right]
  rw [← Nat.mod_add_mod, h1, Nat.mod_add_mod]

theorem run_mem (k : ℕ) (hk : 0 < k) (out : Fin k) : ∀ h s, s ≤ 6*h →
    ix k hk (out.val + h*(k - 2 % k) + s) ∈ run k hk out h
  | 0, s, hs => by
      have h0 : s = 0 := by omega
      subst h0
      have : ix k hk (out.val + 0*(k - 2 % k) + 0) = out := by
        apply Fin.ext; simp [ix, Nat.mod_eq_of_lt out.isLt]
      rw [this]; simp [run]
  | h+1, s, hs => by
      rw [run_succ]
      have hc : 2 % k < k := Nat.mod_lt _ hk
      have ih := run_mem k hk out h (min s (6*h)) (by omega)
      simp only [back, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨_, ih, ⟨s - min s (6*h), by omega⟩, ?_⟩
      apply Fin.ext
      show (out.val + (h+1)*(k - 2 % k) + s) % k =
        ((out.val + h*(k - 2 % k) + min s (6*h)) % k + k - 2 % k + (s - min s (6*h))) % k
      rw [show (out.val + h*(k - 2 % k) + min s (6*h)) % k + k - 2 % k + (s - min s (6*h)) =
        (out.val + h*(k - 2 % k) + min s (6*h)) % k + ((k - 2 % k) + (s - min s (6*h))) by omega,
        Nat.mod_add_mod]
      congr 1
      have : (h+1)*(k - 2 % k) = h*(k - 2 % k) + (k - 2 % k) := by ring
      omega

theorem run_all (k : ℕ) (hk : 0 < k) (out : Fin k) (h : ℕ) (hh : k ≤ 6*h+1) (p : Fin k) :
    p ∈ run k hk out h := by
  obtain ⟨d, hd, he⟩ := shift k hk (out.val + h*(k - 2 % k)) p.val
  have := run_mem k hk out h d (by omega)
  have e : ix k hk (out.val + h*(k - 2 % k) + d) = p := by
    apply Fin.ext
    have := he 0
    simp only [add_zero] at this
    show (out.val + h*(k - 2 % k) + d) % k = p.val
    rw [this, Nat.mod_eq_of_lt p.isLt]
  rwa [e] at this

theorem hit (k : ℕ) (hk : 0 < k) (key c : ℕ) :
    ∃ a e, a < (k+2)/3 ∧ e < 3 ∧ (key + 3*(a+1) + 1) % k = (c + e) % k := by
  obtain ⟨d, hd, he⟩ := shift k hk (key + 4) c
  by_cases hw : d + 2 < k
  · refine ⟨(d+2)/3, 3*((d+2)/3) - d, by omega, by omega, ?_⟩
    rw [← he]; congr 1; omega
  · refine ⟨0, k - d, by omega, by omega, ?_⟩
    rw [← he, show key + 4 + d + (k - d) = key + 3*(0+1) + 1 + k by omega, Nat.add_mod_right]

theorem main (k r : ℕ) (hk : 0 < k) (hmr : (k+2)/3 ≤ r) (hkr : k ≤ 6*(r-(k+2)/3)+1)
    (out start : Fin k) (len : ℕ) (h3 : 3 ≤ len) (hl : len+3 ≤ k) (key : Fin k) :
    (∃ j : Fin r, j.val+1 ≤ (k+2)/3 ∧
      ix k hk (key.val+3*(j.val+1)+1) ∈
        (List.range (r-(j.val+1))).foldl (fun S _ => back k hk S) {out} ∧
      ix k hk (key.val+3*(j.val+1)+1) ∈ (Finset.range len).image (fun a => ix k hk (start.val+a))) ∧
    (∃ j : Fin r, j.val+1 ≤ (k+2)/3 ∧
      ix k hk (key.val+3*(j.val+1)+1) ∈
        (List.range (r-(j.val+1))).foldl (fun S _ => back k hk S) {out} ∧
      ix k hk (key.val+3*(j.val+1)+1) ∉ (Finset.range len).image (fun a => ix k hk (start.val+a))) := by
  constructor
  · obtain ⟨a, e, ha, he, h⟩ := hit k hk key.val start.val
    refine ⟨⟨a, by omega⟩, by show a + 1 ≤ _; omega, run_all k hk out _ (by show k ≤ 6*(r-(a+1))+1; omega) _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨e, Finset.mem_range.mpr (by omega), Fin.ext h.symm⟩
  · obtain ⟨a, e, ha, he, h⟩ := hit k hk key.val (start.val + len)
    refine ⟨⟨a, by omega⟩, by show a + 1 ≤ _; omega, run_all k hk out _ (by show k ≤ 6*(r-(a+1))+1; omega) _, ?_⟩
    rw [Finset.mem_image]
    rintro ⟨a', ha', h'⟩
    have ha'' := Finset.mem_range.mp ha'
    have h2 : (start.val + a') % k = (key.val + 3*(a+1) + 1) % k := congrArg Fin.val h'
    rw [h] at h2
    have h3' : k ∣ (start.val + len + e) - (start.val + a') :=
      (Nat.modEq_iff_dvd' (by omega)).mp h2
    have := Nat.le_of_dvd (by omega) h3'
    omega

end PEqualNP.Outside.L_meta_27810_aux

theorem PEqualNP.Outside.L_meta_27810 : (∀ (k r : ℕ) (hk : 0 < k),
  let m := (k+2)/3
  m ≤ r → k ≤ 6*(r-m)+1 →
  let ix := fun j : ℕ => (⟨j % k, Nat.mod_lt _ hk⟩ : Fin k)
  let back := fun (S : Finset (Fin k)) => Finset.univ.filter (fun p : Fin k =>
    ∃ i ∈ S, ∃ t : Fin 7, p = ix (i.val + k - 2 % k + t.val))
  ∀ (out start : Fin k) (len : ℕ), 3 ≤ len → len+3 ≤ k →
    let side := (Finset.range len).image (fun a => ix (start.val+a))
    let kept := fun j : Fin r =>
      (List.range (r-(j.val+1))).foldl (fun S _ => back S) {out}
    ∀ key : Fin k,
      let site := fun j : Fin r => ix (key.val+3*(j.val+1)+1)
      (∃ j : Fin r, j.val+1 ≤ m ∧ site j ∈ kept j ∧ site j ∈ side) ∧
      (∃ j : Fin r, j.val+1 ≤ m ∧ site j ∈ kept j ∧ site j ∉ side)) := by
  intro k r hk m hmr hkr ix back out start len h3 hl side kept key site
  exact PEqualNP.Outside.L_meta_27810_aux.main k r hk hmr hkr out start len h3 hl key
