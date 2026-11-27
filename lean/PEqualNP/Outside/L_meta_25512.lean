import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25500
import PEqualNP.Outside.L_meta_25489

namespace PEqualNP.Outside.L_meta_25512_aux
open PEqualNP.Outside.L_meta_25500_aux

theorem col_surj {h : ℕ} (c : Fin (2 * h)) : ∃ j e, c = col j e := by
  have hjlt : c.val / 2 < h := by have := c.isLt; omega
  by_cases hodd : c.val % 2 = 1
  · exact ⟨⟨c.val / 2, hjlt⟩, true, Fin.ext (by show c.val = 2 * (c.val / 2) + 1; omega)⟩
  · exact ⟨⟨c.val / 2, hjlt⟩, false, Fin.ext (by show c.val = 2 * (c.val / 2) + 0; omega)⟩

theorem lit_inj {r h : ℕ} (b : Fin r → Fin h → Bool) (hb : Function.Injective b) :
    Function.Injective (lit b) := by
  intro u v huv
  apply hb
  funext j
  have := congrFun huv (col j true)
  rw [lit_col, lit_col] at this
  revert this; cases b u j <;> cases b v j <;> simp

theorem lit_card {r h : ℕ} (b : Fin r → Fin h → Bool) (u : Fin r) :
    (Finset.univ.filter (fun c => lit b u c = true)).card = h := by
  have he : Finset.univ.filter (fun c => lit b u c = true) =
      Finset.univ.image (fun j => col j (b u j)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    obtain ⟨j, e, rfl⟩ := col_surj c
    rw [lit_col]
    constructor
    · intro hh
      refine ⟨j, ?_⟩
      have : b u j = e := by revert hh; cases b u j <;> cases e <;> simp
      rw [this]
    · rintro ⟨j', hj'⟩
      obtain ⟨h1, h2⟩ := col_inj hj'
      subst h1; subst h2; simp
  rw [he, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro j j' hjj
  exact (col_inj hjj).1

theorem lit_miss {r h : ℕ} (b : Fin r → Fin h → Bool)
    (hnc : ∀ i, ∃ u v, b u i = false ∧ b v i = true) (c : Fin (2 * h)) :
    ∃ v, lit b v c = false := by
  obtain ⟨j, e, rfl⟩ := col_surj c
  obtain ⟨u, v, hu, hv⟩ := hnc j
  cases e
  · exact ⟨v, by rw [lit_col, hv]; rfl⟩
  · exact ⟨u, by rw [lit_col, hu]; rfl⟩

end PEqualNP.Outside.L_meta_25512_aux

open PEqualNP.Outside.L_meta_25512_aux in
theorem PEqualNP.Outside.L_meta_25512 : (∀ (k m s : ℕ) (name : Fin m → Fin (2 ^ k)),
  2 ≤ k → 2 ≤ m → Function.Injective name →
  PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin m) (c : Fin (2 * k)) =>
      (name u).val.testBit (c.val / 2) == c.val.testBit 0) s →
  2 * m ≤ s) := by
  intro k m s name hk hm hname hrep
  by_contra hlt
  rw [Nat.not_le] at hlt
  obtain ⟨r, h, row, coord, D, hrow, hcoord, hb, hh, hhr, hnc, hmono, hrb, hrepD, hsz, hDlt, hreads⟩ :=
    PEqualNP.Outside.L_meta_25500 k m s name hk hm hname hrep hlt
  have := PEqualNP.Outside.L_meta_25489 r h
    (PEqualNP.Outside.L_meta_25500_aux.lit (fun a' j' => (name (row a')).val.testBit (coord j').val)) D
    hh (lit_inj _ hb) (lit_card _) (lit_miss _ hnc) hmono hrb hrepD hreads
  omega
