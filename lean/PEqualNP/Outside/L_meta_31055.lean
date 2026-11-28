import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31055

open PEqualNP.CircuitLowerBounds

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

section FreeNot

def ops {n : ℕ} (x y : BitVec n) : List (BitVec n) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]

abbrev basicOps {n : ℕ} (a b : BitVec n) : Finset (BitVec n) := (ops a b).toFinset

theorem ops_swap {n : ℕ} (a b : BitVec n) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def holds {n : ℕ} (av : Finset (BitVec n)) (z : BitVec n) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {n : ℕ} {av : Finset (BitVec n)} {z a : BitVec n} (h : holds av z) :
    holds (insert a av) z := by
  rcases h with h | h | ⟨u, hu, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem hu, he⟩)

theorem holds_mono {n : ℕ} {av av' : Finset (BitVec n)} (sub : av ⊆ av') {x : BitVec n}
    (h : holds av x) : holds av' x := by
  rcases h with h | h | ⟨a, ha, e⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨a, sub ha, e⟩)

theorem holds_not {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} (h : holds av z) :
    holds av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable {n : ℕ} (av : Finset (BitVec n)) (z : BitVec n) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} (h : reachable av z) :
    reachable av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds_not hw⟩

theorem bv_zero_and {n : ℕ} (x : BitVec n) : (0 : BitVec n) &&& x = 0 := BitVec.zero_and
theorem bv_and_zero {n : ℕ} (x : BitVec n) : x &&& (0 : BitVec n) = 0 := BitVec.and_zero
theorem bv_zero_or {n : ℕ} (x : BitVec n) : (0 : BitVec n) ||| x = x := BitVec.zero_or
theorem bv_or_zero {n : ℕ} (x : BitVec n) : x ||| (0 : BitVec n) = x := BitVec.or_zero
theorem bv_not_zero_and {n : ℕ} (x : BitVec n) : ~~~(0 : BitVec n) &&& x = x := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
theorem bv_and_not_zero {n : ℕ} (x : BitVec n) : x &&& ~~~(0 : BitVec n) = x := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
theorem bv_not_zero_or {n : ℕ} (x : BitVec n) : ~~~(0 : BitVec n) ||| x = ~~~0 := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
theorem bv_or_not_zero {n : ℕ} (x : BitVec n) : x ||| ~~~(0 : BitVec n) = ~~~0 := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp

set_option maxRecDepth 5000 in
theorem and_reach {n : ℕ} {av : Finset (BitVec n)} {x y : BitVec n}
    (hx : holds av x) (hy : holds av y) : reachable av (x &&& y) := by
  have const0 : holds av (0 : BitVec n) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [bv_zero_and]; exact .inl const0
  · rw [bv_not_zero_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [bv_and_zero]; exact .inl const0
  · rw [bv_and_not_zero]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const0 | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : BitVec n) (hw : w ∈ basicOps a b) (z : BitVec n) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps, ops]) _ (.inl rfl)
  · exact add _ (by simp [basicOps, ops]) _ (.inl rfl)
  · exact add _ (by simp [basicOps, ops]) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps, ops]) _ (.inr BitVec.not_or.symm)

theorem or_reach {n : ℕ} {av : Finset (BitVec n)} {x y : BitVec n}
    (hx : holds av x) (hy : holds av y) : reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using
    reachable_not (and_reach (holds_not hx) (holds_not hy))

theorem mem_ops_reach {n : ℕ} {av : Finset (BitVec n)} {x y z : BitVec n}
    (hx : holds av x) (hy : holds av y) (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

theorem mem_ops_const {n : ℕ} {av : Finset (BitVec n)} {x y z : BitVec n}
    (hx : holds av x) (hy : holds av y)
    (hconst : (x = 0 ∨ x = ~~~0) ∨ (y = 0 ∨ y = ~~~0))
    (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have h0 : holds av (0 : BitVec n) := .inl rfl
  have h1 : holds av (~~~(0 : BitVec n)) := .inr (.inl rfl)
  have hnx : holds av (~~~x) := holds_not hx
  have hny : holds av (~~~y) := holds_not hy
  rcases hconst with (rfl | rfl) | (rfl | rfl) <;> rcases hz with rfl | rfl | rfl | rfl
  · rw [bv_zero_and]; exact h0
  · rw [bv_zero_or]; exact hy
  · rw [bv_zero_and]; exact h0
  · rw [bv_and_not_zero]; exact hy
  · rw [bv_not_zero_and]; exact hy
  · rw [bv_not_zero_or]; exact h1
  · rw [bv_not_zero_and]; exact hny
  · rw [BitVec.not_not, bv_and_zero]; exact h0
  · rw [bv_and_zero]; exact h0
  · rw [bv_or_zero]; exact hx
  · rw [bv_and_not_zero]; exact hx
  · rw [bv_zero_and]; exact h0
  · rw [bv_and_not_zero]; exact hx
  · rw [bv_or_not_zero]; exact h1
  · rw [BitVec.not_not, bv_and_zero]; exact h0
  · rw [bv_not_zero_and]; exact hnx

def SignedBuild {n : ℕ} (k : ℕ) (av : Finset (BitVec n)) (z : BitVec n) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} (h : holds av z) :
    SignedBuild 0 av z := by
  rcases h with h | h | ⟨a, ha, e | e⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · subst z; exact Or.inr (Or.inr (Or.inl ha))
  · subst z; exact Or.inr (Or.inr (Or.inr (by simpa only [BitVec.not_not, build] using ha)))

theorem sb_wait {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} {k : ℕ}
    (h : SignedBuild k av z) : SignedBuild (k + 1) av z := by
  rcases h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl (.inl h)))
  · exact .inr (.inr (.inr (.inl h)))

theorem sb_le {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} {k l : ℕ} (hkl : k ≤ l)
    (h : SignedBuild k av z) : SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {n : ℕ} {av : Finset (BitVec n)} {t a b z : BitVec n} {k : ℕ}
    (ha : a ∈ av) (hb : b ∈ av) (hne : a ≠ b) (hz : z ∈ basicOps a b)
    (h : SignedBuild k (insert z av) t) : SignedBuild (k + 1) av t := by
  rcases h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl (.inr ⟨a, ha, b, hb, hne, z, hz, h⟩)))
  · exact .inr (.inr (.inr (.inr ⟨a, ha, b, hb, hne, z, hz, h⟩)))

theorem sb_advance {n : ℕ} {av : Finset (BitVec n)} {z t : BitVec n} {k : ℕ}
    (hz : reachable av z)
    (next : ∀ av' : Finset (BitVec n), av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k + 1) av t := by
  rcases hz with h | ⟨a, ha, b, hb, hn, w, hw, ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem ops_map_of {n m : ℕ} {f : BitVec n → BitVec m}
    (hAnd : ∀ a b, f (a &&& b) = (f a &&& f b))
    (hOr : ∀ a b, f (a ||| b) = (f a ||| f b))
    (hNot : ∀ a, f (~~~a) = ~~~(f a)) :
    ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b) := by
  intro a b z hz
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hAnd, hOr, hNot]

theorem live_transport {n m : ℕ} {f : BitVec n → BitVec m}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : BitVec n} {k : ℕ} {s : Finset (BitVec n)} {av : Finset (BitVec m)}
    (run : live basicOps g k s)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild k av (f g) := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    exact sb_zero (hav g (by simp [run]))
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, hn, z, hz, hout, r, he, tail⟩
    · exact sb_wait (ih skip hav)
    · apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz))
      intro av' sub ok
      apply ih tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hr
      · exact ok
      · exact holds_mono sub (hav u (by simp [he, hr]))

theorem live_transport_save_const {n m : ℕ} {f : BitVec n → BitVec m}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : BitVec n} {k : ℕ} {s : Finset (BitVec n)} {av : Finset (BitVec m)}
    (run : live basicOps g k s)
    (hp : p ∈ s) (hconst : f p = 0 ∨ f p = ~~~0)
    (hng : f g ≠ 0 ∧ f g ≠ ~~~0)
    (hav : ∀ w ∈ s, holds av (f w)) :
    1 ≤ k ∧ SignedBuild (k - 1) av (f g) := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    have hpg : p = g := by simpa [run] using hp
    subst hpg
    rcases hconst with h | h
    · exact (hng.1 h).elim
    · exact (hng.2 h).elim
  | succ k ih =>
    simp only [Nat.add_sub_cancel]
    rcases run with skip | ⟨a, ha, b, hb, hn, z, hz, hout, r, he, tail⟩
    · obtain ⟨hk, hsb⟩ := ih skip hp hav
      exact ⟨by omega, sb_le (by omega) hsb⟩
    · have mapped := hm a b z hz
      have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he, hu])
      by_cases touches : p = a ∨ p = b
      · have hc : (f a = 0 ∨ f a = ~~~0) ∨ (f b = 0 ∨ f b = ~~~0) :=
          touches.elim (fun h => .inl (h ▸ hconst)) (fun h => .inr (h ▸ hconst))
        have collapsed := mem_ops_const (hav a ha) (hav b hb) hc mapped
        refine ⟨by omega, live_transport hm tail ?_⟩
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact collapsed
        · exact inOld u hr
      · have pr : p ∈ r := by
          rw [he] at hp
          simpa [Finset.mem_insert, not_or.mp touches |>.1, not_or.mp touches |>.2] using hp
        have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
        refine ⟨by omega, ?_⟩
        rcases mem_ops_reach (hav a ha) (hav b hb) mapped with hok | ⟨x, hx, y, hy, hxy, w, hw, hok⟩
        · obtain ⟨hk, hsb⟩ := ih tail pt (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hr
            · exact hok
            · exact inOld u hr)
          exact sb_le (by omega) hsb
        · obtain ⟨hk, hsb⟩ := ih tail pt (av := insert w av) (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hr
            · exact hok
            · exact holds_insert (inOld u hr))
          have hstep := sb_step hx hy hxy hw hsb
          exact sb_le (by omega) hstep

def selectRows {n m : ℕ} (rows : Fin m → Fin n) (w : BitVec n) : BitVec m :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin m => w[(rows k).val]))).cast List.length_ofFn

theorem selectRows_bit {n m : ℕ} (rows : Fin m → Fin n) (w : BitVec n) (j : Fin m) :
    (selectRows rows w)[j.val] = w[(rows j).val] := by
  rw [← BitVec.getLsbD_eq_getElem j.isLt]
  simp only [selectRows, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dite_eq_left, Option.getD_some]

theorem selectRows_land {n m : ℕ} (rows : Fin m → Fin n) (u v : BitVec n) :
    selectRows rows (u &&& v) = (selectRows rows u &&& selectRows rows v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin m := ⟨j, hj⟩
  change (selectRows rows (u &&& v))[k.val] = (selectRows rows u &&& selectRows rows v)[k.val]
  simp only [selectRows_bit, BitVec.getElem_and]

theorem selectRows_lor {n m : ℕ} (rows : Fin m → Fin n) (u v : BitVec n) :
    selectRows rows (u ||| v) = (selectRows rows u ||| selectRows rows v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin m := ⟨j, hj⟩
  change (selectRows rows (u ||| v))[k.val] = (selectRows rows u ||| selectRows rows v)[k.val]
  simp only [selectRows_bit, BitVec.getElem_or]

theorem selectRows_neg {n m : ℕ} (rows : Fin m → Fin n) (u : BitVec n) :
    selectRows rows (~~~u) = ~~~selectRows rows u := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin m := ⟨j, hj⟩
  change (selectRows rows (~~~u))[k.val] = (~~~selectRows rows u)[k.val]
  simp only [selectRows_bit, BitVec.getElem_not]

def bitDiff {n : ℕ} (a b : Fin n) (w : BitVec n) : Prop :=
  w[a.val] ≠ w[b.val]

theorem ops_bitDiff {n : ℕ} (a b : Fin n) (x y z : BitVec n) (hz : z ∈ basicOps x y)
    (hd : bitDiff a b z) : bitDiff a b x ∨ bitDiff a b y := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨hx, hy⟩ := fail
  apply hd
  unfold bitDiff at hx hy
  simp only [not_not] at hx hy
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, hx, hy]

theorem bitDiff_not {n : ℕ} {a b : Fin n} {w : BitVec n} (h : bitDiff a b w) :
    bitDiff a b (~~~w) := by
  intro heq
  apply h
  simp only [BitVec.getElem_not] at heq
  cases ha : w[a.val] <;> cases hb : w[b.val] <;> simp_all

theorem live_has_unique_sep {n : ℕ} {g p : BitVec n} {k : ℕ}
    {s : Finset (BitVec n)} {ls : List (BitVec n)}
    (hs : s ⊆ ls.toFinset) (hl : live basicOps g k s)
    (a b : Fin n) (hd : bitDiff a b g)
    (huniq : ∀ w ∈ ls, bitDiff a b w → w = p) : p ∈ s := by
  obtain ⟨w, hw, hdw⟩ := live_separates (bitDiff a b) hd (ops_bitDiff a b) hl
  have hwp : w = p := huniq w (List.mem_toFinset.mp (hs hw)) hdw
  exact hwp ▸ hw

theorem sep_of_all {n : ℕ} (a b : Fin n) (ls : List (BitVec n)) (p : BitVec n)
    (h : ls.all (fun w => !(w[a.val] != w[b.val]) || w == p) = true) :
    ∀ w ∈ ls, bitDiff a b w → w = p := by
  intro w hw hdiff
  have h1 := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq, beq_iff_eq] at h1
  exact h1.resolve_left hdiff

theorem map_holds_list {n m : ℕ} (f : BitVec n → BitVec m) (src : List (BitVec n)) (dst : List (BitVec m))
    (h : src.all (fun w => f w == 0 || f w == ~~~0 || dst.any (fun d => f w == d)) = true) :
    ∀ w ∈ src, holds dst.toFinset (f w) := by
  intro w hw
  have h1 := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h1
  rcases h1 with (h0 | h1) | ⟨d, hd, hwd⟩
  · exact .inl h0
  · exact .inr (.inl h1)
  · exact .inr (.inr ⟨d, List.mem_toFinset.mpr hd, .inl hwd⟩)

theorem unwrap_sb {n : ℕ} {k : ℕ} {av : Finset (BitVec n)} {z : BitVec n}
    (h0 : z ≠ 0) (h1 : z ≠ ~~~0) (h : SignedBuild k av z) :
    ∃ t, (t = z ∨ t = ~~~z) ∧ build basicOps t k av := by
  rcases h with hz | hz | hb | hb
  · exact (h0 hz).elim
  · exact (h1 hz).elim
  · exact ⟨z, .inl rfl, hb⟩
  · exact ⟨~~~z, .inr rfl, hb⟩

theorem not_const_of_neg {n : ℕ} {w : BitVec n} (h : w ≠ 0 ∧ w ≠ ~~~0) :
    ~~~w ≠ 0 ∧ ~~~w ≠ ~~~0 := by
  refine ⟨fun heq => h.2 ?_, fun heq => h.1 ?_⟩
  · simpa only [BitVec.not_not] using congrArg (fun u : BitVec n => ~~~u) heq
  · simpa only [BitVec.not_not] using congrArg (fun u : BitVec n => ~~~u) heq

end FreeNot

section SearchP

abbrev WP (P : ℕ) := BitVec (P + P)
def sepP {P : ℕ} (x : WP P) : BitVec P := ((x >>> P) ^^^ x).setWidth P
def cutsP {P : ℕ} (ws : List (WP P)) : BitVec P := ws.foldr (fun w v => sepP w ||| v) 0
def goalP (P : ℕ) : WP P := BitVec.allOnes P ++ (0 : BitVec P)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def differsP {P : ℕ} (i : Fin P) (w : WP P) : Prop :=
  w.getLsbD (P + i.val) ≠ w.getLsbD i.val

theorem goalP_differs {P : ℕ} (i : Fin P) : differsP i (goalP P) := by
  unfold differsP goalP
  have hi : i.val < P := i.isLt
  have hlo : (BitVec.allOnes P ++ (0 : BitVec P)).getLsbD i.val = false := by
    rw [BitVec.getLsbD_append]
    simp [hi]
  have hhi : (BitVec.allOnes P ++ (0 : BitVec P)).getLsbD (P + i.val) = true := by
    rw [BitVec.getLsbD_append]
    have hnot : ¬ (P + i.val < P) := by omega
    simp only [hnot, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_allOnes]
  rw [hlo, hhi]
  decide

theorem ngoalP_differs {P : ℕ} (i : Fin P) : differsP i (~~~goalP P) := by
  have h := goalP_differs i
  unfold differsP at h ⊢
  have h1 : P + i.val < P + P := by omega
  have h2 : i.val < P + P := by omega
  simp only [BitVec.getLsbD_not, h1, h2, decide_true, Bool.true_and]
  intro heq
  apply h
  cases a : (goalP P).getLsbD (P + i.val) <;> cases b : (goalP P).getLsbD i.val <;> simp_all

theorem ops_differsP {P : ℕ} (i : Fin P) (a b z : WP P) (hz : z ∈ basicOps a b)
    (hd : differsP i z) : differsP i a ∨ differsP i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differsP at ha hb
  simp only [not_not] at ha hb
  have hi : P + i.val < P + P := by omega
  have hi' : i.val < P + P := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cutsP_spec {P : ℕ} (ws : List (WP P)) (i : Fin P) :
    (cutsP ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differsP i w := by
  induction ws with
  | nil => simp [cutsP]
  | cons a rest ih =>
    change (sepP a ||| cutsP rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sepP, i.isLt, differsP, Nat.add_comm, bx]

theorem cutsP_full {P : ℕ} {g : WP P} (hg : g = goalP P ∨ g = ~~~goalP P) {k : ℕ} {ws : List (WP P)}
    (h : live basicOps g k ws.toFinset) : cutsP ws = BitVec.allOnes P := by
  have hd : ∀ i, differsP i g := by
    intro i; rcases hg with rfl | rfl
    · exact goalP_differs i
    · exact ngoalP_differs i
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differsP ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops_differsP ⟨j, hj⟩) h
  have hbit := (cutsP_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

def keepChoices {α : Type} (a b : α) (r : List α) : List (List α) :=
  [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {α : Type} [DecidableEq α] {ws r : List α} {a b : α} {needed : Finset α}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {α : Type} [DecidableEq α] {goal : α} {ws : List α} (hn : ws.Nodup)
    (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatchP (P : ℕ) (extra : ℕ) (next : ℕ → List (WP P) → Bool) (a b : WP P) (r : List (WP P)) : Bool :=
  let base := cutsP r
  let full := BitVec.allOnes P
  (ops a b).any fun w =>
    let v := sepP w ||| base
    ((v == full) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sepP a == full) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sepP b == full) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sepP a ||| sepP b == full) && next (extra - 2) (w :: a :: b :: r))

def optimizedP (P : ℕ) : ℕ → ℕ → List (WP P) → Bool
  | 0, _, ws => (ws == [goalP P] || ws == [~~~goalP P])
  | k + 1, extra, ws => (ws == [goalP P] || ws == [~~~goalP P]) ||
    (pairs ws).any (fun (a, b, r) => dispatchP P extra (optimizedP P k) a b r)

theorem dispatchP_complete {P k extra : ℕ} {a b z : WP P} {r kept : List (WP P)}
    (next : ℕ → List (WP P) → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cutsP (z :: kept) = BitVec.allOnes P) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatchP P extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cutsP, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimizedP_complete {P : ℕ} {g : WP P} (hg : g = goalP P ∨ g = ~~~goalP P) (n : ℕ)
    (ws : List (WP P)) (extra : ℕ) (hn : ws.Nodup) (room : extra + ws.length = n + 1)
    (h : live basicOps g n ws.toFinset) : optimizedP P n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimizedP, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimizedP, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : WP P} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatchP P extra (optimizedP P k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatchP_complete (k := k) (extra := extra) (optimizedP P k) hop hk (by omega)
          (by omega) (cutsP_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimizedP, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap,
          go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def searchP (P : ℕ) (n : ℕ) (inputs : List (WP P)) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n + 1) && (cutsP ws == BitVec.allOnes P) && optimizedP P n (n + 1 - ws.length) ws

theorem searchP_complete {P : ℕ} {g : WP P} (hg : g = goalP P ∨ g = ~~~goalP P) (n : ℕ)
    (inputs : List (WP P)) (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) :
    searchP P n inputs = true := by
  classical
  obtain ⟨s, hs, hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws, List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cutsP_full hg hl',
      optimizedP_complete hg n ws _ hnd (by omega : n + 1 - ws.length + ws.length = n + 1) hl']⟩

theorem goalP_ne_const {P : ℕ} (hP : 0 < P) :
    goalP P ≠ 0 ∧ goalP P ≠ ~~~0 ∧ ~~~goalP P ≠ 0 ∧ ~~~goalP P ≠ ~~~0 := by
  have hd := goalP_differs ⟨0, hP⟩
  have hdn := ngoalP_differs ⟨0, hP⟩
  have h0 : ¬ differsP ⟨0, hP⟩ (0 : WP P) := by unfold differsP; simp
  have h1 : ¬ differsP ⟨0, hP⟩ (~~~(0 : WP P)) := by
    unfold differsP
    have hb : 0 < P + P := by omega
    simp [hb]
    omega
  exact ⟨fun e => h0 (e ▸ hd), fun e => h1 (e ▸ hd), fun e => h0 (e ▸ hdn), fun e => h1 (e ▸ hdn)⟩

theorem signed_rejectP {P k : ℕ} (hP : 0 < P) {ws : List (WP P)} (hn : ws.Nodup)
    (hf : searchP P k ws = false) {t : WP P} (ht : t = goalP P ∨ t = ~~~goalP P)
    (h : SignedBuild k ws.toFinset t) : False := by
  have nt := goalP_ne_const hP
  rcases ht with rfl | rfl
  all_goals
    rcases h with h | h | h | h
    · first | exact nt.1 h | exact nt.2.2.1 h
    · first | exact nt.2.1 h | exact nt.2.2.2 h
    · exact Bool.noConfusion (hf.symm.trans (searchP_complete (by simp) k ws hn h))
    · exact Bool.noConfusion (hf.symm.trans (searchP_complete (by simp) k ws hn h))

end SearchP

section K4Base

def k4_16_vars : List (BitVec 16) := [0xaaaa#16, 0xcccc#16, 0xf0f0#16, 0xff00#16]
def k4v16 (i : Fin 4) : BitVec 16 := k4_16_vars.getD i.val 0
def k4_tt16 : BitVec 16 := 0xfee8#16

def k4a : WP 30 := 0x2cb2cb2c0000fc0#60
def k4b : WP 30 := 0x55555554003f000#60
def k4c : WP 30 := 0x9a69a6980fc0000#60
def k4d : WP 30 := 0xe38e38e3f000000#60
def k4inputs : List (WP 30) := [k4a, k4b, k4c, k4d]

def k4Base60 : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8,
    3, 5, 6, 9, 10, 12, 3, 5, 6, 9, 10, 12, 3, 5, 6, 9, 10, 12, 3, 5, 6, 9, 10, 12, 3, 5, 6, 9, 10, 12]

def permBits4 (p0 p1 p2 p3 : ℕ) (y : ℕ) : Fin 16 :=
  let m := (if y.testBit 0 then 1 <<< p0 else 0) |||
           (if y.testBit 1 then 1 <<< p1 else 0) |||
           (if y.testBit 2 then 1 <<< p2 else 0) |||
           (if y.testBit 3 then 1 <<< p3 else 0)
  ⟨m % 16, Nat.mod_lt _ (by decide)⟩

def k4RowMap (i j : Fin 4) (k : Fin 60) : Fin 16 :=
  let rem := (List.finRange 4).filter (fun q => q != i && q != j)
  permBits4 i.val j.val (rem.getD 0 0).val (rem.getD 1 0).val (k4Base60[k.val]!)

def k4Proj (i j : Fin 4) : BitVec 16 → WP 30 := selectRows (k4RowMap i j)

def checkK4Proj : Bool :=
  (List.finRange 4).all fun i =>
    (List.finRange 4).all fun j =>
      if i == j then true else
        (k4Proj i j k4_tt16 == goalP 30) &&
        (k4Proj i j (k4v16 i) == k4a) &&
        (k4Proj i j (k4v16 j) == k4b) &&
        k4_16_vars.all fun w => k4inputs.any fun d => k4Proj i j w == d

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem k4Proj_ok : checkK4Proj = true := by decide +kernel

theorem k4_16_cover {w : BitVec 16} (hw : w ∈ k4_16_vars.toFinset) : ∃ i : Fin 4, k4v16 i = w := by
  rw [List.mem_toFinset] at hw
  simp only [k4_16_vars, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩

theorem k4_16_not_target : ∀ i : Fin 4, k4v16 i ≠ k4_tt16 ∧ k4v16 i ≠ ~~~k4_tt16 := by decide

theorem k4_nd0 : ((k4a &&& k4b) :: k4inputs).Nodup := by decide
theorem k4_nd1 : ((k4a ||| k4b) :: k4inputs).Nodup := by decide
theorem k4_nd2 : ((k4a &&& ~~~k4b) :: k4inputs).Nodup := by decide

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem k4_s0 : searchP 30 5 ((k4a &&& k4b) :: k4inputs) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem k4_s1 : searchP 30 5 ((k4a ||| k4b) :: k4inputs) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem k4_s2 : searchP 30 5 ((k4a &&& ~~~k4b) :: k4inputs) = false := by decide +kernel

theorem k4_step_aux (i j : Fin 4) (hij : i ≠ j) {t z : BitVec 16}
    (ht : t = k4_tt16 ∨ t = ~~~k4_tt16)
    (hz : z = k4v16 i &&& k4v16 j ∨ z = k4v16 i ||| k4v16 j ∨ z = k4v16 i &&& ~~~k4v16 j)
    (rest : Finset (BitVec 16)) (hsub : rest ⊆ k4_16_vars.toFinset)
    (tail : live basicOps t 5 (insert z rest)) : False := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp k4Proj_ok i (List.mem_finRange i)) j (List.mem_finRange j)
  have hne : (i == j) = false := beq_false_of_ne hij
  simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨⟨⟨hg, hi⟩, hj⟩, hall⟩ := h1
  let f := k4Proj i j
  have hi' : f (k4v16 i) = k4a := hi
  have hj' : f (k4v16 j) = k4b := hj
  have hAnd : ∀ u v, f (u &&& v) = f u &&& f v := selectRows_land (k4RowMap i j)
  have hOr : ∀ u v, f (u ||| v) = f u ||| f v := selectRows_lor (k4RowMap i j)
  have hNot : ∀ u, f (~~~u) = ~~~f u := selectRows_neg (k4RowMap i j)
  have hm := ops_map_of hAnd hOr hNot
  have hft : f t = goalP 30 ∨ f t = ~~~goalP 30 := by
    rcases ht with rfl | rfl
    · exact .inl hg
    · exact .inr ((hNot k4_tt16).trans (congrArg (fun u : WP 30 => ~~~u) hg))
  have hrest : ∀ u ∈ rest, holds k4inputs.toFinset (f u) := by
    intro u hu
    have hallu := List.all_eq_true.mp hall u (List.mem_toFinset.mp (hsub hu))
    obtain ⟨d, hd, heq⟩ := List.any_eq_true.mp hallu
    exact .inr (.inr ⟨d, List.mem_toFinset.mpr hd, .inl (beq_iff_eq.mp heq)⟩)
  have run_with (w0 : WP 30) (hfw : f z = w0) (hnd : (w0 :: k4inputs).Nodup)
      (hsch : searchP 30 5 (w0 :: k4inputs) = false) : False := by
    apply signed_rejectP (by decide) hnd hsch hft
    apply live_transport hm tail
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hr
    · exact .inr (.inr ⟨w0, List.mem_toFinset.mpr (List.mem_cons_self ..), .inl hfw⟩)
    · exact holds_mono (by intro x hx; exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp hx))) (hrest u hr)
  rcases hz with rfl | rfl | rfl
  · exact run_with (k4a &&& k4b) (by rw [hAnd, hi', hj']) k4_nd0 k4_s0
  · exact run_with (k4a ||| k4b) (by rw [hOr, hi', hj']) k4_nd1 k4_s1
  · exact run_with (k4a &&& ~~~k4b) (by rw [hAnd, hNot, hi', hj']) k4_nd2 k4_s2

theorem k4_no6_16 (t : BitVec 16) (ht : t = k4_tt16 ∨ t = ~~~k4_tt16)
    (hb : build basicOps t 6 k4_16_vars.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  rcases first_live (k := 5) hl with done | ⟨a, ha, b, hb', hab, z, hz, _, rest, he, tail⟩
  · have mt := hs (show t ∈ s by simp [done])
    obtain ⟨i, hi⟩ := k4_16_cover mt
    rcases ht with rfl | rfl
    · exact (k4_16_not_target i).1 hi
    · exact (k4_16_not_target i).2 hi
  · obtain ⟨i, rfl⟩ := k4_16_cover (hs ha)
    obtain ⟨j, rfl⟩ := k4_16_cover (hs hb')
    have hij : i ≠ j := fun e => hab (congrArg k4v16 e)
    have hsub : rest ⊆ k4_16_vars.toFinset := fun u hu =>
      hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact k4_step_aux i j hij ht (.inl rfl) rest hsub tail
    · exact k4_step_aux i j hij ht (.inr (.inl rfl)) rest hsub tail
    · exact k4_step_aux i j hij ht (.inr (.inr rfl)) rest hsub tail
    · exact k4_step_aux j i hij.symm ht (.inr (.inr rfl)) rest hsub tail

end K4Base

section Compile128

abbrev W128 := BitVec 128

def bit128 (k : Fin 128) (z : W128) : Bool := z[k.val]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read_bit128 (w : List W128) (i : ℕ) (k : Fin 128) :
    (w.map (bit128 k)).getD i false = bit128 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit128]

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W128) (g : Gate) : W128 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W128) (g : Gate) (hg : legal g) (k : Fin 128) :
    step (w.map (bit128 k)) g = (w ++ [action w g]).map (bit128 k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W128)[k.val] = false := by change (0#128)[k.val] = false; simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit128, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit128, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : ℕ := (gs.filter isBinary).length

theorem available_read {av : Finset W128} {w : List W128} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W128) (av : Finset W128) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    show ∀ x : W128, x ||| (0 : W128) = x from fun x => BitVec.or_zero,
    show ∀ x : W128, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (target : W128) (hnt0 : target ≠ 0) (hnt1 : target ≠ ~~~0)
    (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W128) (av : Finset W128) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit128 k))).getD out false = bit128 k target) :
    ∃ t, (t = target ∨ t = ~~~target) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit128, bit128] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim (hnt0 zero)
    · exact False.elim (hnt1 ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun u : W128 => ~~~u) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit128 k))).getD out false = bit128 k target := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W128) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

end Compile128

theorem sb_not {n k : ℕ} {av : Finset (BitVec n)} {z : BitVec n}
    (h : SignedBuild k av z) : SignedBuild k av (~~~z) := by
  rcases h with rfl | rfl | h | h
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not] using h)))
  · exact .inr (.inr (.inl h))

theorem cut_signed {n m k : ℕ} (tgt : BitVec n) (tgt' : BitVec m)
    (ls : List (BitVec n)) (dst : List (BitVec m))
    (p : BitVec n) (a b : Fin n) (f : BitVec n → BitVec m)
    (hm : ∀ x y z, z ∈ basicOps x y → f z ∈ basicOps (f x) (f y))
    (hNot : ∀ z, f (~~~z) = ~~~f z)
    (hnc : tgt ≠ 0 ∧ tgt ≠ ~~~0) (hnc' : tgt' ≠ 0 ∧ tgt' ≠ ~~~0)
    (hd : bitDiff a b tgt)
    (hu : ∀ w ∈ ls, bitDiff a b w → w = p)
    (hp : f p = 0 ∨ f p = ~~~0) (ht : f tgt = tgt')
    (supply : ∀ w ∈ ls, holds dst.toFinset (f w))
    (built : SignedBuild k ls.toFinset tgt) :
    SignedBuild (k - 1) dst.toFinset tgt' := by
  obtain ⟨t, he, run⟩ := unwrap_sb hnc.1 hnc.2 built
  obtain ⟨s, hs, liveRun⟩ := compress run
  have hdiff : bitDiff a b t := by
    rcases he with rfl | rfl
    · exact hd
    · exact bitDiff_not hd
  have present := live_has_unique_sep hs liveRun a b hdiff hu
  have heq : f t = tgt' ∨ f t = ~~~tgt' := by
    rcases he with rfl | rfl
    · exact .inl ht
    · exact .inr (by rw [hNot, ht])
  have hnon : f t ≠ 0 ∧ f t ≠ ~~~0 := by
    rcases heq with h | h <;> rw [h]
    · exact hnc'
    · exact not_const_of_neg hnc'
  obtain ⟨_, result⟩ := live_transport_save_const hm liveRun present hp hnon
    (fun w hw => supply w (List.mem_toFinset.mp (hs hw)))
  rcases heq with h | h
  · rwa [h] at result
  · rw [h] at result
    simpa only [BitVec.not_not] using sb_not result

def pack (hi lo : ℕ) : W128 := BitVec.ofNat 128 (hi * 2^64 + lo)
def rail0 : W128 := pack 0 4294901760
def rail1 : W128 := pack 0 281470681743360
def rail2 : W128 := pack 12297829382473034410 12297829382473034410
def rail3 : W128 := pack 0 18446462598732840960
def rail4 : W128 := pack 65535 0
def rail5 : W128 := pack 14757395258967641292 14757395258967641292
def rail6 : W128 := pack 17361641481138401520 17361641481138401520
def rail7 : W128 := pack 18374966859414961920 18374966859414961920
def avail0 : List W128 := [rail0, rail1, rail2, rail3, rail4, rail5, rail6, rail7]
def tgt0 : W128 := pack 18368211356893118440 18372714973718445800
def avail1 : List W128 := [rail1, rail2, rail3, rail4, rail5, rail6, rail7]
def tgt1 : W128 := pack 18368211356893118440 18372714973700357864
def avail2 : List W128 := [rail2, rail3, rail4, rail5, rail6, rail7]
def tgt2 : W128 := pack 18368211356893118440 18372714956520488680
def avail3 : List W128 := [rail2, rail4, rail5, rail6, rail7]
def tgt3 : W128 := pack 18368211356893118440 18368211356893118184

def pinRows (code : ℕ) (k : Fin 128) : Fin 128 :=
  if k.val / 16 = code then ⟨k.val % 16, by have := Nat.mod_lt k.val (show 0 < 16 by decide); omega⟩
  else k

def lastRows (k : Fin 16) : Fin 128 := ⟨k.val, by have := k.isLt; omega⟩

theorem cut0 {s : ℕ} (h : SignedBuild s avail0.toFinset tgt0) :
    SignedBuild (s - 1) avail1.toFinset tgt1 := by
  exact cut_signed tgt0 tgt1 avail0 avail1 rail0 2 18 (selectRows (pinRows 1))
    (ops_map_of (selectRows_land (pinRows 1)) (selectRows_lor (pinRows 1)) (selectRows_neg (pinRows 1)))
    (selectRows_neg (pinRows 1)) (by decide +kernel) (by decide +kernel)
    (by unfold bitDiff; decide +kernel)
    (sep_of_all _ _ _ _ (by decide +kernel)) (.inl (by decide +kernel)) (by decide +kernel)
    (map_holds_list _ _ _ (by decide +kernel)) h

theorem cut1 {s : ℕ} (h : SignedBuild s avail1.toFinset tgt1) :
    SignedBuild (s - 1) avail2.toFinset tgt2 := by
  exact cut_signed tgt1 tgt2 avail1 avail2 rail1 2 34 (selectRows (pinRows 2))
    (ops_map_of (selectRows_land (pinRows 2)) (selectRows_lor (pinRows 2)) (selectRows_neg (pinRows 2)))
    (selectRows_neg (pinRows 2)) (by decide +kernel) (by decide +kernel)
    (by unfold bitDiff; decide +kernel)
    (sep_of_all _ _ _ _ (by decide +kernel)) (.inl (by decide +kernel)) (by decide +kernel)
    (map_holds_list _ _ _ (by decide +kernel)) h

theorem cut2 {s : ℕ} (h : SignedBuild s avail2.toFinset tgt2) :
    SignedBuild (s - 1) avail3.toFinset tgt3 := by
  exact cut_signed tgt2 tgt3 avail2 avail3 rail3 4 52 (selectRows (pinRows 3))
    (ops_map_of (selectRows_land (pinRows 3)) (selectRows_lor (pinRows 3)) (selectRows_neg (pinRows 3)))
    (selectRows_neg (pinRows 3)) (by decide +kernel) (by decide +kernel)
    (by unfold bitDiff; decide +kernel)
    (sep_of_all _ _ _ _ (by decide +kernel)) (.inl (by decide +kernel)) (by decide +kernel)
    (map_holds_list _ _ _ (by decide +kernel)) h

theorem cut3 {s : ℕ} (h : SignedBuild s avail3.toFinset tgt3) :
    SignedBuild (s - 1) k4_16_vars.toFinset k4_tt16 := by
  exact cut_signed tgt3 k4_tt16 avail3 k4_16_vars rail4 8 72 (selectRows lastRows)
    (ops_map_of (selectRows_land lastRows) (selectRows_lor lastRows) (selectRows_neg lastRows))
    (selectRows_neg lastRows) (by decide +kernel) (by decide +kernel)
    (by unfold bitDiff; decide +kernel)
    (sep_of_all _ _ _ _ (by decide +kernel)) (.inl (by decide +kernel)) (by decide +kernel)
    (map_holds_list _ _ _ (by decide +kernel)) h

def edgeList : List ℕ := [0,4,1,4,0,5,1,5,2,5,0,6,2,6,3,6,5,6,0,7,2,7,4,7,5,7,6,7]

def edgeValue (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

set_option maxRecDepth 12000 in
theorem sample : ∀ k : Fin 128,
    edgeValue (fun i => bit128 k (avail0.getD i.val 0)) = bit128 k tgt0 := by
  decide +kernel

theorem binary_floor (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = edgeValue x) :
    11 ≤ binaryCost gs := by
  by_contra! short
  have init : ∀ u ∈ avail0, holds avail0.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 128) :
      (gs.foldl step (avail0.map (bit128 k))).getD o false = bit128 k tgt0 := by
    let x (i : Fin 8) : Bool := bit128 k (avail0.getD i.val 0)
    have width : avail0.length = 8 := rfl
    have same : List.ofFn x = avail0.map (bit128 k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < avail0.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (avail0.map (bit128 k)) = bit128 k tgt0
    rw [← same, correct]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile tgt0 (by decide +kernel) (by decide +kernel)
    gs o hg avail0 avail0.toFinset init evaluate
  have signed : SignedBuild (binaryCost gs) avail0.toFinset tgt0 := by
    rcases ht with rfl | rfl
    · exact .inr (.inr (.inl run))
    · exact .inr (.inr (.inr run))
  have low := cut3 (cut2 (cut1 (cut0 signed)))
  have bad : SignedBuild 6 k4_16_vars.toFinset k4_tt16 := sb_le (by omega) low
  obtain ⟨z, hz, path⟩ := unwrap_sb (by decide) (by decide) bad
  exact k4_no6_16 z hz path

theorem with_not (gs : List Gate) (h : ∃ g ∈ gs, g.op = .not) :
    binaryCost gs < gs.length := by
  induction gs with
  | nil => simp at h
  | cons a t ih =>
    have bound : binaryCost t ≤ t.length := List.length_filter_le _ _
    rcases h with ⟨g,hg,hop⟩
    rcases List.mem_cons.mp hg with eq | hmem
    · have ha : a.op = GateOp.not := eq ▸ hop
      have n : isBinary a = false := by simp [isBinary,ha]
      simpa [binaryCost,n] using Nat.lt_succ_of_le bound
    · have rest := ih ⟨g,hmem,hop⟩
      cases ha : isBinary a with
      | false => simpa [binaryCost,ha] using Nat.lt_succ_of_le bound
      | true => simpa [binaryCost,ha] using Nat.succ_lt_succ rest

def replacement : List Gate :=
  [⟨.or,[5,4]⟩,⟨.or,[2,0]⟩,⟨.or,[5,7]⟩,⟨.or,[0,7]⟩,
   ⟨.or,[1,11]⟩,⟨.or,[9,3]⟩,⟨.or,[10,13]⟩,⟨.and,[8,12]⟩,
   ⟨.and,[6,14]⟩,⟨.and,[9,10]⟩,⟨.or,[15,16]⟩,⟨.or,[18,17]⟩]

theorem replacement_basis : ∀ g ∈ replacement,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [replacement]

set_option maxRecDepth 20000 in
theorem replacement_eval : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨replacement,19⟩ (List.ofFn x) = edgeValue x := by
  decide +kernel

theorem equal_decisions {p : Prop} (a b : Decidable p) : @decide p a = @decide p b :=
  congrArg (fun d => @decide p d) (Subsingleton.elim a b)

end PEqualNP.Outside.L_meta_31055

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_31055 in
theorem PEqualNP.Outside.L_meta_31055 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by

  intro gs o alphabet _ correct
  by_cases h : ∃ g ∈ gs, g.op = GateOp.not
  · have agrees (x : Fin 8 → Bool) : Circuit.eval ⟨gs,o⟩ (List.ofFn x) = edgeValue x :=
      (correct x).trans (equal_decisions _ _)
    have lower := binary_floor gs o alphabet agrees
    have paid := with_not gs h
    refine ⟨replacement,19,replacement_basis,?_,fun x => (replacement_eval x).trans (equal_decisions _ _)⟩
    change 12 ≤ gs.length
    omega
  · refine ⟨gs,o,?_,le_rfl,correct⟩
    intro g hg
    rcases alphabet g hg with ⟨op,arity⟩
    rcases op with p | p | p
    · exact ⟨Or.inl p,arity⟩
    · exact ⟨Or.inr p,arity⟩
    · exact (h ⟨g,hg,p⟩).elim
