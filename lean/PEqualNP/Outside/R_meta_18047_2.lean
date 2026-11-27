import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18047_2
    (hX2Props :
      have x1 : Finset ℕ := Finset.range (40 : ℕ);
have x2 : Finset (Finset ℕ) := Finset.image (fun (x2 : ℕ) => {x3 ∈ x1 | x2.testBit x3 = Bool.true}) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].toFinset;
x2.card ≤ (11 : ℕ) ∧ ∀ s ∈ x2, s ⊆ x1)
    (hBounded :
      have x1 : Finset ℕ := Finset.range (40 : ℕ); have x2 : Finset (Finset ℕ) := Finset.image (fun (x2 : ℕ) => {x3 ∈ x1 | x2.testBit x3 = Bool.true}) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].toFinset; have x3 : Finset ℕ := Insert.insert (40 : ℕ) (Finset.range (16 : ℕ)); ∀ (x4 x5 : Finset ℕ) (x6 x7 : Finset (Finset ℕ)),   have x8 : Finset (Finset ℕ) := Insert.insert (Insert.insert (40 : ℕ) x4) (Insert.insert (Insert.insert (41 : ℕ) x5) x2);   have x9 : Finset (Finset ℕ) := {x9 ∈ x6 | x9 ⊆ x1};   have x10 : Finset (Finset ℕ) := Finset.image₂ (fun (x10 x11 : Finset ℕ) => x10 ∩ x11) x9 x9;   have x11 : Finset (Finset ℕ) := Finset.image₂ (fun (x11 x12 : Finset ℕ) => x11 ∩ x12 ∩ x1 ∪ if {(40 : ℕ), (41 : ℕ)} ⊆ x11 ∪ x12 then {(40 : ℕ)} else ∅) x6 x6;   x4 ∈ x10 → x5 ∈ x10 → x4 ⊆ x1 → x5 ⊆ x1 → (∀ s ∈ x6, s ⊆ Finset.range (42 : ℕ)) → x6.card ≤ (31 : ℕ) → (1 : ℕ) ≤ x7.card → ¬x4 ⊆ Finset.range (16 : ℕ) → ¬x5 ⊆ Finset.range (16 : ℕ) → (∀ x16 ∈ x6 \ x8, ∃ x18 ∈ x6, ∃ x19 ∈ x6, x18 ⊂ x16 ∧ x19 ⊂ x16 ∧ x16 = x18 ∪ x19) → (∀ x17 ∈ x6, {x19 ∈ x6 ∩ x8 | x19 ⊆ x17}.biUnion id = x17) → (1 : ℕ) ≤ (x6 \ x8).card → (x6 \ x8).card ≤ (18 : ℕ) → x7.card ≤ (9 : ℕ) → x7.biUnion id = x3 → (∀ x22 ∈ x7, x22 ∈ x11 ∧ x22 ⊆ x3 ∧ ∀ x24 ∈ x11, x24 ⊆ x3 → x22 ⊆ x24 → x24 = x22) → (∀ x23 ∈ x7, ∃ x25 ∈ x23, ∀ x26 ∈ x7, x25 ∈ x26 → x26 = x23) → (21 : ℕ) ≤ (x6 \ x8).card + (2 : ℕ) * x7.card) :
    have x1 : Finset ℕ := Finset.range (40 : ℕ); have x2 : Finset (Finset ℕ) := Finset.image (fun (x2 : ℕ) => {x3 ∈ x1 | x2.testBit x3 = Bool.true}) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].toFinset; have x3 : Finset ℕ := Insert.insert (40 : ℕ) (Finset.range (16 : ℕ)); ∀ (x4 x5 : Finset ℕ) (x6 x7 : Finset (Finset ℕ)),   have x8 : Finset (Finset ℕ) := Insert.insert (Insert.insert (40 : ℕ) x4) (Insert.insert (Insert.insert (41 : ℕ) x5) x2);   have x9 : Finset (Finset ℕ) := {x9 ∈ x6 | x9 ⊆ x1};   have x10 : Finset (Finset ℕ) := Finset.image₂ (fun (x10 x11 : Finset ℕ) => x10 ∩ x11) x9 x9;   have x11 : Finset (Finset ℕ) := Finset.image₂ (fun (x11 x12 : Finset ℕ) => x11 ∩ x12 ∩ x1 ∪ if {(40 : ℕ), (41 : ℕ)} ⊆ x11 ∪ x12 then {(40 : ℕ)} else ∅) x6 x6;   x4 ∈ x10 → x5 ∈ x10 → ¬x4 ⊆ Finset.range (16 : ℕ) → ¬x5 ⊆ Finset.range (16 : ℕ) → (∀ x16 ∈ x6 \ x8, ∃ x18 ∈ x6, ∃ x19 ∈ x6, x18 ⊂ x16 ∧ x19 ⊂ x16 ∧ x16 = x18 ∪ x19) → (∀ x17 ∈ x6, {x19 ∈ x6 ∩ x8 | x19 ⊆ x17}.biUnion id = x17) → (1 : ℕ) ≤ (x6 \ x8).card → (x6 \ x8).card ≤ (18 : ℕ) → x7.card ≤ (9 : ℕ) → x7.biUnion id = x3 → (∀ x22 ∈ x7, x22 ∈ x11 ∧ x22 ⊆ x3 ∧ ∀ x24 ∈ x11, x24 ⊆ x3 → x22 ⊆ x24 → x24 = x22) → (∀ x23 ∈ x7, ∃ x25 ∈ x23, ∀ x26 ∈ x7, x25 ∈ x26 → x26 = x23) → (21 : ℕ) ≤ (x6 \ x8).card + (2 : ℕ) * x7.card :=
  fun x4 x5 x6 x7 hx4 hx5 hnot4 hnot5 hgen hbi hlb hub hx7c hx7u hmax hpriv => by
    let x1 : Finset ℕ := Finset.range (40 : ℕ)
    let x2 : Finset (Finset ℕ) := Finset.image (fun (x2 : ℕ) => {x3 ∈ x1 | x2.testBit x3 = Bool.true})
      [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ),
       (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ),
       (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].toFinset
    let x8 : Finset (Finset ℕ) := Insert.insert (Insert.insert (40 : ℕ) x4) (Insert.insert (Insert.insert (41 : ℕ) x5) x2)
    have hx4_sub : x4 ⊆ Finset.range (40 : ℕ) := by
      rcases Finset.mem_image₂.mp hx4 with ⟨a, ha, b, _, rfl⟩
      exact Finset.inter_subset_left.trans (Finset.mem_filter.mp ha).2
    have hx5_sub : x5 ⊆ Finset.range (40 : ℕ) := by
      rcases Finset.mem_image₂.mp hx5 with ⟨a, ha, b, _, rfl⟩
      exact Finset.inter_subset_left.trans (Finset.mem_filter.mp ha).2
    have hx2_card : x2.card ≤ (11 : ℕ) := hX2Props.1
    have hx2_sub : ∀ s ∈ x2, s ⊆ Finset.range (40 : ℕ) := hX2Props.2
    have hx8_sub : ∀ s ∈ x8, s ⊆ Finset.range (42 : ℕ) := by
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs1
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz4
        · exact Finset.mem_range.mpr (by decide)
        · exact Finset.mem_range.mpr (Nat.lt_trans (Finset.mem_range.mp (hx4_sub hz4)) (by decide))
      · rcases Finset.mem_insert.mp hs1 with rfl | hs2
        · intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz5
          · exact Finset.mem_range.mpr (by decide)
          · exact Finset.mem_range.mpr (Nat.lt_trans (Finset.mem_range.mp (hx5_sub hz5)) (by decide))
        · intro z hz
          exact Finset.mem_range.mpr (Nat.lt_trans (Finset.mem_range.mp (hx2_sub s hs2 hz)) (by decide))
    have hx6_sub : ∀ s ∈ x6, s ⊆ Finset.range (42 : ℕ) := by
      intro s hs
      rw [← hbi s hs]
      intro z hz
      rcases Finset.mem_biUnion.mp hz with ⟨t, ht, hzt⟩
      exact hx8_sub t (Finset.mem_inter.mp (Finset.mem_filter.mp ht).1).2 hzt
    have hx8_card : x8.card ≤ (13 : ℕ) := by
      have hc1 : x8.card ≤ (Insert.insert (Insert.insert (41 : ℕ) x5) x2).card + 1 := Finset.card_insert_le _ _
      have hc2 : (Insert.insert (Insert.insert (41 : ℕ) x5) x2).card ≤ x2.card + 1 := Finset.card_insert_le _ _
      omega
    have hx6_card : x6.card ≤ (31 : ℕ) := by
      have hsdiff : x6.card ≤ (x6 \ x8).card + x8.card := by
        have hsub : x6 ⊆ (x6 \ x8) ∪ x8 := by
          rw [Finset.sdiff_union_self_eq_union]
          exact Finset.subset_union_left
        exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      exact Nat.le_trans hsdiff (Nat.add_le_add hub hx8_card)
    have hx7_pos : (1 : ℕ) ≤ x7.card := by
      have h40 : (40 : ℕ) ∈ Insert.insert (40 : ℕ) (Finset.range (16 : ℕ)) := Finset.mem_insert_self _ _
      rw [← hx7u] at h40
      rcases Finset.mem_biUnion.mp h40 with ⟨s, hs, _⟩
      exact Finset.card_pos.mpr ⟨s, hs⟩
    exact hBounded x4 x5 x6 x7 hx4 hx5 hx4_sub hx5_sub hx6_sub hx6_card hx7_pos hnot4 hnot5 hgen hbi hlb hub hx7c hx7u hmax hpriv
