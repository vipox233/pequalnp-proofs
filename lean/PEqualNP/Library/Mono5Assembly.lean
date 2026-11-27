import PEqualNP.Library.Mono5.CoverA
import PEqualNP.Library.Mono5.CoverB
import PEqualNP.Library.Mono5.CoverC
import PEqualNP.MetaComplexity.Helpers.LocClean

/-! Data of `L-meta-8613`, written by notes/data/table2/statements/mono5/lean_cover.py. The pieces assembled: every monotone table of five inputs is a listed table after relabelling. -/

namespace PEqualNP.Library.Mono5

theorem monoTables_five : monoTables 5 = step 16 E4 (c00 ++ (c01 ++ (c02 ++ (c03 ++ (c04 ++ (c05 ++ (c06 ++ (c07 ++ (c08 ++ (c09 ++ (c10 ++ (c11)))))))))))) := by
  rw [← E4_split]
  show step 16 (monoTables 4) (monoTables 4) = _
  rw [monoTables_four]

theorem cover : ∀ t ∈ monoTables 5, Good reps t := by
  intro t ht
  rw [monoTables_five] at ht
  simp only [step_append, List.mem_append] at ht
  rcases ht with h | h | h | h | h | h | h | h | h | h | h | h
  · exact cover00 t h
  · exact cover01 t h
  · exact cover02 t h
  · exact cover03 t h
  · exact cover04 t h
  · exact cover05 t h
  · exact cover06 t h
  · exact cover07 t h
  · exact cover08 t h
  · exact cover09 t h
  · exact cover10 t h
  · exact cover11 t h

end PEqualNP.Library.Mono5

/-! L-meta-8613: the five-input assembly. The 210 listed claims give the claim for every monotone
function of five inputs: its table is a listed one after relabelling the inputs
(`Mono5.cover`), and relabelling keeps both sizes. -/

set_option maxRecDepth 20000 in
open PEqualNP.Library.Mono5 in
theorem PEqualNP.Library.Mono5Assembly : (∀ T ∈ ({0xa8808000, 0xa8888880, 0xaaa8a880, 0xe8808080, 0xe8808880, 0xe880a880, 0xe880e880, 0xe8888880, 0xe888a080, 0xe888a880, 0xe888e080, 0xe888e880, 0xe8a8a800, 0xe8a8a880, 0xe8a8a888, 0xe8a8c880, 0xe8a8e800, 0xe8a8e880, 0xe8a8e888, 0xe8e8e880, 0xeaa8a880, 0xeaa8a888, 0xeaa8a8a8, 0xeaa8aaa8, 0xeaa8c000, 0xeaa8c080, 0xeaa8c880, 0xeaa8c888, 0xeaa8e880, 0xeaa8e888, 0xeaa8e8a8, 0xeaaaaaa8, 0xeaaac880, 0xeaaae880, 0xeaaaeaa8, 0xeac0e880, 0xeac8e000, 0xeac8e080, 0xeac8e880, 0xeac8e888, 0xeac8e8c0, 0xeae8e800, 0xeae8e888, 0xeae8e8a8, 0xeae8e8c0, 0xeae8e8c8, 0xeae8ea80, 0xeae8ea88, 0xeae8eaa8, 0xeaeaeaa8, 0xeee0e880, 0xeee0e8a0, 0xeee0eac0, 0xeee8e888, 0xeee8e8a0, 0xeee8e8a8, 0xeee8e8e0, 0xeee8eaa0, 0xeee8eaa8, 0xeee8eac0, 0xeee8eac8, 0xeee8eae0, 0xeee8eae8, 0xeeeaeaa0, 0xeeeaeaa8, 0xeeeaeac8, 0xeeeaeae0, 0xeeeaeae8, 0xfee8e880, 0xfee8e888, 0xfee8e8a8, 0xfee8e8e8, 0xfee8eaa8, 0xfee8eac0, 0xfee8eac8, 0xfee8eae8, 0xfee8eee0, 0xfee8eee8, 0xfee8fee8, 0xfeeaeaa8, 0xfeeaeaaa, 0xfeeaeac0, 0xfeeaeac8, 0xfeeaeae8, 0xfeeaece0, 0xfeeaece8, 0xfeeaeee0, 0xfeeaeee8, 0xfeeafcc8, 0xfeeafce8, 0xfeeafee8, 0xfeeeeee0, 0xfeeeeee8, 0xfeeeeeea, 0xfeeefaa8, 0xfeeefac0, 0xfeeefae8, 0xfeeefee8, 0xfefefee8, 0xfffefee8, 0xfffefeea, 0x00000000, 0xaaaaaaaa, 0x88888888, 0xeeeeeeee, 0xffffffff, 0x80808080, 0xa8a8a8a8, 0xeaeaeaea, 0xfefefefe, 0x80008000, 0x88808880, 0xa888a888, 0xaaa8aaa8, 0xeaaaeaaa, 0xeac0eac0, 0xeee0eee0, 0xeeeaeeea, 0xfeeefeee, 0xfffefffe, 0x80000000, 0x80808000, 0x88808080, 0x88888880, 0xa8888888, 0xa888a000, 0xa8a8a800, 0xa8a8a888, 0xaaa8a8a8, 0xaaaaaaa8, 0xe8e8e8e8, 0xeaaaaaaa, 0xeaaac000, 0xeac8eac8, 0xeaeaea00, 0xeaeaeaaa, 0xeaeaeac0, 0xeeeaeaea, 0xeeeeeee0, 0xeeeeeeea, 0xfeeeeeee, 0xfeeefaaa, 0xfefefeaa, 0xfefefeee, 0xfffefefe, 0xfffffffe, 0xa880a880, 0xa888a080, 0xe888e888, 0xe8a8e8a8, 0xeaaac080, 0xeaaac888, 0xeac8e0c0, 0xeac8eac0, 0xeae8eae8, 0xeaeaeac8, 0xeee0eae0, 0xeee8eee8, 0xeeeaece0, 0xeeeaeee0, 0xfeeafeea, 0xfeeefaea, 0x88808000, 0xa8808080, 0xa8808880, 0xa888a880, 0xa8a8a880, 0xaaa8a888, 0xe8888888, 0xe888a000, 0xe888a888, 0xe888e000, 0xe8a8a8a8, 0xe8a8c800, 0xe8a8c888, 0xe8e8e800, 0xe8e8e888, 0xe8e8e8a8, 0xeaa8eaa8, 0xeaaae888, 0xeaaae8a8, 0xeac0e8c0, 0xeac8e8c8, 0xeae8e8e8, 0xeae8ea00, 0xeae8eac0, 0xeae8eac8, 0xeaeaea80, 0xeaeaea88, 0xeaeaeae8, 0xeee0e8e0, 0xeee8e8e8, 0xeee8eee0, 0xeeeaeaaa, 0xeeeaeac0, 0xeeeaece8, 0xeeeaeee8, 0xeeeeeee8, 0xfeeaeaea, 0xfeeaeeea, 0xfeeafcc0, 0xfeeefac8, 0xfeeefee0, 0xfeeefeea, 0xfefefea8, 0xfefefeea, 0xfffefeee, 0xe8808000, 0xeae8e880, 0xeee8e880} : Finset ℕ), ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∀ f : (Fin 5 → Bool) → Bool, (∀ x y : Fin 5 → Bool, (∀ i, x i = true → y i = true) → f x = true → f y = true) → ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 f s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = f x := by
  intro H f hf s hs
  obtain ⟨σ, τ, hinv, T, hT, hbits⟩ := cover _ (mono_mem 5 f hf)
  have hg : (fun x : Fin 5 → Bool => f (x ∘ σ)) =
      (fun x : Fin 5 → Bool => Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) := by
    funext x
    have h1 := testBit_table 5 f (x ∘ σ)
    have h2 := hbits (idx x) (idx_lt x)
    simp only [testBit_idx] at h2
    rw [← h1]
    exact h2
  have hs' := PEqualNP.MetaComplexity.Helpers.PermInputs.relabel_size σ f s hs
  rw [hg] at hs'
  obtain ⟨C, hC1, hC2, hC3⟩ := H T (reps_sub T hT) s hs'
  have hm : PEqualNP.MetaComplexity.Loc.HasMonoSize 5
      (fun x : Fin 5 → Bool => Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s := by
    refine ⟨C, ?_, ?_, hC2, hC3⟩
    · intro g hg
      have h := (hC1 g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      refine ⟨?_, (hC1 g hg).2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · intro g hg
      have h := (hC1 g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h <;> rw [h] <;> exact fun e => by cases e
  obtain ⟨D, hD1, hD2, hD3, hD4⟩ :=
    PEqualNP.MetaComplexity.Loc.Clean.relabel_mono τ _ s hm
  refine ⟨D, ?_, hD3, ?_⟩
  · intro g hg
    have h := (hD1 g hg).1
    have hn := hD2 g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    refine ⟨?_, (hD1 g hg).2⟩
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hn
  · intro x
    rw [hD4 x]
    exact (congrFun hg (x ∘ τ)).symm.trans (by simp [Function.comp_def, hinv])
