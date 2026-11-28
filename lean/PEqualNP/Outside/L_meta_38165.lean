import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38165

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

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
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

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
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

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008241824 * 2 ^ 32 + 4008222880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x0008581b510c2d54#64 ++ 0x00021606d4430b55#64 ++ 0xf918f87ff31c7fff#64 ++ 0xbe463e1ffcc71fff#64 : BitVec 256),
   (0x0c632bb8c5619730#64 ++ 0x0318caee315865cc#64 ++ 0xfee73fb8cde39f32#64 ++ 0xffb9cfee3378e7cc#64 : BitVec 256),
   (0x930585c0ae02c2a8#64 ++ 0x24c161702b80b0aa#64 ++ 0xbb07c7c0fe03e3ff#64 ++ 0xeec1f1f03f80f8ff#64 : BitVec 256),
   (0x43b006ed0fb403c0#64 ++ 0x50ec01bb43ed00f0#64 ++ 0xd7f807ff0ffc03c0#64 ++ 0xf5fe01ffc3ff00f0#64 : BitVec 256),
   (0x23def0000adb7800#64 ++ 0x88f7bc0002b6de00#64 ++ 0xeffff8000ffffc00#64 ++ 0xfbfffe0003ffff00#64 : BitVec 256),
   (0x77ffff76f0000001#64 ++ 0x1dffffddbc000000#64 ++ 0x77fffffff0000000#64 ++ 0xddfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [6, 4]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0xf918f87ff31c7fff 0xbe463e1ffcc71fff

def z1 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0xfee73fb8cde39f32 0xffb9cfee3378e7cc

def z2 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0xeffff8000ffffc00 0xfbfffe0003ffff00

def z3 : W := mkw 0x23def0031adf7844 0x88f7bc00c6b7de11 0xeffff8473ffffccd 0xfbfffe11cfffff33

def z4 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0xd7f807ff0ffc03c0 0xf5fe01ffc3ff00f0

def z5 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x77fffffff0000000 0xddfffffffc000000

def z6 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0xbb07c7c0fe03e3ff 0xeec1f1f03f80f8ff

def z7 : W := mkw 0x0008581250000000 0x0002160494000000 0x7118f87ff0000000 0x9c463e1ffc000000

def z8 : W := mkw 0x77ffff7ff10c2d55 0x1dffffdffc430b55 0xfffffffff31c7fff 0xfffffffffcc71fff

def z9 : W := mkw 0x0042200000411000 0x0010880000104400 0xeee738000de39c00 0xfbb9ce000378e700

def z10 : W := mkw 0x402006ed052403c0 0x500801bb414900f0 0x100007ff000003c0 0x040001ffc00000f0

def z11 : W := mkw 0x4ff32ffdcff597f0 0x53fccbff73fd65fc 0xffff3fffcfff9ff2 0xffffcffff3ffe7fc

def z12 : W := mkw 0x43b006650a9400c0 0x50ec019942a50030 0x57f807ff021c00c0 0xd5fe01ffc0870030

def z13 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0x930707c00e0383c0 0xe4c1c1f00380e0f0

def z14 : W := mkw 0x0c632bb0c4619220 0x0318caec31186488 0x76e73fb8cce38000 0xddb9cfee3338e000

def z15 : W := mkw 0x54210f76f0000001 0x150843ddbc000000 0x100007fff0000000 0x040001fffc000000

def z16 : W := mkw 0x63fef6ed0fff7bc0 0xd8ffbdbb43ffdef0 0xffffffff0fffffc0 0xffffffffc3fffff0

def z17 : W := mkw 0x039004c00e900280 0x00e4013003a400a0 0xd7f807c00ffc03c0 0xf5fe01f003ff00f0

def z18 : W := mkw 0x930585c9afb6c3e8 0x64c161726bedb0fa 0xbb07c7c0ffffe3ff 0xeec1f1f03ffff8ff

def z19 : W := mkw 0xd4210ff6f40082a9 0x350843fdbd0020aa 0x100007fff00003ff 0x040001fffc0000ff

def z20 : W := mkw 0x000000890fb403c0 0x4000002243ed00f0 0x800000000ffc03c0 0x2000000003ff00f0

def z21 : W := mkw 0x0008581250082c14 0x0002160494020b05 0x2800f800f0007c3f 0x0a003e003c001f0f

def z22 : W := mkw 0x746fff76f0000001 0x1d1bffddbc000000 0x3007fffff0000000 0x0c01fffffc000000

def z23 : W := mkw 0x030480000a024000 0x00c1200002809000 0xab07c0000e03e000 0xeac1f0000380f800

def z24 : W := mkw 0x43b486ed0fb643c0 0x50ed21bb43ed90f0 0xffffc7ff0fffe3c0 0xfffff1ffc3fff8f0

def z25 : W := mkw 0x77f7a764a0000001 0x1dfde9d928000000 0x06e7078000000000 0x41b9c1e000000000

def z26 : W := mkw 0x43b0066400000000 0x10ec019900000000 0x57f807ff00000000 0xd5fe01ffc0000000

def z27 : W := mkw 0x64fa7a3650000001 0x193e9e8d94000000 0x44f8383f00000000 0x113e0e0fc0000000

def z28 : W := mkw 0x439004450a9400c0 0x50e4011142a50030 0x01180047021c00c0 0x00460011c0870030

def z29 : W := mkw 0x0800008805619730 0x02000022015865cc 0x880000000de39f32 0x220000000378e7cc

def z30 : W := mkw 0x7ffffffef5619731 0x1fffffffbd5865cc 0xfffffffffde39f32 0xffffffffff78e7cc

def z31 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0xa800f800f31c7fff 0x2a003e003cc71fff

def z32 : W := mkw 0x40b0022d01b40140 0x502c008b406d0050 0x44f8003f01fc0000 0x113e000fc07f0000

def z33 : W := mkw 0x0000000901040140 0x0000000240410050 0x80000000031c03c0 0x2000000000c700f0

def z34 : W := mkw 0x23def8125adb7c14 0x88f7be0496b6df05 0xeffff800fffffc3f 0xfbfffe003fffff0f

def z35 : W := mkw 0x43b85eff5fb403c0 0x50ee17bfd7ed00f0 0xf7f8fffffffc03c0 0xfdfe3fffffff00f0

def z36 : W := mkw 0x6cfa7a3e51611511 0x1b3e9e8f94584544 0x44f8383f01e01c00 0x113e0e0fc0780700

def z37 : W := mkw 0x4020066400000000 0x1008019900000000 0x100007ff00000000 0x040001ffc0000000

def z38 : W := mkw 0x77ffff76fadb7801 0x9dffffddbeb6de00 0xfffffffffffffc00 0xffffffffffffff00

def z39 : W := mkw 0x54295f7ff10c2d55 0x150a57dffc430b55 0xf918fffff31c7fff 0xbe463ffffcc71fff

def z40 : W := mkw 0x77ffff7ef1000511 0x1dffffdfbc400144 0xfffffffff1001f32 0xfffffffffc4007cc

def z41 : W := mkw 0x0c6323a084619220 0x0318c8e821186488 0x06e707800ce38000 0x41b9c1e00338e000

def z42 : W := mkw 0x0042281841411510 0x00108a0610504544 0xfee73838cde39f32 0xffb9ce0e3378e7cc

def z43 : W := mkw 0x0c622a3841611510 0x03188a8e10584544 0x44e0383801e01c00 0x11380e0e00780700

def z44 : W := mkw 0x930484402a024088 0x24c121100a809022 0x0100c040320060cd 0x004030100c801833

def z45 : W := mkw 0x64fb7b36d0000001 0x193edecdb4000000 0x76ff3fbfc0000000 0xddbfcfeff0000000

def z46 : W := mkw 0xb3dff5c0aedbfaa8 0xacf7fd702bb6feaa 0xffffffc0ffffffff 0xfffffff03fffffff

def z47 : W := mkw 0x08000089056dbf74 0x02000022415b6fdd 0x880000000fffffff 0x2200000003ffffff

def z48 : W := mkw 0x64fa7a3f510c2d55 0x193e9e8fd4430b55 0x44f8383f011c1c00 0x113e0e0fc0470700

def z49 : W := mkw 0x77f7a7edafb403c1 0x5dfde9fb6bed00f0 0xd7ff07ff0ffc03c0 0xf5ffc1ffc3ff00f0

def z50 : W := mkw 0x00085003100c2844 0x00021400c4030a11 0xe918f847331c7ccd 0xba463e11ccc71f33

def z51 : W := mkw 0x77ffff77fa9400c1 0x5dffffddfea50030 0x77fffffff21c00c0 0xddfffffffc870030

def z52 : W := mkw 0x739cd44630000001 0x1ce735118c000000 0x0118c04730000000 0x00463011cc000000

def z53 : W := mkw 0x0c210bb8c5208730 0x030842ee314821cc 0xd6e007b8cde00332 0xf5b801ee337800cc

def z54 : W := mkw 0x0c432990c4419630 0x0310ca643110658c 0xba073f80cc039f32 0xee81cfe03300e7cc

def z55 : W := mkw 0x0c6323a084619220 0x0318c8e821186488 0xeee73f800de39c00 0xfbb9cfe00378e700

def z56 : W := mkw 0x9f47add0ee43d6b8 0x27d1eb743b90f5ae 0xbb07ffc0fe03ffff 0xeec1fff03f80ffff

def z57 : W := mkw 0x346ffb32f0000001 0x0d1bfeccbc000000 0x76e7ffb8f0000000 0xddb9ffee3c000000

def z58 : W := mkw 0x5c210ffef5208731 0x170843ffbd4821cc 0x100007fff0000332 0x040001fffc0000cc

def z59 : W := mkw 0x9c67abb8e563d738 0x2719eaee3958f5ce 0xfee7ffb8fde3ff3f 0xffb9ffee3f78ffcf

def z60 : W := mkw 0x43b0066d01b40140 0x50ec019b406d0050 0x57f807ff01fc0000 0xd5fe01ffc07f0000

def z61 : W := mkw 0x000000000ad35000 0x8000000002b4d400 0x000000000ce38000 0x000000000338e000

def z62 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0x020707800c038000 0x4081c1e00300e000

def z63 : W := mkw 0x23def81b5bdf7d54 0x88f7be06d6f7df55 0xfffff87fffffffff 0xfffffe1fffffffff

def z64 : W := mkw 0x0001018084008220 0x0000406021002088 0xba070780cc038332 0xee81c1e03300e0cc

def z65 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0x4018383f011c1c00 0x10060e0fc0470700

def z66 : W := mkw 0x77fffffef5200301 0x1dffffffbd4800c0 0xf7fffffffde00300 0xfdffffffff7800c0

def z67 : W := mkw 0x40b002ad05b40340 0x502c00ab416d00d0 0xd6f807bf0dfc0300 0xf5be01efc37f00c0

def z68 : W := mkw 0x23def00000000000 0x08f7bc0000000000 0x67fff80000000000 0xd9fffe0000000000

def z69 : W := mkw 0x080000890ff597f0 0x4200002243fd65fc 0x880000000fff9ff2 0x2200000003ffe7fc

def z70 : W := mkw 0x7ff7a7e4a4619221 0x1ffde9f929186488 0x06e707800ce38000 0x41b9c1e00338e000

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0x5118007f00000000 0x9446001fc0000000

def z72 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa0700000c038000 0xea81c0000300e000

def z73 : W := mkw 0x239cd0000a9a6800 0x88e7340002a69a00 0x0118c000021c6000 0x0046300000871800

def z74 : W := mkw 0x73def4463adb7801 0x9cf7bd118eb6de00 0xeffff8473ffffc00 0xfbfffe11cfffff00

def z75 : W := mkw 0x00085003100c2844 0x00021400c4030a11 0xb918c047f21c63ff 0xae463011fc8718ff

def z76 : W := mkw 0x40b006ed05b403c0 0x502c01bb416d00f0 0x54f807ff01fc03c0 0x153e01ffc07f00f0

def z77 : W := mkw 0xf7ffffffffb6c3e9 0x7dffffffffedb0fa 0xffffffffffffe3ff 0xfffffffffffff8ff

def z78 : W := mkw 0x0c4b7912d049bc34 0x0312de44b4126f0d 0x2807f800f003fc3f 0x0a01fe003c00ff0f

def z79 : W := mkw 0x0008581250000000 0x0002160494000000 0x2000f800f0000000 0x08003e003c000000

def z80 : W := mkw 0x0c6b7bbad5619730 0x031adeeeb55865cc 0xfffffffffde39f32 0xffffffffff78e7cc

def z81 : W := mkw 0x039000000a900000 0x00e4000002a40000 0xc7f800000ffc0000 0xf1fe000003ff0000

def z82 : W := mkw 0x800000890fb6c3e8 0x6000002243edb0fa 0x880000000fffe3ff 0x2200000003fff8ff

def z83 : W := mkw 0xd3b587edafb6c3e8 0x74ed61fb6bedb0fa 0xffffc7ffffffe3ff 0xfffff1fffffff8ff

def z84 : W := mkw 0x0000000901040140 0x0000000240410050 0xd118007f031c03c0 0xb446001fc0c700f0

def z85 : W := mkw 0x900105c0a40082a8 0x24004170290020aa 0xba0707c0fc0383ff 0xee81c1f03f00e0ff

def z86 : W := mkw 0xf39dd5c6be02c2a9 0x3ce77571af80b0aa 0xbb1fc7c7fe03e3ff 0xeec7f1f1ff80f8ff

def z87 : W := mkw 0x9f67aff8ef63d7b8 0x27d9ebfe3bd8f5ee 0xffe7fff8ffe3ffff 0xfff9fffe3ff8ffff

def z88 : W := mkw 0x77ffff76f0d93801 0x9dffffddbc364e00 0x77fffffff1fc1c00 0xddfffffffc7f0700

def z89 : W := mkw 0x20da700000d93800 0x88369c0000364e00 0x44f8380001fc1c00 0x113e0e00007f0700

def z90 : W := mkw 0x030004c00e000280 0x00c00130038000a0 0x930007c00e0003c0 0xe4c001f0038000f0

def z91 : W := mkw 0x0000081841000510 0x0000020610400144 0xf8003838c1001f32 0xbe000e0e304007cc

def z92 : W := mkw 0x0398581b5b9c2d54 0x00e61606d6e70b55 0xfff8f87ffffc7fff 0xfffe3e1fffff1fff

def z93 : W := mkw 0xb34ff5c0ae4bfaa8 0xacd3fd702b92feaa 0xbb07ffc0fe03ffff 0xeec1fff03f80ffff

def z94 : W := mkw 0x54210ffff52403c1 0x550843fffd4900f0 0x100007fff00003c0 0x040001fffc0000f0

def z95 : W := mkw 0x439004440a900080 0x50e4011102a40020 0x0000000000000000 0x0000000000000000

def z96 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0xffe7fff8ffe3ffff 0xfff9fffe3ff8ffff

def z97 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0x46f807bf0dfc0000 0x51be01efc37f0000

def z98 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0x5018387ff11c1fff 0x14060e1ffc4707ff

def z99 : W := mkw 0x800000800e02c2a8 0x200000200380b0aa 0x880000000e03e3ff 0x220000000380f8ff

def z100 : W := mkw 0x0c210bb8c5208730 0x030842ee314821cc 0x100007b8c0000332 0x040001ee300000cc

def z101 : W := mkw 0x7ffffffefffbff31 0x9fffffffbffeffcc 0xffffffffffffff32 0xffffffffffffffcc

def z102 : W := mkw 0x57258f76f0000001 0x15c963ddbc000000 0x3307c7fff0000000 0xccc1f1fffc000000

def z103 : W := mkw 0x0000000901040140 0x0000000240410050 0xf918c07ff31c63ff 0xbe46301ffcc718ff

def z104 : W := mkw 0x7ffffffef5208731 0x1fffffffbd4821cc 0x77fffffff0000332 0xddfffffffc0000cc

def z105 : W := mkw 0xb39dd5c0ae9aeaa8 0xace775702ba6baaa 0xbb1fc7c0fe1fe3ff 0xeec7f1f03f87f8ff

def z106 : W := mkw 0x4390044400000000 0x10e4011100000000 0x0118004700000000 0x00460011c0000000

def z107 : W := mkw 0x032006e80f200380 0x00c801ba03c800e0 0xd7e007f80fe003c0 0xf5f801fe03f800f0

def z108 : W := mkw 0x0c632b38c1619530 0x0318cace3058654c 0x6ce73838c1e39c32 0x1b39ce0e3078e70c

def z109 : W := mkw 0xd39585c5ae96c2e8 0x74e561716ba5b0ba 0xbb1fc7c7fe1fe3ff 0xeec7f1f1ff87f8ff

def z110 : W := mkw 0x04632b30c0000000 0x0118cacc30000000 0x76e73fb8c0000000 0xddb9cfee30000000

def z111 : W := mkw 0x00085009010c2d54 0x0002140240430b55 0xe918f800031c7fff 0xba463e0000c71fff

def z112 : W := mkw 0x40b0022400000000 0x102c008900000000 0x44f8003f00000000 0x113e000fc0000000

def z113 : W := mkw 0xf7ffff76f002c029 0x3dffffddbc00b00a 0x7ffffffff003e03f 0xdffffffffc00f80f

def z114 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0x111807ff021c03c0 0x044601ffc08700f0

def z115 : W := mkw 0x43b85e7f510c2d54 0x10ee179fd4430b55 0xfff8fffff31c7fff 0xfffe3ffffcc71fff

def z116 : W := mkw 0x0000081941040550 0x0000020650410154 0xf918387fc31c1ff2 0xbe460e1ff0c707fc

def z117 : W := mkw 0x900105c0a40082a8 0x24004170290020aa 0x100007c0f00003ff 0x040001f03c0000ff

def z118 : W := mkw 0x90058100a002c028 0x240160402800b00a 0x2807c000f003e03f 0x0a01f0003c00f80f

def z119 : W := mkw 0x344ff912f0000001 0x0d13fe44bc000000 0x2007f800f0000000 0x0801fe003c000000

def z120 : W := mkw 0x0c6b7bbbd56dbf74 0x031adeeef55b6fdd 0xffffffffffffffff 0xffffffffffffffff

def z121 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x26e7ff80f0000000 0x49b9ffe03c000000

def z122 : W := mkw 0x930585c9af0eeffc 0x24c161726bc3bbff 0xbb07c7c0ff1fffff 0xeec1f1f03fc7ffff

def z123 : W := mkw 0x000000890fff7bc0 0xc000002243ffdef0 0x880000000fffffc0 0x2200000003fffff0

def z124 : W := mkw 0x67fefa3650000001 0x19ffbe8d94000000 0x67fff83f00000000 0xd9fffe0fc0000000

def z125 : W := mkw 0x3c4ff912f0419431 0x0f13fe44bc10650c 0x2807f800f0039c32 0x0a01fe003c00e70c

def z126 : W := mkw 0x37dff912f0000001 0x0df7fe44bc000000 0x67fff800f0000000 0xd9fffe003c000000

def z127 : W := mkw 0x739cd4463a9a6801 0x9ce735118ea69a00 0x0118c047321c6000 0x00463011cc871800

def z128 : W := mkw 0x0300044000000000 0x00c0011000000000 0x130007c000000000 0xc4c001f000000000

def z129 : W := mkw 0x0008500000082800 0x0002140000020a00 0xe918f800031c7c00 0xba463e0000c71f00

def z130 : W := mkw 0x77ffff76fad35001 0x9dffffddbeb4d400 0x77fffffffce38000 0xddffffffff38e000

def z131 : W := mkw 0x13058540a0000000 0x04c1615028000000 0x0207078000000000 0x4081c1e000000000

def z132 : W := mkw 0x0c210bb8c5208730 0x030842ee314821cc 0xba0707b8cc038332 0xee81c1ee3300e0cc

def z133 : W := mkw 0x000000000adb7800 0x8000000002b6de00 0x880000000ffffc00 0x2200000003ffff00

def z134 : W := mkw 0x13058540a0000000 0x04c1615028000000 0x3307c7c0f0000000 0xccc1f1f03c000000

def z135 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0xfffff840ffffffff 0xfffffe103fffffff

def z136 : W := mkw 0x0c432910c0419430 0x0310ca443010650c 0x28073800c0039c32 0x0a01ce003000e70c

def z137 : W := mkw 0xf7fffff6fe02c2a9 0x3dfffffdbf80b0aa 0xfffffffffe03e3ff 0xffffffffff80f8ff

def z138 : W := mkw 0x239cd0000a9a6800 0x88e7340002a69a00 0xe918f800031c7c00 0xba463e0000c71f00

def z139 : W := mkw 0x0c632bbbd5659774 0x0318caeef55965dd 0xfee73ffffde39fff 0xffb9cfffff78e7ff

def z140 : W := mkw 0x43b85eff5fbc2fd4 0x50ee17bfd7ef0bf5 0xfff8fffffffc7fff 0xfffe3fffffff1fff

def z141 : W := mkw 0x930ddddbff0eeffc 0x24c37776ffc3bbff 0xfb1fffffff1fffff 0xfec7ffffffc7ffff

def z142 : W := mkw 0x002002a805200300 0x000800aa014800c0 0xd6e007b80de00300 0xf5b801ee037800c0

def z143 : W := mkw 0x930484c02e02c2a8 0x24c121300b80b0aa 0x8900c0403e03e3ff 0x224030100f80f8ff

def z144 : W := mkw 0x77ffffffffb403c1 0x5dffffffffed00f0 0xf7fffffffffc03c0 0xfdffffffffff00f0

def z145 : W := mkw 0x23def000004b7800 0x88f7bc000012de00 0x6ffff8000003fc00 0xdbfffe000000ff00

def z146 : W := mkw 0x402006ed052403c0 0x500801bb414900f0 0xd11807ff031c03c0 0xb44601ffc0c700f0

def z147 : W := mkw 0x77ffff76f0082c15 0x1dffffddbc020b05 0x7ffffffff0007c3f 0xdffffffffc001f0f

def z148 : W := mkw 0x43b006e40eb00280 0x50ec01b903ac00a0 0x06e007800ce00000 0x41b801e003380000

def z149 : W := mkw 0xd3b486ed2fb643c8 0x74ed21bb4bed90f2 0xd7f8c7ff3ffc63cd 0xf5fe31ffcfff18f3

def z150 : W := mkw 0x0000000000000000 0x0000000000000000 0xb900c040f20063ff 0xae4030103c8018ff

def z151 : W := mkw 0x0004800000024000 0x0001200000009000 0x2807c0000003e000 0x0a01f0000000f800

def z152 : W := mkw 0x23d6a0000ad35000 0x88f5a80002b4d400 0xeee738000de39c00 0xfbb9ce000378e700

def z153 : W := mkw 0x204ef000004b7800 0x8813bc000012de00 0xe91ff800031ffc00 0xba47fe0000c7ff00

def z154 : W := mkw 0x0000000000000000 0x0000000000000000 0x3100c040f0000000 0x8c4030103c000000

def z155 : W := mkw 0x239cd0000a9a6800 0x88e7340002a69a00 0xc7f8c0000ffc6000 0xf1fe300003ff1800

def z156 : W := mkw 0x002002a905240340 0x000800aa414900d0 0xd7f807ff0ffc03c0 0xf5fe01ffc3ff00f0

def z157 : W := mkw 0x030cd0000a0a6800 0x00c3340002829a00 0xeb1ff8000f1ffc00 0xfac7fe0003c7ff00

def z158 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0x1100c7c0f20063ff 0x044031f03c8018ff

def z159 : W := mkw 0x239cd0000adb7800 0x88e7340002b6de00 0x8918c0000ffffc00 0x2246300003ffff00

def z160 : W := mkw 0x639cd4450a9e68c0 0xd8e7351142a79a30 0x0118c047021c60c0 0x00463011c0871830

def z161 : W := mkw 0x64fa7a3650d93801 0x993e9e8d94364e00 0x44f8383f01fc1c00 0x113e0e0fc07f0700

def z162 : W := mkw 0x046b7b32d0000000 0x011adeccb4000000 0x77fffffff0000000 0xddfffffffc000000

def z163 : W := mkw 0x43b006640a900000 0x10ec019902a40000 0xd7f807ff0ffc0000 0xf5fe01ffc3ff0000

def z164 : W := mkw 0x63fef6640adb7800 0x98ffbd9902b6de00 0xffffffff0ffffc00 0xffffffffc3ffff00

def z165 : W := mkw 0x00000009010c2d54 0x0000000240430b55 0x88000000031c7fff 0x2200000000c71fff

def z166 : W := mkw 0x0008500b110c2944 0x00021402c4430a51 0xd118c07f331c63cd 0xb446301fccc718f3

def z167 : W := mkw 0xb3def4402adb7888 0xacf7bd100ab6de22 0xeffff8403ffffccd 0xfbfffe100fffff33

def z168 : W := mkw 0x0001018084008220 0x0000406021002088 0x10000780c0000332 0x040001e0300000cc

def z169 : W := mkw 0x1767af70e0000000 0x05d9ebdc38000000 0x77e7fff8f0000000 0xddf9fffe3c000000

def z170 : W := mkw 0x63fef6ed0fb403c0 0x58ffbdbb43ed00f0 0xf7ffffff0ffc03c0 0xfdffffffc3ff00f0

def z171 : W := mkw 0x20da781b51dd3d54 0x88369e06d4774f55 0xfdf8f87ff3fc7fff 0xbf7e3e1ffcff1fff

def z172 : W := mkw 0x2fdff910cadbfc30 0x8bf7fe4432b6ff0c 0xeffff800cffffc32 0xfbfffe0033ffff0c

def z173 : W := mkw 0xf7ffff76fa024089 0x3dffffddbe809022 0x77fffffff20060cd 0xddfffffffc801833

def z174 : W := mkw 0x43b0066400000000 0x10ec019900000000 0x06e0078000000000 0x41b801e000000000

def z175 : W := mkw 0x039000000a900000 0x00e4000002a40000 0x06e000000ce00000 0x41b8000003380000

def z176 : W := mkw 0x04632b30c0411000 0x0118cacc30104400 0xfee73fb8cde39c00 0xffb9cfee3378e700

def z177 : W := mkw 0x77ffff7ff1040141 0x1dffffdffc410050 0xf7fffffff31c03c0 0xfdfffffffcc700f0

def z178 : W := mkw 0x239cd00000000000 0x08e7340000000000 0x0118c00000000000 0x0046300000000000

def z179 : W := mkw 0x046b7b3bd10c2d54 0x011adecef4430b55 0xfffffffff31c7fff 0xfffffffffcc71fff

def z180 : W := mkw 0x739dd546b0000001 0x1ce77551ac000000 0x331fc7c7f0000000 0xccc7f1f1fc000000

def z181 : W := mkw 0x77ffff76fa900001 0x1dffffddbea40000 0xf7fffffffffc0000 0xfdffffffffff0000

def z182 : W := mkw 0x40200eff552407d4 0x500803bfd54901f5 0x100007fff00003ff 0x040001fffc0000ff

def z183 : W := mkw 0x54632f76f0000001 0x1518cbddbc000000 0x76e73ffff0000000 0xddb9cffffc000000

def z184 : W := mkw 0x0800000801611510 0x0200000200584544 0x0000000001e01c00 0x0000000000780700

def z185 : W := mkw 0x77ffff76f04b7801 0x9dffffddbc12de00 0x7ffffffff003fc00 0xdffffffffc00ff00

def z186 : W := mkw 0x13058540aa024000 0x04c161502a809000 0xbb07c7c0fe03e000 0xeec1f1f03f80f800

def z187 : W := mkw 0x57b10fffffb403c1 0x55ec43ffffed00f0 0xd7f807fffffc03c0 0xf5fe01ffffff00f0

def z188 : W := mkw 0x93058540a002c028 0x24c161502800b00a 0x3b07c7c0f003e03f 0xcec1f1f03c00f80f

def z189 : W := mkw 0x23def8184bdb7d10 0x88f7be0612f6df44 0xfffff838cfffff32 0xfffffe0e33ffffcc

def z190 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0x2ee7f8000ce3fc00 0x4bb9fe000338ff00

def z191 : W := mkw 0x77fefe7670000001 0x1dffbf9d9c000000 0x45f8f87f30000000 0x117e3e1fcc000000

def z192 : W := mkw 0x0000000000082c14 0x0000000000020b05 0x0800000000007c3f 0x0200000000001f0f

def z193 : W := mkw 0x0c632bb8cffbff30 0x8318caee33feffcc 0xfee73fb8cfffff32 0xffb9cfee33ffffcc

def z194 : W := mkw 0x830004c00e02c2a8 0x20c001300380b0aa 0x9b0007c00e03e3ff 0xe6c001f00380f8ff

def z195 : W := mkw 0x47f32f74c0000000 0x11fccbdd30000000 0x77ff3fffc0000000 0xddffcffff0000000

def z196 : W := mkw 0x0c632bb0c4619630 0x0318caec3118658c 0x2ee73f80cce39c32 0x4bb9cfe03338e70c

def z197 : W := mkw 0x43b85e7650000000 0x10ee179d94000000 0x77f8fffff0000000 0xddfe3ffffc000000

def z198 : W := mkw 0x2c4ff910c04bfc30 0x8b13fe443012ff0c 0x2807f800c003fc32 0x0a01fe003000ff0c

def z199 : W := mkw 0x4c632ffdc56597f0 0x5318cbff715965fc 0xfee73fffcde39ff2 0xffb9cffff378e7fc

def z200 : W := mkw 0x204ef0000adb7800 0x8813bc0002b6de00 0xa807f8000ffffc00 0x2a01fe0003ffff00

def z201 : W := mkw 0x00000089052403c0 0x40000022414900f0 0x00000000000003c0 0x00000000000000f0

def z202 : W := mkw 0x00085003100c2844 0x00021400c4030a11 0x0118c047321c60cd 0x00463011cc871833

def z203 : W := mkw 0x64f2222400000001 0x193c888900000000 0x04e0000000000000 0x0138000000000000

def z204 : W := mkw 0x7fffff7ef1611511 0x1fffffdfbc584544 0x77fffffff1e01c00 0xddfffffffc780700

def z205 : W := mkw 0x43b006ed0fff7bc0 0xd0ec01bb43ffdef0 0xdff807ff0fffffc0 0xf7fe01ffc3fffff0

def z206 : W := mkw 0x0c622a3841611510 0x03188a8e10584544 0xeee738380de39c00 0xfbb9ce0e0378e700

def z207 : W := mkw 0x0000081b51040554 0x00000206d4410155 0x1000007ff00003ff 0x0400001ffc0000ff

def z208 : W := mkw 0x77ffff7ff1040555 0x1dffffdffc410155 0x77fffffff00003ff 0xddfffffffc0000ff

def z209 : W := mkw 0x739cd447300c2845 0x1ce73511cc030a11 0x0118c047321c60cd 0x00463011cc871833

def z210 : W := mkw 0x2ffffbb8cffbff30 0x8bfffeee33feffcc 0xffffffb8cfffff32 0xffffffee33ffffcc

def z211 : W := mkw 0x0c6323a885619320 0x0318c8ea215864c8 0xd6e707b80de38300 0xf5b9c1ee0378e0c0

def z212 : W := mkw 0x00000009010c2d54 0x0000000240430b55 0x00000000011c1c00 0x0000000000470700

def z213 : W := mkw 0x63bcd6ed0fbe6bc0 0xd8ef35bb43ef9af0 0xd7f8c7ff0ffc63c0 0xf5fe31ffc3ff18f0

def z214 : W := mkw 0x77ffffffffff7bc1 0xddffffffffffdef0 0xffffffffffffffc0 0xfffffffffffffff0

def z215 : W := mkw 0x9f6ffffbff6ffffc 0x27dbfffeffdbffff 0xffffffffffffffff 0xffffffffffffffff

def z216 : W := mkw 0x33dff540a0000000 0x0cf7fd5028000000 0x77ffffc0f0000000 0xddfffff03c000000

def z217 : W := mkw 0xb44ff912f002c029 0x2d13fe44bc00b00a 0x2807f800f003e03f 0x0a01fe003c00f80f

def z218 : W := mkw 0x77f7a764aad35001 0x9dfde9d92ab4d400 0x06e707800ce38000 0x41b9c1e00338e000

def z219 : W := mkw 0x04210b30c0000000 0x010842cc30000000 0x100007b8c0000000 0x040001ee30000000

def z220 : W := mkw 0x0000000000000000 0x0000000000000000 0xc6e000000de00000 0xf1b8000003780000

def z221 : W := mkw 0x800000000002c028 0x200000000000b00a 0x080000000003e03f 0x020000000000f80f

def z222 : W := mkw 0x64fa7a3f510c2d55 0x193e9e8fd4430b55 0xfdf8f87ff31c7fff 0xbf7e3e1ffcc71fff

def z223 : W := mkw 0x0c632bb9c5659770 0x0318caee715965dc 0xffff3fffcfff9ff2 0xffffcffff3ffe7fc

def z224 : W := mkw 0x54210f7ff1040555 0x150843dffc410155 0x100007fff00003ff 0x040001fffc0000ff

def z225 : W := mkw 0xf7fffff6fe02c2a9 0x3dfffffdbf80b0aa 0x77fffffffc038000 0xddffffffff00e000

def z226 : W := mkw 0x74fb7f76f0000001 0x1d3edfddbc000000 0x54f83ffff0000000 0x153e0ffffc000000

def z227 : W := mkw 0x930105c0ae0082a8 0x24c041702b8020aa 0x930007c0fe0003ff 0xe4c001f03f8000ff

def z228 : W := mkw 0x00000001000c2844 0x0000000040030a11 0x00000000021c60cd 0x0000000000871833

def z229 : W := mkw 0x0000000901040140 0x0000000240410050 0x4018003f011c0000 0x1006000fc0470000

def z230 : W := mkw 0x77f7a764a0000001 0x1dfde9d928000000 0x37e7c7c0f0000000 0xcdf9f1f03c000000

def z231 : W := mkw 0x23d6a0000ad35000 0x88f5a80002b4d400 0x06e700000ce38000 0x41b9c0000338e000

def z232 : W := mkw 0x0c6a7a3b516d3d54 0x031a9e8ed45b4f55 0xfdf8f87ff3fc7fff 0xbf7e3e1ffcff1fff

def z233 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0x54e03fb8c1e01f32 0x15380fee307807cc

def z234 : W := mkw 0x7ffffffff56dbf75 0x1ffffffffd5b6fdd 0xffffffffffffffff 0xffffffffffffffff

def z235 : W := mkw 0x204ef000004b7800 0x8813bc000012de00 0x2807f8000003fc00 0x0a01fe000000ff00

def z236 : W := mkw 0x0800008805208730 0x02000022014821cc 0x0000000000000332 0x00000000000000cc

def z237 : W := mkw 0x039000890fb403c0 0x40e4002243ed00f0 0xc7f800000ffc03c0 0xf1fe000003ff00f0

def z238 : W := mkw 0x0842208805619730 0x02108822015865cc 0xeee738000de39f32 0xfbb9ce000378e7cc

def z239 : W := mkw 0x77f7a7e4aeb00281 0x5dfde9f92bac00a0 0x06e707800ce00000 0x41b9c1e003380000

def z240 : W := mkw 0x0000000801000510 0x0000000200400144 0x8800000001001f32 0x22000000004007cc

def z241 : W := mkw 0x2ff7abb8cff3d730 0x8bfdeaee33fcf5cc 0xfee73fb8cde39f32 0xffb9cfee3378e7cc

def z242 : W := mkw 0x23d6a0000adb7800 0x88f5a80002b6de00 0x8ee700000ffffc00 0x63b9c00003ffff00

def z243 : W := mkw 0x4c210ffdc52487f0 0x530843ff714921fc 0x100007ffc00003f2 0x040001fff00000fc

def z244 : W := mkw 0x63fef66400000000 0x18ffbd9900000000 0x77ffffff00000000 0xddffffffc0000000

def z245 : W := mkw 0xd3bddfffffbeeffc 0x74ef77ffffefbbff 0xffffffffffffffff 0xffffffffffffffff

def z246 : W := mkw 0x006222a805611300 0x001888aa015844c0 0xfee73fb80de39f00 0xffb9cfee0378e7c0

def z247 : W := mkw 0x4ff32ffcc5619730 0x13fccbff315865cc 0xffff3fffcde39f32 0xffffcffff378e7cc

def z248 : W := mkw 0x77ffff76f0082801 0x1dffffddbc020a00 0xfffffffff31c7c00 0xfffffffffcc71f00

def z249 : W := mkw 0x43b0066d01040140 0x10ec019b40410050 0xd7f807ff031c03c0 0xf5fe01ffc0c700f0

def z250 : W := mkw 0x0800089845619730 0x02000226115865cc 0xf8003838cde39f32 0xbe000e0e3378e7cc

def z251 : W := mkw 0x439004c50e9402c0 0x50e4013143a500b0 0x931807c70e1c03c0 0xe4c601f1c38700f0

def z252 : W := mkw 0x004a700000493800 0x00129c0000124e00 0xeffff8000ffffc00 0xfbfffe0003ffff00

def z253 : W := mkw 0x030004c90f0403c0 0x00c0013243c100f0 0xd31807ff0f1c03c0 0xf4c601ffc3c700f0

def z254 : W := mkw 0x6ffffffdcffffff0 0xdbffffff73fffffc 0xffffffffcffffff2 0xfffffffff3fffffc

def z255 : W := mkw 0x73bcd6ef3fb403c1 0x5cef35bbcfed00f0 0xd7f8c7ff3ffc03c0 0xf5fe31ffcfff00f0

def z256 : W := mkw 0x90010100a0008028 0x240040402800200a 0x00000000f000003f 0x000000003c00000f

def z257 : W := mkw 0x0000081b51040554 0x00000206d4410155 0xd118007ff31c03ff 0xb446001ffcc700ff

def z258 : W := mkw 0x0c210bbbd5248774 0x030842eef54921dd 0x100007fff00003ff 0x040001fffc0000ff

def z259 : W := mkw 0x0463232080000000 0x0118c8c820000000 0x06e7078000000000 0x41b9c1e000000000

def z260 : W := mkw 0x00085813500c2c54 0x00021604d4030b15 0x2918f847f21c7cff 0x0a463e11fc871f3f

def z261 : W := mkw 0x0000081b510c2d54 0x00000206d4430b55 0x9800007ff31c7fff 0x2600001ffcc71fff

def z262 : W := mkw 0x77f7af74e0000001 0x1dfdebdd38000000 0x76e73fb8c0000000 0xddb9cfee30000000

def z263 : W := mkw 0x0000000000000000 0x0000000000000000 0x88000000020063ff 0x22000000008018ff

def z264 : W := mkw 0x800000890f0eeffc 0x2000002243c3bbff 0x880000000f1fffff 0x2200000003c7ffff

def z265 : W := mkw 0x0043218084419220 0x0010c86021106488 0xfee73f80cde39f32 0xffb9cfe03378e7cc

def z266 : W := mkw 0x0800008004619220 0x0200002001186488 0x000000000ce38000 0x000000000338e000

def z267 : W := mkw 0x0000000901040140 0x0000000240410050 0x1000007f000003c0 0x0400001fc00000f0

def z268 : W := mkw 0x23d6a00000000000 0x08f5a80000000000 0x06e7000000000000 0x41b9c00000000000

def z269 : W := mkw 0x344ff912f0000001 0x0d13fe44bc000000 0x711ff87ff0000000 0x9c47fe1ffc000000

def z270 : W := mkw 0x23def8125adb7800 0x88f7be0496b6de00 0xfffff87ffffffc00 0xfffffe1fffffff00

def z271 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z272 : W := mkw 0x77ffff76fa024001 0x1dffffddbe809000 0xfffffffffe03e000 0xffffffffff80f800

def z273 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0xe918f83f031c7c00 0xba463e0fc0c71f00

def z274 : W := mkw 0x9000044020000088 0x2400011008000022 0x00000040300000cd 0x000000100c000033

def z275 : W := mkw 0x0000081250000000 0x0000020494000000 0x1000007ff0000000 0x0400001ffc000000

def z276 : W := mkw 0x53b58764a0000000 0x14ed61d928000000 0x77ffc7fff0000000 0xddfff1fffc000000

def z277 : W := mkw 0x40285eff552c2fd4 0x500a17bfd54b0bf5 0xf918fffff31c7fff 0xbe463ffffcc71fff

def z278 : W := mkw 0x67fa7e7650000001 0x19fe9f9d94000000 0x57f83fff00000000 0xd5fe0fffc0000000

def z279 : W := mkw 0x77bddf76f0000001 0x1def77ddbc000000 0x1118c7fff0000000 0x044631fffc000000

def z280 : W := mkw 0x77ffff76fa9a6801 0x9dffffddbea69a00 0x77fffffff21c6000 0xddfffffffc871800

def z281 : W := mkw 0x039850000a982800 0x00e6140002a60a00 0xeff8f8000ffc7c00 0xfbfe3e0003ff1f00

def z282 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0x3307c7c0fc038000 0xccc1f1f03f00e000

def z283 : W := mkw 0x03d220000ad11000 0x00f4880002b44400 0xefff38000fff9c00 0xfbffce0003ffe700

def z284 : W := mkw 0x00000000004b7800 0x800000000012de00 0x080000000003fc00 0x020000000000ff00

def z285 : W := mkw 0xd7258ff6fe02c2a9 0x35c963fdbf80b0aa 0xbb07c7fffe03e3ff 0xeec1f1ffff80f8ff

def z286 : W := mkw 0x0000081b51040554 0x00000206d4410155 0x0000003f00000000 0x0000000fc0000000

def z287 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0x38073fb8c0039f32 0x0e01cfee3000e7cc

def z288 : W := mkw 0x0000000000d93800 0x8000000000364e00 0x0000000001fc1c00 0x00000000007f0700

def z289 : W := mkw 0x64fa7a3650000001 0x193e9e8d94000000 0x75f8f87ff0000000 0x9d7e3e1ffc000000

def z290 : W := mkw 0x344ff912f04b7801 0x8d13fe44bc12de00 0x2807f800f003fc00 0x0a01fe003c00ff00

def z291 : W := mkw 0x90058100a002c028 0x240160402800b00a 0x0007000000038000 0x0001c0000000e000

def z292 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0x46e73fb80de39c00 0x51b9cfee0378e700

def z293 : W := mkw 0x5000044630000001 0x140001118c000000 0x0000004730000000 0x00000011cc000000

def z294 : W := mkw 0x93058100aa02c028 0x24c160402a80b00a 0xab07c000fe03e03f 0xeac1f0003f80f80f

def z295 : W := mkw 0x000000890fbc2fd4 0x4000002243ef0bf5 0x880000000ffc7fff 0x2200000003ff1fff

def z296 : W := mkw 0x0008581250082800 0x0002160494020a00 0xf918f87ff31c7c00 0xbe463e1ffcc71f00

def z297 : W := mkw 0x4ff32ffccff197b0 0x53fccbff33fc65ec 0xfee73fb8cde39f32 0xffb9cfee3378e7cc

def z298 : W := mkw 0x54210764a0000001 0x150841d928000000 0x0000078000000000 0x000001e000000000

def z299 : W := mkw 0x00000009010c2d54 0x0000000240430b55 0xb900c040f31c7fff 0xae4030103cc71fff

def z300 : W := mkw 0x0000000310040044 0x00000000c4010011 0x00000047300000cd 0x00000011cc000033

def z301 : W := mkw 0x20da700000d93800 0x88369c0000364e00 0xeeff38000dff9c00 0xfbbfce00037fe700

def z302 : W := mkw 0x800000800e02c2a8 0x200000200380b0aa 0x000000000c038000 0x000000000300e000

def z303 : W := mkw 0x930484402a024088 0x24c121100a809022 0xab07c0403e03e0cd 0xeac1f0100f80f833

def z304 : W := mkw 0x53b587edafb403c0 0x54ed61fb6bed00f0 0xf7ffc7fffffc03c0 0xfdfff1ffffff00f0

def z305 : W := mkw 0x43b006e40eb00280 0x50ec01b903ac00a0 0x57f807ff0ce00000 0xd5fe01ffc3380000

def z306 : W := mkw 0x2ff7a3a08ef3d220 0x8bfde8e823bcf488 0x06e707800ce38000 0x41b9c1e00338e000

def z307 : W := mkw 0x27fffb30c0000000 0x09fffecc30000000 0x77ffffb8c0000000 0xddffffee30000000

def z308 : W := mkw 0x0c4b791bd14dbd74 0x0312de46f4536f5d 0xf91ff87ff31fffff 0xbe47fe1ffcc7ffff

def z309 : W := mkw 0x43b107ed8fb483e0 0x50ec41fb63ed20f8 0xffff07ffcfff83f2 0xffffc1fff3ffe0fc

def z310 : W := mkw 0x800000800edbfaa8 0xa000002003b6feaa 0x880000000fffffff 0x2200000003ffffff

def z311 : W := mkw 0x3c6ffbbaf5619731 0x0f1bfeeebd5865cc 0xfee7ffb8fde39f32 0xffb9ffee3f78e7cc

def z312 : W := mkw 0x374ffd52f0000001 0x0dd3ff54bc000000 0x3307ffc0f0000000 0xccc1fff03c000000

def z313 : W := mkw 0x04632bb0c4008220 0x0118caec31002088 0xfee73fb8cc038332 0xffb9cfee3300e0cc

def z314 : W := mkw 0x43b006e40eb00280 0x50ec01b903ac00a0 0x97e007c00ee003c0 0xe5f801f003b800f0

def z315 : W := mkw 0x0000008004008220 0x0000002001002088 0x880000000c038332 0x220000000300e0cc

def z316 : W := mkw 0x90058180ae02c2a8 0x240160602b80b0aa 0xa807c000fe03e3ff 0x2a01f0003f80f8ff

def z317 : W := mkw 0x0c622ab845611710 0x03188aae115845c4 0xd6e03fb80de01f00 0xf5b80fee037807c0

def z318 : W := mkw 0x4fb10ffdcfb487f0 0x53ec43ff73ed21fc 0xd7f807ffcffc03f2 0xf5fe01fff3ff00fc

def z319 : W := mkw 0x030480000a024000 0x00c1200002809000 0x0100c00002006000 0x0040300000801800

def z320 : W := mkw 0x930cdc5b7b0e6ddc 0x24c33716dec39b77 0xf918f87ff31c7fff 0xbe463e1ffcc71fff

def z321 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0xba070780cc038332 0xee81c1e03300e0cc

def z322 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0x16e707b8cce38332 0x45b9c1ee3338e0cc

def z323 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0x16e007ff0ce003c0 0x45b801ffc33800f0

def z324 : W := mkw 0xb3dff5c0aedbfaa8 0xacf7fd702bb6feaa 0xefffff800ffffc00 0xfbffffe003ffff00

def z325 : W := mkw 0xf7f7a7e4ae02c2a9 0x3dfde9f92b80b0aa 0xbfe7c7c0fe03e3ff 0xeff9f1f03f80f8ff

def z326 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0x1118c07ff21c63ff 0x0446301ffc8718ff

def z327 : W := mkw 0xb39cd4402a9a6888 0xace735100aa69a22 0x0118c040321c60cd 0x004630100c871833

def z328 : W := mkw 0x03085cdb5f0c2fd4 0x00c21736d7c30bf5 0xfb18ffffff1c7fff 0xfec63fffffc71fff

def z329 : W := mkw 0x43b006ed0fbc2fd4 0x50ec01bb43ef0bf5 0xdff807ff0ffc7fff 0xf7fe01ffc3ff1fff

def z330 : W := mkw 0x344ff91bf10c2d55 0x0d13fe46fc430b55 0xf91ff87ff31c7fff 0xbe47fe1ffcc71fff

def z331 : W := mkw 0x23da70000ad93800 0x88f69c0002b64e00 0xc7f838000ffc1c00 0xf1fe0e0003ff0700

def z332 : W := mkw 0x0000000000000000 0x0000000000000000 0xe800380001001c00 0xba000e0000400700

def z333 : W := mkw 0x90058100a002c028 0x240160402800b00a 0xb907c040f203e3ff 0xae41f0103c80f8ff

def z334 : W := mkw 0x0020022000000000 0x0008008800000000 0x56e007b800000000 0xd5b801ee00000000

def z335 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x46ff3fbf00000000 0x51bfcfefc0000000

def z336 : W := mkw 0x63fef22d0bff7940 0xd8ffbc8b42ffde50 0xeffff83f0ffffc00 0xfbfffe0fc3ffff00

def z337 : W := mkw 0x0801018885619730 0x02004062215865cc 0xba070780cde39f32 0xee81c1e03378e7cc

def z338 : W := mkw 0x402006ed052403c0 0x500801bb414900f0 0xd6e007ff0de003c0 0xf5b801ffc37800f0

def z339 : W := mkw 0x04622a3040000000 0x01188a8c10000000 0x44e0383800000000 0x11380e0e00000000

def z340 : W := mkw 0x0c295bbbd52caf74 0x030a56eef54b2bdd 0xf918fffff31c7fff 0xbe463ffffcc71fff

def z341 : W := mkw 0x939585c0ae92c2a8 0x24e561702ba4b0aa 0xffffc7c0ffffe3ff 0xfffff1f03ffff8ff

def z342 : W := mkw 0x0c432998c5619730 0x0310ca66315865cc 0xa8073800cde39f32 0x2a01ce003378e7cc

def z343 : W := mkw 0x23def0000a900000 0x08f7bc0002a40000 0xe7fff8000ffc0000 0xf9fffe0003ff0000

def z344 : W := mkw 0x0000000000000000 0x0000000000000000 0xb8000000c0000332 0xae000000300000cc

def z345 : W := mkw 0x20da700000000000 0x08369c0000000000 0x44f8380000000000 0x113e0e0000000000

def z346 : W := mkw 0x000000800eb00280 0x4000002003ac00a0 0x000000000ce00000 0x0000000003380000

def z347 : W := mkw 0x4cf22a3d41f51550 0x533c8a8f507d4554 0x44f8383f01fc1c00 0x113e0e0fc07f0700

def z348 : W := mkw 0x54295f76f0000001 0x150a57ddbc000000 0x7118fffff0000000 0x9c463ffffc000000

def z349 : W := mkw 0x0c6b7bbbd56dbf74 0x031adeeef55b6fdd 0xfeff3fbfcdff9f32 0xffbfcfeff37fe7cc

def z350 : W := mkw 0x130585c0a4008220 0x04c1617029002088 0xbb07c7c0fc038332 0xeec1f1f03f00e0cc

def z351 : W := mkw 0x432006ed0f2403c0 0x50c801bb43c900f0 0x930007ff0e0003c0 0xe4c001ffc38000f0

def z352 : W := mkw 0xd3b107edafb483e8 0x74ec41fb6bed20fa 0xd7f807fffffc03ff 0xf5fe01ffffff00ff

def z353 : W := mkw 0x204ef000004b7800 0x8813bc000012de00 0xeee7f8000de3fc00 0xfbb9fe000378ff00

def z354 : W := mkw 0x0000081b51040554 0x00000206d4410155 0xb900c07ff20063ff 0xae40301ffc8018ff

def z355 : W := mkw 0x40b85a3f51bc2d54 0x502e168fd46f0b55 0xfdf8f87ff3fc7fff 0xbf7e3e1ffcff1fff

def z356 : W := mkw 0xdff7affdeff7d7f8 0x77fdebff7bfdf5fe 0xffffffffffffffff 0xffffffffffffffff

def z357 : W := mkw 0x239480000a924000 0x88e5200002a49000 0x0000000000000000 0x0000000000000000

def z358 : W := mkw 0x4bb006ed0ff597f0 0x52ec01bb43fd65fc 0xdff807ff0fff9ff2 0xf7fe01ffc3ffe7fc

def z359 : W := mkw 0x0c632bb8c5208730 0x0318caee314821cc 0x76e73fb8c0000332 0xddb9cfee300000cc

def z360 : W := mkw 0x77ffff77f00c2845 0x1dffffddfc030a11 0x77fffffff21c60cd 0xddfffffffc871833

def z361 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0xd118387f031c1fc0 0xb4460e1fc0c707f0

def z362 : W := mkw 0xc3b006ed0fb6c3e8 0x70ec01bb43edb0fa 0xdff807ff0fffe3ff 0xf7fe01ffc3fff8ff

def z363 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0x120707c0fc0383ff 0x4481c1f03f00e0ff

def z364 : W := mkw 0x60fa722d01fd3940 0xd83e9c8b407f4e50 0x44f8383f01fc1c00 0x113e0e0fc07f0700

def z365 : W := mkw 0xb74ffdd2fe02c2a9 0x2dd3ff74bf80b0aa 0xbb07ffc0fe03e3ff 0xeec1fff03f80f8ff

def z366 : W := mkw 0x77fff766b0000001 0x1dfffdd9ac000000 0x07ffc7c730000000 0x41fff1f1cc000000

def z367 : W := mkw 0x2046a00000435000 0x8811a8000010d400 0x0007000000038000 0x0001c0000000e000

def z368 : W := mkw 0x0c632bb9cff597f0 0x4318caee73fd65fc 0xfee73fb8cfff9ff2 0xffb9cfee33ffe7fc

def z369 : W := mkw 0x030004c00e000280 0x00c00130038000a0 0xbb00c7c0fe0063ff 0xeec031f03f8018ff

def z370 : W := mkw 0x0390000000000000 0x00e4000000000000 0x47f8000000000000 0xd1fe000000000000

def z371 : W := mkw 0x900105c0a40082a8 0x24004170290020aa 0x0000078000000000 0x000001e000000000

def z372 : W := mkw 0xb3d7a5c0aed3d2a8 0xacf5e9702bb4f4aa 0xbfe7c7c0fee3e3ff 0xeff9f1f03fb8f8ff

def z373 : W := mkw 0x7ff7affce5619731 0x1ffdebff395865cc 0xfee73fb8cde39f32 0xffb9cfee3378e7cc

def z374 : W := mkw 0x800101808e02c2a8 0x200040602380b0aa 0xba070780ce03e3ff 0xee81c1e03380f8ff

def z375 : W := mkw 0xb3d7a5c0aed3d2a8 0xacf5e9702bb4f4aa 0x06e707800ce38000 0x41b9c1e00338e000

def z376 : W := mkw 0x0c6a7a3b516d3d54 0x031a9e8ed45b4f55 0x44f8383f01fc1c00 0x113e0e0fc07f0700

def z377 : W := mkw 0x0008581a51082d14 0x0002160694420b45 0xf800f838f1007f3f 0xbe003e0e3c401fcf

def z378 : W := mkw 0x0008500000082800 0x0002140000020a00 0xf918f840f31c7fff 0xbe463e103cc71fff

def z379 : W := mkw 0x2ffff3a08efbfa20 0x8bfffce823befe88 0xefffff800ffffc00 0xfbffffe003ffff00

def z380 : W := mkw 0x130585c0ae000280 0x04c161702b8000a0 0xb307c7c0fe0003c0 0xecc1f1f03f8000f0

def z381 : W := mkw 0x130ddd52f0000000 0x04c37754bc000000 0x731ffffff0000000 0xdcc7fffffc000000

def z382 : W := mkw 0x0001010080008020 0x0000404020002008 0x28070000c0038032 0x0a01c0003000e00c

def z383 : W := mkw 0x77ffff7ffbdf7d55 0x9dffffdffef7df55 0xffffffffffffffff 0xffffffffffffffff

def z384 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0xfffffffff20063ff 0xfffffffffc8018ff

def z385 : W := mkw 0x1304844020000000 0x04c1211008000000 0x0100c04030000000 0x004030100c000000

def z386 : W := mkw 0x0f67abb8cf63d730 0x03d9eaee33d8f5cc 0xffe7ffb8cfe3ff32 0xfff9ffee33f8ffcc

def z387 : W := mkw 0x880000880f63d7b8 0x2200002203d8f5ee 0x880000000fe3ffff 0x2200000003f8ffff

def z388 : W := mkw 0x900105c0ae02c2a8 0x240041702b80b0aa 0x980007c0fe03e3ff 0x260001f03f80f8ff

def z389 : W := mkw 0x44200a3650000001 0x1108028d94000000 0x0000003f00000000 0x0000000fc0000000

def z390 : W := mkw 0x4390044d0b9401c0 0x50e4011342e50070 0xd118007f031c03c0 0xb446001fc0c700f0

def z391 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000040f00003ff 0x040000103c0000ff

def z392 : W := mkw 0x930cd4433a0e68cc 0x24c33510ce839a33 0x0118c047321c60cd 0x00463011cc871833

def z393 : W := mkw 0x57b10f76f0000001 0x15ec43ddbc000000 0x57f807fff0000000 0xd5fe01fffc000000

def z394 : W := mkw 0x039000000adb7800 0x80e4000002b6de00 0xcff800000ffffc00 0xf3fe000003ffff00

def z395 : W := mkw 0x43b006e50eb402c0 0x50ec01b943ad00b0 0x07f807c70efc00c0 0x41fe01f1c3bf0030

def z396 : W := mkw 0x63f6a6ed0ff753c0 0xd8fda9bb43fdd4f0 0xd7ff07ff0fff83c0 0xf5ffc1ffc3ffe0f0

def z397 : W := mkw 0x23fef2a80ffb7b00 0x88ffbcaa03fedec0 0xffffffb80fffff00 0xffffffee03ffffc0

def z398 : W := mkw 0x80000080040082a8 0x20000020010020aa 0x00000000000003ff 0x00000000000000ff

def z399 : W := mkw 0x930585c0a40082a8 0x24c16170290020aa 0x3307c7c0f00003ff 0xccc1f1f03c0000ff

def z400 : W := mkw 0x43b00efd4fb407d0 0x50ec03bf53ed01f4 0xfff83fffcffc1ff2 0xfffe0ffff3ff07fc

def z401 : W := mkw 0x0000000801000100 0x0000000200400040 0xd000003801000300 0xb400000e004000c0

def z402 : W := mkw 0x0008500000000000 0x0002140000000000 0x6118f80000000000 0x98463e0000000000

def z403 : W := mkw 0x0008581b5bdf7d54 0x80021606d6f7df55 0xf918f87fffffffff 0xbe463e1fffffffff

def z404 : W := mkw 0x900dd91bf10eed7c 0x24037646fc43bb5f 0xf91ff87ff31fffff 0xbe47fe1ffcc7ffff

def z405 : W := mkw 0x0008500000082800 0x0002140000020a00 0x2800f80000007c00 0x0a003e0000001f00

def z406 : W := mkw 0x00285abb552c2f54 0x000a16aed54b0bd5 0xfff8fffffffc7fff 0xfffe3fffffff1fff

def z407 : W := mkw 0x239cd0000a9a6800 0x88e7340002a69a00 0xab1fc0000e1fe000 0xeac7f0000387f800

def z408 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0xab07c7800e03e000 0xeac1f1e00380f800

def z409 : W := mkw 0x04632b38c1000510 0x0118cace30400144 0xfee73fb8c1001f32 0xffb9cfee304007cc

def z410 : W := mkw 0x00085813500c2844 0x00021604d4030a11 0x7118f87ff21c60cd 0x9c463e1ffc871833

def z411 : W := mkw 0x082002a805619730 0x020800aa015865cc 0xdee007b80de39f32 0xf7b801ee0378e7cc

def z412 : W := mkw 0x03b002a80fb00300 0x00ec00aa03ec00c0 0xd7f807b80ffc0300 0xf5fe01ee03ff00c0

def z413 : W := mkw 0x004220000adb7800 0x8010880002b6de00 0xeee738000ffffc00 0xfbb9ce0003ffff00

def z414 : W := mkw 0x23def00000d93800 0x88f7bc0000364e00 0x67fff80001fc1c00 0xd9fffe00007f0700

def z415 : W := mkw 0x77ffff76f0411001 0x1dffffddbc104400 0xfffffffffde39c00 0xffffffffff78e700

def z416 : W := mkw 0x10010540a0000000 0x0400415028000000 0x100007c0f0000000 0x040001f03c000000

def z417 : W := mkw 0x0c622ab845619730 0x03188aae115865cc 0xcce038380de39f32 0x33380e0e0378e7cc

def z418 : W := mkw 0x130ddd5bf10c2d54 0x04c37756fc430b55 0xfb1ffffff31c7fff 0xfec7fffffcc71fff

def z419 : W := mkw 0x93058540aa02c0a8 0x24c161502a80b02a 0x2907c040f203e0ff 0x0a41f0103c80f83f

def z420 : W := mkw 0x63def4450adf78c0 0xd8f7bd1142b7de30 0xeffff8470ffffcc0 0xfbfffe11c3ffff30

def z421 : W := mkw 0x830480800e02c2a8 0x20c120200380b0aa 0xab07c0000e03e3ff 0xeac1f0000380f8ff

def z422 : W := mkw 0x04632bb8c5200300 0x0118caee314800c0 0xf6e73fb8cde00300 0xfdb9cfee337800c0

def z423 : W := mkw 0x0c010910c0008430 0x030042443000210c 0x00000000c0000032 0x000000003000000c

def z424 : W := mkw 0x930dd5c0ae0aeaa8 0x24c375702b82baaa 0xfb1fffc0ff1fffff 0xfec7fff03fc7ffff

def z425 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0x46ff38000dff9c00 0x51bfce00037fe700

def z426 : W := mkw 0x000000000a024000 0x0000000002809000 0x880000000e03e000 0x220000000380f800

def z427 : W := mkw 0x000000000a900000 0x0000000002a40000 0x800000000ffc0000 0x2000000003ff0000

def z428 : W := mkw 0x0000000901b40140 0x40000002406d0050 0x0000000001fc0000 0x00000000007f0000

def z429 : W := mkw 0x0304800000000000 0x00c1200000000000 0x2307c00000000000 0xc8c1f00000000000

def z430 : W := mkw 0x234ef0000a4b7800 0x88d3bc000292de00 0xab07f8000e03fc00 0xeac1fe000380ff00

def z431 : W := mkw 0x0008581250000000 0x0002160494000000 0xf918f87ff20063ff 0xbe463e1ffc8018ff

def z432 : W := mkw 0x7fffff76f0419431 0x1fffffddbc10650c 0x7ffffffff0039c32 0xdffffffffc00e70c

def z433 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0x45f8f80003fc7c00 0x117e3e0000ff1f00

def z434 : W := mkw 0x030000000a000000 0x00c0000002800000 0x830000000e000000 0xe0c0000003800000

def z435 : W := mkw 0x43b006e40e000280 0x10ec01b9038000a0 0xd7f807ff0e0003c0 0xf5fe01ffc38000f0

def z436 : W := mkw 0x300cd00230000001 0x0c0334008c000000 0x0000c00030000000 0x000030000c000000

def z437 : W := mkw 0xb3dff100aadbf828 0xacf7fc402ab6fe0a 0xeffff800fffffc3f 0xfbfffe003fffff0f

def z438 : W := mkw 0x0000000100040040 0x0000000040010010 0x01180047021c00c0 0x00460011c0870030

def z439 : W := mkw 0x030581808e02c220 0x00c160602380b088 0xbb07c780ce03e332 0xeec1f1e03380f8cc

def z440 : W := mkw 0x0008581b51040140 0x00021606d4410050 0xf118f87ff31c03c0 0xbc463e1ffcc700f0

def z441 : W := mkw 0x6cfb7bbed5619731 0x1b3edeefb55865cc 0xfeff3fbfcde39f32 0xffbfcfeff378e7cc

def z442 : W := mkw 0x930484402a024088 0x24c121100a809022 0x0000000000000000 0x0000000000000000

def z443 : W := mkw 0x9c47a910e043d438 0x2711ea443810f50e 0x2807f800f003fc3f 0x0a01fe003c00ff0f

def z444 : W := mkw 0x0c6b7bbad569bf34 0x031adeeeb55a6fcd 0xfee7ffb8fde3ff3f 0xffb9ffee3f78ffcf

def z445 : W := mkw 0x43b85eff5fbc2fd4 0x50ee17bfd7ef0bf5 0xd7f83fff0ffc1fc0 0xf5fe0fffc3ff07f0

def z446 : W := mkw 0x030004400a000080 0x00c0011002800020 0x01000040020000c0 0x0040001000800030

def z447 : W := mkw 0x43b006ec0fb00380 0x50ec01bb03ec00e0 0xd6e007b80de00300 0xf5b801ee037800c0

def z448 : W := mkw 0x030480000adb7800 0x80c1200002b6de00 0xab07c0000ffffc00 0xeac1f00003ffff00

def z449 : W := mkw 0x33dff540aadb7800 0x8cf7fd502ab6de00 0xffffffc0fffffc00 0xfffffff03fffff00

def z450 : W := mkw 0x77ffffffffbc2fd5 0x5dffffffffef0bf5 0xfffffffffffc7fff 0xffffffffffff1fff

def z451 : W := mkw 0x43b006ec05200300 0x10ec01bb014800c0 0xd7f807ff0de00300 0xf5fe01ffc37800c0

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0x2800c000f000603f 0x0a0030003c00180f

def z453 : W := mkw 0xd3b587e4ae02c2a8 0x34ed61f92b80b0aa 0xffffc7fffe03e3ff 0xfffff1ffff80f8ff

def z454 : W := mkw 0x40b0022400b00000 0x502c0089002c0000 0x04e0000000e00000 0x0138000000380000

def z455 : W := mkw 0x0008500000082800 0x0002140000020a00 0x40183800011c1c00 0x10060e0000470700

def z456 : W := mkw 0x77f7a764a0000001 0x1dfde9d928000000 0x57ff07ff00000000 0xd5ffc1ffc0000000

def z457 : W := mkw 0x0000081040000410 0x0000020410000104 0x28003800c0001c32 0x0a000e003000070c

def z458 : W := mkw 0x23d6a0000ad35000 0x88f5a80002b4d400 0xafe7c0000ee3e000 0xebf9f00003b8f800

def z459 : W := mkw 0x43b006ed052403c0 0x50ec01bb414900f0 0x57f807ff000003c0 0xd5fe01ffc00000f0

def z460 : W := mkw 0x00010998c5008730 0x00004266314021cc 0xfa073fb8cd039f32 0xfe81cfee3340e7cc

def z461 : W := mkw 0x000000010a9400c0 0x4000000042a50030 0x00000000021c00c0 0x0000000000870030

def z462 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0x4118f87f331c7ccd 0x10463e1fccc71f33

def z463 : W := mkw 0x23def0890fff7bc0 0xc8f7bc2243ffdef0 0xeffff8000fffffc0 0xfbfffe0003fffff0

def z464 : W := mkw 0x43b856ed0fbc2bc0 0x50ee15bb43ef0af0 0xfff8ffff0ffc7fc0 0xfffe3fffc3ff1ff0

def z465 : W := mkw 0x9b0585c8af63d7b8 0x26c161722bd8f5ee 0xbb07c7c0ffe3ffff 0xeec1f1f03ff8ffff

def z466 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0xc818383f031c7fff 0x32060e0fc0c71fff

def z467 : W := mkw 0x2cfa7a3841f93d10 0x8b3e9e8e107e4f44 0x44f8383801fc1c00 0x113e0e0e007f0700

def z468 : W := mkw 0x93058540aa024088 0x24c161502a809022 0x3307c7c0f20060cd 0xccc1f1f03c801833

def z469 : W := mkw 0x43b0022d0bb40140 0x50ec008b42ed0050 0xc7f8003f0ffc0000 0xf1fe000fc3ff0000

def z470 : W := mkw 0x030004c90fb403c0 0x40c0013243ed00f0 0x930007c00ffc03c0 0xe4c001f003ff00f0

def z471 : W := mkw 0x930dd5c3be0eeaec 0x24c37570ef83babb 0xbb1fc7c7fe1fe3ff 0xeec7f1f1ff87f8ff

def z472 : W := mkw 0x73def44630000001 0x1cf7bd118c000000 0x67fff84730000000 0xd9fffe11cc000000

def z473 : W := mkw 0x739cd4473a9400c1 0x5ce73511cea50030 0x0118c047321c00c0 0x00463011cc870030

def z474 : W := mkw 0xf7f7a7e4ae02c2a9 0x3dfde9f92b80b0aa 0x06e707800c038000 0x41b9c1e00300e000

def z475 : W := mkw 0x2ffffbb8c5619730 0x0bfffeee315865cc 0xffffffb8cde39f32 0xffffffee3378e7cc

def z476 : W := mkw 0x23def0000a9a6800 0x88f7bc0002a69a00 0x67fff800021c6000 0xd9fffe0000871800

def z477 : W := mkw 0x20da70000adb7800 0x88369c0002b6de00 0xccf838000ffffc00 0x333e0e0003ffff00

def z478 : W := mkw 0x8c632bb8cf63d7b8 0x2318caee33d8f5ee 0xfee73fb8cfe3ffff 0xffb9cfee33f8ffff

def z479 : W := mkw 0x930484402a024088 0x24c121100a809022 0xb900c040f20063ff 0xae4030103c8018ff

def z480 : W := mkw 0x23def81250000000 0x08f7be0494000000 0x77fff87ff0000000 0xddfffe1ffc000000

def z481 : W := mkw 0x20da781b51dd3d54 0x88369e06d4774f55 0x44f8383f01fc1c00 0x113e0e0fc07f0700

def z482 : W := mkw 0x40b002ad0fb403c0 0x502c00ab43ed00f0 0xc4f8003f0ffc03c0 0x313e000fc3ff00f0

def z483 : W := mkw 0x0001018084008220 0x0000406021002088 0xbb07c7c0fe03e3ff 0xeec1f1f03f80f8ff

def z484 : W := mkw 0x77f7af76f0000001 0x1dfdebddbc000000 0x16e707fff0000000 0x45b9c1fffc000000

def z485 : W := mkw 0x0c6323a885619730 0x0318c8ea215865cc 0x8ee707800de39f32 0x63b9c1e00378e7cc

def z486 : W := mkw 0x14010912f0000001 0x05004244bc000000 0x00000000f0000000 0x000000003c000000

def z487 : W := mkw 0x039480000a924000 0x00e5200002a49000 0xefffc0000fffe000 0xfbfff00003fff800

def z488 : W := mkw 0x0008500210082804 0x0002140084020a01 0x0000c0003000600d 0x000030000c001803

def z489 : W := mkw 0x77fff764aadb7801 0x9dfffdd92ab6de00 0xefffff800ffffc00 0xfbffffe003ffff00

def z490 : W := mkw 0x0346a0000a435000 0x00d1a8000290d400 0xefe7f8000fe3fc00 0xfbf9fe0003f8ff00

def z491 : W := mkw 0x0ff32bb8cff19730 0x03fccaee33fc65cc 0xffff3fb8cfff9f32 0xffffcfee33ffe7cc

def z492 : W := mkw 0x800000000a024088 0x2000000002809022 0x00000000020060cd 0x0000000000801833

def z493 : W := mkw 0x4020022d01240140 0x5008008b40490050 0x0000003f00000000 0x0000000fc0000000

def z494 : W := mkw 0x030cd81b5b0e6d54 0x00c33606d6c39b55 0xfb1ff87fff1fffff 0xfec7fe1fffc7ffff

def z495 : W := mkw 0x0c632b30c0419430 0x0318cacc3010650c 0x7ee73fb8c0039c32 0xdfb9cfee3000e70c

def z496 : W := mkw 0x23def0090bdf7d54 0x88f7bc0242f7df55 0xeffff8000fffffff 0xfbfffe0003ffffff

def z497 : W := mkw 0xfffffffeff63d7b9 0x3fffffffbfd8f5ee 0xffffffffffe3ffff 0xfffffffffff8ffff

def z498 : W := mkw 0x0c210bb8c5619730 0x030842ee315865cc 0x980007b8cde39f32 0x260001ee3378e7cc

def z499 : W := mkw 0xf39cd4463a024089 0x3ce735118e809022 0x0118c047320060cd 0x00463011cc801833

def z500 : W := mkw 0x0090000000900000 0x0024000000240000 0x44f8000001fc0000 0x113e0000007f0000

def z501 : W := mkw 0x0008581250082c14 0x0002160494020b05 0x0000380000001c00 0x00000e0000000700

def z502 : W := mkw 0x0042200000411000 0x0010880000104400 0x44e0380001e01c00 0x11380e0000780700

def z503 : W := mkw 0x2bdef0880ffbff30 0x8af7bc2203feffcc 0xeffff8000fffff32 0xfbfffe0003ffffcc

def z504 : W := mkw 0x800000800e02c2a8 0x200000200380b0aa 0xb900c040fe03e3ff 0xae4030103f80f8ff

def z505 : W := mkw 0xbffffff8effbffb8 0xaffffffe3bfeffee 0xfffffff8ffffffff 0xfffffffe3fffffff

def z506 : W := mkw 0x63f6a6e40ef35280 0xd8fda9b903bcd4a0 0x06e707800ce38000 0x41b9c1e00338e000

def z507 : W := mkw 0x5c632ffef5619731 0x1718cbffbd5865cc 0xfee73ffffde39f32 0xffb9cfffff78e7cc

def z508 : W := mkw 0x77fffff6f4008221 0x1dfffffdbd002088 0xfffffffffc038332 0xffffffffff00e0cc

def z509 : W := mkw 0xd39484452a9640c8 0x74e521114aa59032 0x0118c047321c60cd 0x00463011cc871833

def z510 : W := mkw 0x930dddd2fe02c2a8 0x24c37774bf80b0aa 0xfb1ffffffe03e3ff 0xfec7ffffff80f8ff

def z511 : W := mkw 0x0c6323a084619220 0x0318c8e821186488 0xbee70780cce38332 0xefb9c1e03338e0cc

def z512 : W := mkw 0x0008581841082d10 0x0002160610420b44 0xf918f838c31c7f32 0xbe463e0e30c71fcc

def z513 : W := mkw 0x9c210ff8e52087b8 0x270843fe394821ee 0x100007f8f00003ff 0x040001fe3c0000ff

def z514 : W := mkw 0x002103a885208320 0x000840ea214820c8 0xfee707b8cde38332 0xffb9c1ee3378e0cc

def z515 : W := mkw 0x0c43210080419020 0x0310c84020106408 0x0007000000038000 0x0001c0000000e000

def z516 : W := mkw 0x9f67a7e0ae63d2a8 0x27d9e9f82b98f4aa 0xbfe7c7c0fee3e3ff 0xeff9f1f03fb8f8ff

def z517 : W := mkw 0x43b006e40eb00280 0x50ec01b903ac00a0 0xc7f807800ffc0000 0xf1fe01e003ff0000

def z518 : W := mkw 0x0008581250000000 0x0002160494000000 0x4018383f00000000 0x10060e0fc0000000

def z519 : W := mkw 0x90010ddbf50487fc 0x24004376fd4121ff 0x100007fff00003ff 0x040001fffc0000ff

def z520 : W := mkw 0x9f67a7e0ae63d2a8 0x27d9e9f82b98f4aa 0x06e707800ce38000 0x41b9c1e00338e000

def z521 : W := mkw 0x2c6ffbb8c56bff30 0x8b1bfeee315affcc 0xfee7ffb8cde3ff32 0xffb9ffee3378ffcc

def z522 : W := mkw 0x63fefeff5fff7fd4 0xd8ffbfbfd7ffdff5 0xffffffffffffffff 0xffffffffffffffff

def z523 : W := mkw 0x0000000901040554 0x0000000240410155 0x00000000000003ff 0x00000000000000ff

def z524 : W := mkw 0x43b0066d0bb401c0 0x50ec019b42ed0070 0x45f8007f03fc00c0 0x117e001fc0ff0030

def z525 : W := mkw 0x039000090b940140 0x00e4000242e50050 0xd7f8007f0ffc03c0 0xf5fe001fc3ff00f0

def z526 : W := mkw 0x004a781b514d3d54 0x00129e06d4534f55 0xfffff87fffffffff 0xfffffe1fffffffff

def z527 : W := mkw 0x900585c0a402c2a8 0x240161702900b0aa 0x3807c7c0f003e3ff 0x0e01f1f03c00f8ff

def z528 : W := mkw 0x030484c00e024280 0x00c12130038090a0 0xbb07c7c00e03e3c0 0xeec1f1f00380f8f0

def z529 : W := mkw 0x000004c004000280 0x00000130010000a0 0x100007c0000003c0 0x040001f0000000f0

def z530 : W := mkw 0x9c632ff8e56197b8 0x2718cbfe395865ee 0xfee73ff8fde39fff 0xffb9cffe3f78e7ff

def z531 : W := mkw 0x10058100a0000000 0x0401604028000000 0x2007c000f0000000 0x0801f0003c000000

def z532 : W := mkw 0x20da700000d93800 0x88369c0000364e00 0xedf8f80003fc7c00 0xbb7e3e0000ff1f00

def z533 : W := mkw 0x200cd000000a6800 0x8803340000029a00 0x0000c00000006000 0x0000300000001800

def z534 : W := mkw 0x0000081841000510 0x0000020610400144 0x10000038c0000332 0x0400000e300000cc

def z535 : W := mkw 0xf3fff7edaffffbe8 0xfcfffdfb6bfffefa 0xffffffffffffffff 0xffffffffffffffff

def z536 : W := mkw 0xf7fffff6fedbfaa9 0xbdfffffdbfb6feaa 0xffffffffffffffff 0xffffffffffffffff

def z537 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0x86e007800ffc03c0 0x61b801e003ff00f0

def z538 : W := mkw 0x23def00000082800 0x08f7bc0000020a00 0xeffff800031c7c00 0xfbfffe0000c71f00

def z539 : W := mkw 0x0009599bd50caf74 0x00025666f5432bdd 0xfb1fffffff1fffff 0xfec7ffffffc7ffff

def z540 : W := mkw 0x0c622a3841611510 0x03188a8e10584544 0xfce03838c1e01f32 0xbf380e0e307807cc

def z541 : W := mkw 0xd02107eda52483e8 0x740841fb694920fa 0x100007fff00003ff 0x040001fffc0000ff

def z542 : W := mkw 0x77ffff7ff10c2d55 0x1dffffdffc430b55 0x77fffffff11c1c00 0xddfffffffc470700

def z543 : W := mkw 0xf7fffff6f40082a9 0x3dfffffdbd0020aa 0x77fffffff00003ff 0xddfffffffc0000ff

def z544 : W := mkw 0x23def4c00edb7a80 0x88f7bd3003b6dea0 0xffffffc00fffffc0 0xfffffff003fffff0

def z545 : W := mkw 0x030480000a024000 0x00c1200002809000 0xbb07c040fe03e3ff 0xeec1f0103f80f8ff

def z546 : W := mkw 0x030004c00e000280 0x00c00130038000a0 0x020007800c000000 0x408001e003000000

def z547 : W := mkw 0x0008581250082c14 0x0002160494020b05 0x7918f87ff0007c3f 0x9e463e1ffc001f0f

def z548 : W := mkw 0x0c210bb8c5208730 0x030842ee314821cc 0xf8003fb8c1001f32 0xbe000fee304007cc

def z549 : W := mkw 0x0c632bb9c56dbf74 0x0318caee715b6fdd 0xfee73fb8cfffffff 0xffb9cfee33ffffff

def z550 : W := mkw 0x402006e404200280 0x500801b9010800a0 0x0000078000000000 0x000001e000000000

def z551 : W := mkw 0xd3b587e4aeb2c2a8 0x74ed61f92bacb0aa 0xbfe7c7c0fee3e3ff 0xeff9f1f03fb8f8ff

def z552 : W := mkw 0x0c62222000611000 0x0318888800184400 0x04e0000000e00000 0x0138000000380000

def z553 : W := mkw 0x0042200000411000 0x0010880000104400 0x2807380000039c00 0x0a01ce000000e700

def z554 : W := mkw 0x0020022801200100 0x0008008a00480040 0x44e0003801e00000 0x1138000e00780000

def z555 : W := mkw 0x37dff912fadb7801 0x8df7fe44beb6de00 0xeffff800fffffc00 0xfbfffe003fffff00

def z556 : W := mkw 0x67fa7eff5fb403c1 0x59fe9fbfd7ed00f0 0xd7f83fff0ffc03c0 0xf5fe0fffc3ff00f0

def z557 : W := mkw 0x0008581250082c14 0x0002160494020b05 0xe918f800f31c7c3f 0xba463e003cc71f0f

def z558 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0x7118f87ff11c1c00 0x9c463e1ffc470700

def z559 : W := mkw 0x0c2103a084208220 0x030840e821082088 0x0000078000000000 0x000001e000000000

def z560 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0xf818383fc11c1f32 0xbe060e0ff04707cc

def z561 : W := mkw 0x74fffb36f0000001 0x1d3ffecdbc000000 0x64fff83ff0000000 0x193ffe0ffc000000

def z562 : W := mkw 0x4ff327ed8ff593e0 0x53fcc9fb63fd64f8 0xd7ff07ff0fff83c0 0xf5ffc1ffc3ffe0f0

def z563 : W := mkw 0xb3dff5c0ae02c2a8 0x2cf7fd702b80b0aa 0xffffffc0fe03e3ff 0xfffffff03f80f8ff

def z564 : W := mkw 0x0000008004000200 0x0000002001000080 0x920007800c000300 0xe48001e0030000c0

def z565 : W := mkw 0x0008589b5fbc2fd4 0x40021626d7ef0bf5 0xf918f87ffffc7fff 0xbe463e1fffff1fff

def z566 : W := mkw 0x0000081250000414 0x0000020494000105 0x00000000f000003f 0x000000003c00000f

def z567 : W := mkw 0x4090000500940040 0x5024000140250010 0x00180007001c0000 0x00060001c0070000

def z568 : W := mkw 0x000850000adb7800 0x8002140002b6de00 0xe918f8000ffffc00 0xba463e0003ffff00

def z569 : W := mkw 0x00000819410c2d54 0x0000020650430b55 0xf8003838c31c7fff 0xbe000e0e30c71fff

def z570 : W := mkw 0x73bcd66630000001 0x1cef35998c000000 0x57f8c7ff30000000 0xd5fe31ffcc000000

def z571 : W := mkw 0x90058180a402c228 0x240160602900b08a 0xba07c780fc03e33f 0xee81f1e03f00f8cf

def z572 : W := mkw 0x20def00000db7800 0x8837bc000036de00 0x6cfff80001fffc00 0x1b3ffe00007fff00

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1180000031c0000 0xb046000000c70000

def z574 : W := mkw 0x2cfb7bb8c5f9bf30 0x8b3edeee317e6fcc 0xfeff3fb8cdff9f32 0xffbfcfee337fe7cc

def z575 : W := mkw 0x8008589b5f0eeffc 0x20021626d7c3bbff 0xf918f87fff1fffff 0xbe463e1fffc7ffff

def z576 : W := mkw 0x0000000000082800 0x0000000000020a00 0x88000000031c7c00 0x2200000000c71f00

def z577 : W := mkw 0x900105c0a40082a8 0x24004170290020aa 0xb900c7c0f20063ff 0xae4031f03c8018ff

def z578 : W := mkw 0x030105c08e0082a0 0x00c04170238020a8 0xbb0707c0ce0383f2 0xeec1c1f03380e0fc

def z579 : W := mkw 0x0008581a51000510 0x0002160694400144 0xf918f87ff1001f32 0xbe463e1ffc4007cc

def z580 : W := mkw 0x23dff1808edbfa20 0x88f7fc6023b6fe88 0xffffff80cfffff32 0xffffffe033ffffcc

def z581 : W := mkw 0x0008581250082c14 0x0002160494020b05 0xb900f840f2007fff 0xae403e103c801fff

def z582 : W := mkw 0x0042200000411000 0x0010880000104400 0x06e700000ce38000 0x41b9c0000338e000

def z583 : W := mkw 0x43b00eff5fb407d4 0x50ec03bfd7ed01f5 0xd7f807fffffc03ff 0xf5fe01ffffff00ff

def z584 : W := mkw 0x0f632ff8cf6197b0 0x03d8cbfe33d865ec 0xffe73ff8cfe39ff2 0xfff9cffe33f8e7fc

def z585 : W := mkw 0x0000081841000510 0x0000020610400144 0xf900f878f3007fff 0xbe403e1e3cc01fff

def z586 : W := mkw 0x67fefa365adb7801 0x99ffbe8d96b6de00 0xeffff83f0ffffc00 0xfbfffe0fc3ffff00

def z587 : W := mkw 0x23def0000ad35000 0x88f7bc0002b4d400 0x67fff8000ce38000 0xd9fffe000338e000

def z588 : W := mkw 0x77dffd56f0000001 0x1df7ff55bc000000 0x211ff847f0000000 0x0847fe11fc000000

def z589 : W := mkw 0x932587e8af22c3a8 0x24c961fa2bc8b0ea 0xffe7c7f8ffe3e3ff 0xfff9f1fe3ff8f8ff

def z590 : W := mkw 0x0001018084008220 0x0000406021002088 0x020707800c038000 0x4081c1e00300e000

def z591 : W := mkw 0x47f32ffdcfb403c0 0x51fccbff73ed00f0 0xf7ff3fffcffc03c0 0xfdffcffff3ff00f0

def z592 : W := mkw 0x7394844420000001 0x1ce5211108000000 0x0000000000000000 0x0000000000000000

def z593 : W := mkw 0x3447a100a0000001 0x0d11e84028000000 0x0007000000000000 0x0001c00000000000

def z594 : W := mkw 0x40b85a3f51bc2d54 0x502e168fd46f0b55 0x44f8383f01fc1c00 0x113e0e0fc07f0700

def z595 : W := mkw 0x900dd912f00aec3c 0x24037644bc02bb0f 0x2807f800f003fc3f 0x0a01fe003c00ff0f

def z596 : W := mkw 0x23def81b5bdf7d54 0x88f7be06d6f7df55 0xeffff83f0ffffc00 0xfbfffe0fc3ffff00

def z597 : W := mkw 0x0000000000000000 0x0000000000000000 0x91000040020003c0 0xa4400010008000f0

def z598 : W := mkw 0x00200ab845200710 0x000802ae114801c4 0xfee03fb8cde01f32 0xffb80fee337807cc

def z599 : W := mkw 0x0000008805200300 0x00000022014800c0 0x800000000de00300 0x20000000037800c0

def z600 : W := mkw 0x0c432910c0419430 0x0310ca443010650c 0xeee73800cde39c32 0xfbb9ce003378e70c

def z601 : W := mkw 0x239cd0031a9e6844 0x88e73400c6a79a11 0x0118c047321c60cd 0x00463011cc871833

def z602 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0xfff8c7fffffc63ff 0xfffe31ffffff18ff

def z603 : W := mkw 0x9f67aff8ef63d7b8 0x27d9ebfe3bd8f5ee 0xfee73fb8cde39f32 0xffb9cfee3378e7cc

def z604 : W := mkw 0x239cd81b5b9e6d54 0x88e73606d6e79b55 0xf918f87ff31c7fff 0xbe463e1ffcc71fff

def z605 : W := mkw 0x0c42281040411410 0x03108a0410104504 0x0000380000001c00 0x00000e0000000700

def z606 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0x0307c7c03e03e0cd 0x40c1f1f00f80f833

def z607 : W := mkw 0x739cdc5f710c2d55 0x1ce73717dc430b55 0xf918f87ff31c7fff 0xbe463e1ffcc71fff

def z608 : W := mkw 0x0000081040000000 0x0000020410000000 0x70003838c0000000 0x9c000e0e30000000

def z609 : W := mkw 0x002002a004200200 0x000800a801080080 0x06e007800ce00000 0x41b801e003380000

def z610 : W := mkw 0x204ef81b514f7d54 0x8813be06d453df55 0xf91ff87ff31fffff 0xbe47fe1ffcc7ffff

def z611 : W := mkw 0x7ffffff6f4619221 0x1ffffffdbd186488 0x77fffffffce38000 0xddffffffff38e000

def z612 : W := mkw 0x0000000000411000 0x0000000000104400 0x880000000de39c00 0x220000000378e700

def z613 : W := mkw 0x63fef6e40efb7a80 0xd8ffbdb903bedea0 0xefffff800ffffc00 0xfbffffe003ffff00

def z614 : W := mkw 0x1f67aff8e5619730 0x07d9ebfe395865cc 0xffe7fff8fde39f32 0xfff9fffe3f78e7cc

def z615 : W := mkw 0x0042200000000000 0x0010880000000000 0x66e7380000000000 0xd9b9ce0000000000

def z616 : W := mkw 0x439004450a9400c0 0x50e4011142a50030 0xc7f800470ffc00c0 0xf1fe0011c3ff0030

def z617 : W := mkw 0x7ffffffffff597f1 0x5ffffffffffd65fc 0xffffffffffff9ff2 0xffffffffffffe7fc

def z618 : W := mkw 0x2ffefa384bfb7d10 0x8bffbe8e12fedf44 0xeffff8380ffffc00 0xfbfffe0e03ffff00

def z619 : W := mkw 0xb04ff100a04bf828 0xac13fc402812fe0a 0x2807f800f003fc3f 0x0a01fe003c00ff0f

def z620 : W := mkw 0x77fffff6fe000281 0x1dfffffdbf8000a0 0xf7fffffffe0003c0 0xfdffffffff8000f0

def z621 : W := mkw 0x0000081b51040554 0x00000206d4410155 0xf800387ff1001fff 0xbe000e1ffc4007ff

def z622 : W := mkw 0x23d6a0000ad35000 0x88f5a80002b4d400 0xc7ff00000fff8000 0xf1ffc00003ffe000

def z623 : W := mkw 0x0001010080000000 0x0000404020000000 0x32070780c0000000 0xcc81c1e030000000

def z624 : W := mkw 0x204ef812504b7c14 0x8813be049412df05 0x2807f800f003fc3f 0x0a01fe003c00ff0f

def z625 : W := mkw 0x930dddd2fe0aeebc 0x24c37774bf82bbaf 0xbb07ffc0fe03ffff 0xeec1fff03f80ffff

def z626 : W := mkw 0x13058540a0000000 0x04c1615028000000 0xbb07c7c0f20063ff 0xeec1f1f03c8018ff

def z627 : W := mkw 0x23def00000411000 0x08f7bc0000104400 0xeffff8000de39c00 0xfbfffe000378e700

def z628 : W := mkw 0x6098500610000001 0x1826140184000000 0x0018000700000000 0x00060001c0000000

def z629 : W := mkw 0x402006ed0fb403c0 0x500801bb43ed00f0 0x900007ff0ffc03c0 0x240001ffc3ff00f0

def z630 : W := mkw 0x43f226ed0ff513c0 0x50fc89bb43fd44f0 0xffff3fff0fff9fc0 0xffffcfffc3ffe7f0

def z631 : W := mkw 0x0008500000082800 0x0002140000020a00 0x0118c000021c6000 0x0046300000871800

def z632 : W := mkw 0xf7ffffffff0eeffd 0x3dffffffffc3bbff 0xffffffffff1fffff 0xffffffffffc7ffff

def z633 : W := mkw 0x90095ddbf50caffc 0x24025776fd432bff 0xf918fffff31c7fff 0xbe463ffffcc71fff

def z634 : W := mkw 0x9347a5c0ae43d2a8 0x24d1e9702b90f4aa 0xffe7ffc0ffe3ffff 0xfff9fff03ff8ffff

def z635 : W := mkw 0x2098500000982800 0x8826140000260a00 0x00180000001c0000 0x0006000000070000

def z636 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0x8a0707800e03e3ff 0x6281c1e00380f8ff

def z637 : W := mkw 0x40000445000400c0 0x5000011140010030 0x00000047000000c0 0x00000011c0000030

def z638 : W := mkw 0x4ff22efd4ff517d0 0x53fc8bbf53fd45f4 0xd7f83fff0ffc1fc0 0xf5fe0fffc3ff07f0

def z639 : W := mkw 0x000000800e000280 0x00000020038000a0 0x800000000e0003c0 0x20000000038000f0

def z640 : W := mkw 0x2ffffbbbdfffff74 0x8bfffeeef7ffffdd 0xffffffffffffffff 0xffffffffffffffff

def z641 : W := mkw 0x0c200a3841200510 0x0308028e10480144 0x0000003800000000 0x0000000e00000000

def z642 : W := mkw 0x43985c5f5b9c2dd4 0x50e61717d6e70b75 0xf918f87ff31c7fff 0xbe463e1ffcc71fff

def z643 : W := mkw 0x93058dd8ef02c7b8 0x24c163763bc0b1ee 0xfb07fff8ff03ffff 0xfec1fffe3fc0ffff

def z644 : W := mkw 0x000000890fb403c0 0x4000002243ed00f0 0xd118007f0ffc03c0 0xb446001fc3ff00f0

def z645 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0x291ff800021ffc00 0x0a47fe000087ff00

def z646 : W := mkw 0x23def0090bdf7940 0x88f7bc0242f7de50 0xfffff87f0fffffc0 0xfffffe1fc3fffff0

def z647 : W := mkw 0x930585c9af06c3e8 0x24c161726bc1b0fa 0xfb1fc7ffff1fe3ff 0xfec7f1ffffc7f8ff

def z648 : W := mkw 0x0008500b110c2d54 0x00021402c4430b55 0x8918c047331c7fff 0x22463011ccc71fff

def z649 : W := mkw 0x77fffffff52403c1 0x5dfffffffd4900f0 0x77fffffff00003c0 0xddfffffffc0000f0

def z650 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0x2a07c780fc03e03f 0x4a81f1e03f00f80f

def z651 : W := mkw 0xd3b587edafb6c3e8 0x74ed61fb6bedb0fa 0xd7ff07ff0fff83c0 0xf5ffc1ffc3ffe0f0

def z652 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0x07ffc0000effe000 0x41fff00003bff800

def z653 : W := mkw 0x43b856ef1fbc2bc4 0x50ee15bbc7ef0af1 0xd7f8c7ff3ffc63cd 0xf5fe31ffcfff18f3

def z654 : W := mkw 0x63fa76ed0ffd3bc0 0xd8fe9dbb43ff4ef0 0xd7f83fff0ffc1fc0 0xf5fe0fffc3ff07f0

def z655 : W := mkw 0x0c632b38c1611510 0x0318cace30584544 0x76e73fb8c1e01c00 0xddb9cfee30780700

def z656 : W := mkw 0xa3def0800edbfaa8 0xa8f7bc2003b6feaa 0xeffff8000fffffff 0xfbfffe0003ffffff

def z657 : W := mkw 0x739cdc5670000001 0x1ce737159c000000 0x7118f87ff0000000 0x9c463e1ffc000000

def z658 : W := mkw 0x0808589b556dbf74 0x02021626d55b6fdd 0xf918f87fffffffff 0xbe463e1fffffffff

def z659 : W := mkw 0x77fffff6feb00281 0x5dfffffdbfac00a0 0x77fffffffce00000 0xddffffffff380000

def z660 : W := mkw 0x002002a90fb403c0 0x400800aa43ed00f0 0xd6e007b80ffc03c0 0xf5b801ee03ff00f0

def z661 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0x6818f83ff11c7c3f 0x1a063e0ffc471f0f

def z662 : W := mkw 0x0c6b7bb8c569bf30 0x031adeee315a6fcc 0xffffffb8cfffff32 0xffffffee33ffffcc

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0xa900c00002006000 0xaa40300000801800

def z664 : W := mkw 0x0c432918c1419530 0x0310ca463050654c 0xf8073838c1039f32 0xbe01ce0e3040e7cc

def z665 : W := mkw 0x439004cd0fb403c0 0x50e4013343ed00f0 0x811800470ffc03c0 0x20460011c3ff00f0

def z666 : W := mkw 0x204a700000493800 0x88129c0000124e00 0x0000380000001c00 0x00000e0000000700

def z667 : W := mkw 0x4cf32bbdc5f59770 0x533ccaef717d65dc 0xfeff3fbfcdff9f32 0xffbfcfeff37fe7cc

def z668 : W := mkw 0x00000009010c2d54 0x0000000240430b55 0xd918007f031c7fff 0xb646001fc0c71fff

def z669 : W := mkw 0x0000081841000510 0x0000020610400144 0x4000383801001c00 0x10000e0e00400700

def z670 : W := mkw 0x00085003100c2844 0x00021400c4030a11 0x00180007001c0000 0x00060001c0070000

def z671 : W := mkw 0x002002a805200300 0x000800aa014800c0 0x100007b800000300 0x040001ee000000c0

def z672 : W := mkw 0x4ff327e48ef192a0 0x53fcc9f923bc64a8 0x06e707800ce38000 0x41b9c1e00338e000

def z673 : W := mkw 0x77fff764a0000001 0x1dfffdd928000000 0x67ffff8000000000 0xd9ffffe000000000

def z674 : W := mkw 0x930484c02e024288 0x24c121300b8090a2 0x9300c7c03e0063cd 0xe4c031f00f8018f3

def z675 : W := mkw 0x204ef00000000000 0x0813bc0000000000 0x2007f80000000000 0x0801fe0000000000

def z676 : W := mkw 0x930585c0aedbfaa8 0xa4c161702bb6feaa 0xbb07c7c0ffffffff 0xeec1f1f03fffffff

def z677 : W := mkw 0xb3dffddbffdffffc 0xacf7ff76fff7ffff 0xffffffffffffffff 0xffffffffffffffff

def z678 : W := mkw 0x9f258ff8ef22c7b8 0x27c963fe3bc8b1ee 0xbb07c7f8fe03e3ff 0xeec1f1fe3f80f8ff

def z679 : W := mkw 0x4ffb7fffdffdbff4 0x53fedffff7ff6ffd 0xffffffffffffffff 0xffffffffffffffff

def z680 : W := mkw 0x27fffb30cadb7800 0x89fffecc32b6de00 0xffffffb8cffffc00 0xffffffee33ffff00

def z681 : W := mkw 0x0008581b51040554 0x00021606d4410155 0x7118f87ff00003ff 0x9c463e1ffc0000ff

def z682 : W := mkw 0x244a781250000001 0x09129e0494000000 0x0000380000000000 0x00000e0000000000

def z683 : W := mkw 0x000000090bdf7d54 0x8000000242f7df55 0x880000000fffffff 0x2200000003ffffff

def z684 : W := mkw 0x080000880ffbff30 0x8200002203feffcc 0x880000000fffff32 0x2200000003ffffcc

def z685 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0x3800f87ff0007fff 0x0e003e1ffc001fff

def z686 : W := mkw 0x344ff912f0082c15 0x0d13fe44bc020b05 0x2807f800f0007c3f 0x0a01fe003c001f0f

def z687 : W := mkw 0x9767aff0ee02c2a8 0x25d9ebfc3b80b0aa 0xffe7fff8fe03e3ff 0xfff9fffe3f80f8ff

def z688 : W := mkw 0x77ffff7ff1b40141 0x5dffffdffc6d0050 0x77fffffff1fc0000 0xddfffffffc7f0000

def z689 : W := mkw 0x0008500210000000 0x0002140084000000 0x0118c04730000000 0x00463011cc000000

def z690 : W := mkw 0x000000000a9a6800 0x8000000002a69a00 0x00000000021c6000 0x0000000000871800

def z691 : W := mkw 0x9004800020024008 0x2401200008009002 0x0000c0003000600d 0x000030000c001803

def z692 : W := mkw 0x64fa7a3f51b40141 0x593e9e8fd46d0050 0x44f8383f01fc0000 0x113e0e0fc07f0000

def z693 : W := mkw 0x40b0022d01b40140 0x502c008b406d0050 0xd5f8007f03fc03c0 0xb57e001fc0ff00f0

def z694 : W := mkw 0x00085009010c2940 0x0002140240430a50 0xf918f87f031c7fc0 0xbe463e1fc0c71ff0

def z695 : W := mkw 0x93058ddbff06c7fc 0x24c16376ffc1b1ff 0xbb07c7fffe03e3ff 0xeec1f1ffff80f8ff

def z696 : W := mkw 0x439854471a9c28c4 0x50e61511c6a70a31 0x0118c047321c60cd 0x00463011cc871833

def z697 : W := mkw 0x0800000000419430 0x020000000010650c 0x0800000000039c32 0x020000000000e70c

def z698 : W := mkw 0xd3b587e4aeb2c2a8 0x74ed61f92bacb0aa 0x06e707800ce38000 0x41b9c1e00338e000

def z699 : W := mkw 0x039000000a900000 0x00e4000002a40000 0x01180000021c0000 0x0046000000870000

def z700 : W := mkw 0xd32587edaf26c3e8 0x74c961fb6bc9b0fa 0xbb07c7fffe03e3ff 0xeec1f1ffff80f8ff

def z701 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100c040320060cd 0x004030100c801833

def z702 : W := mkw 0x20d2200000d11000 0x8834880000344400 0x04e0000000e00000 0x0138000000380000

def z703 : W := mkw 0x23def0000a024000 0x08f7bc0002809000 0xeffff8000e03e000 0xfbfffe000380f800

def z704 : W := mkw 0x030480000a024000 0x00c1200002809000 0x020700000c038000 0x4081c0000300e000

def z705 : W := mkw 0x04432910c0000000 0x0110ca4430000000 0x20073800c0000000 0x0801ce0030000000

def z706 : W := mkw 0x23def81b510c2d54 0x08f7be06d4430b55 0xfffff87ff31c7fff 0xfffffe1ffcc71fff

def z707 : W := mkw 0x73def4442adb7801 0x9cf7bd110ab6de00 0xeffff8000ffffc00 0xfbfffe0003ffff00

def z708 : W := mkw 0xb44ff912f04bf829 0xad13fe44bc12fe0a 0x2807f800f003fc3f 0x0a01fe003c00ff0f

def z709 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0xfffff800cfffff32 0xfffffe0033ffffcc

def z710 : W := mkw 0x000000890fbc2bc0 0x4000002243ef0af0 0x880000000ffc7fc0 0x2200000003ff1ff0

def z711 : W := mkw 0x77ffff76fad35001 0x9dffffddbeb4d400 0xfffffffffee3e000 0xffffffffffb8f800

def z712 : W := mkw 0x039000890fb403c0 0x40e4002243ed00f0 0x811800000ffc03c0 0x2046000003ff00f0

def z713 : W := mkw 0x08000089052487f0 0x42000022414921fc 0x00000000000003f2 0x00000000000000fc

def z714 : W := mkw 0x930585c0a402c2a8 0x24c161702900b0aa 0x3b07c7c0f003e3ff 0xcec1f1f03c00f8ff

def z715 : W := mkw 0x002002a90fb403c0 0x400800aa43ed00f0 0xd7f807ff0ffc03c0 0xf5fe01ffc3ff00f0

def z716 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0xffff3fffcde39f32 0xffffcffff378e7cc

def z717 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x76ff3fbfc0000000 0xddbfcfeff0000000

def z718 : W := mkw 0x47f32f74cad11000 0x11fccbdd32b44400 0xffff3fffcfff9c00 0xffffcffff3ffe700

def z719 : W := mkw 0x77fff766b0000001 0x1dfffdd9ac000000 0x57ffc7ff30000000 0xd5fff1ffcc000000

def z720 : W := mkw 0x0800008905659770 0x02000022415965dc 0x880000000fff9ff2 0x2200000003ffe7fc

def z721 : W := mkw 0x130ddd52fa0a6800 0x04c37754be829a00 0xfb1fffffff1ffc00 0xfec7ffffffc7ff00

def z722 : W := mkw 0x8c632bb8c56197b8 0x2318caee315865ee 0xfee73fb8cde39fff 0xffb9cfee3378e7ff

def z723 : W := mkw 0x0c632bb9c5659774 0x0318caee715965dd 0xfee73fb8cde39fff 0xffb9cfee3378e7ff

def z724 : W := mkw 0x43b006ed0fb407d4 0x50ec01bb43ed01f5 0xd7f807ff0ffc03ff 0xf5fe01ffc3ff00ff

def z725 : W := mkw 0x9c4ff912f04bfc3c 0x2713fe44bc12ff0f 0x2807f800f003fc3f 0x0a01fe003c00ff0f

def z726 : W := mkw 0x77ffff76f0082c15 0x1dffffddbc020b05 0x77fffffff0001c00 0xddfffffffc000700

def z727 : W := mkw 0x54210f76f0000415 0x150843ddbc000105 0x100007fff000003f 0x040001fffc00000f

def z728 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x55f8fffff0000000 0x157e3ffffc000000

def z729 : W := mkw 0x0c632b30c0419430 0x0318cacc3010650c 0xfee73fb8cde39c32 0xffb9cfee3378e70c

def z730 : W := mkw 0x004220000ad11000 0x0010880002b44400 0xeee738000fff9c00 0xfbb9ce0003ffe700

def z731 : W := mkw 0x77ffff76f0082801 0x1dffffddbc020a00 0x7ffffffff0007c00 0xdffffffffc001f00

def z732 : W := mkw 0x0062222000411000 0x0018888800104400 0xfee73fb80de39c00 0xffb9cfee0378e700

def z733 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0xfff83fff0ffc1fc0 0xfffe0fffc3ff07f0

def z734 : W := mkw 0x0bd220890ff597f0 0x42f4882243fd65fc 0xefff38000fff9ff2 0xfbffce0003ffe7fc

def z735 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0x6efff8000dfffc00 0x5bbffe00037fff00

def z736 : W := mkw 0x000000890ffd3bc0 0xc000002243ff4ef0 0x800000000ffc1fc0 0x2000000003ff07f0

def z737 : W := mkw 0x44200e7650000001 0x1108039d94000000 0x100007ff00000000 0x040001ffc0000000

def z738 : W := mkw 0x346ffb32f0000001 0x0d1bfeccbc000000 0x77fffffff0000000 0xddfffffffc000000

def z739 : W := mkw 0x0c632bb9c5659770 0x0318caee715965dc 0xfee73fb8cfff9ff2 0xffb9cfee33ffe7fc

def z740 : W := mkw 0x43b006640a900000 0x10ec019902a40000 0x06e007800ce00000 0x41b801e003380000

def z741 : W := mkw 0x030484c00e024280 0x00c12130038090a0 0xbb07c7c0fe03e3ff 0xeec1f1f03f80f8ff

def z742 : W := mkw 0x0300044000000000 0x00c0011000000000 0x531807ff00000000 0xd4c601ffc0000000

def z743 : W := mkw 0xf7ffff76fa024089 0x3dffffddbe809022 0xfffffffffe03e0cd 0xffffffffff80f833

def z744 : W := mkw 0x0c632bb9c5659770 0x0318caee715965dc 0xfeff3fbfcdff9f32 0xffbfcfeff37fe7cc

def z745 : W := mkw 0x77ffff76f0024001 0x1dffffddbc009000 0x7ffffffff003e000 0xdffffffffc00f800

def z746 : W := mkw 0x77ffff76fa4b7801 0x9dffffddbe92de00 0xfffffffffe03fc00 0xffffffffff80ff00

def z747 : W := mkw 0x00432998c5419730 0x0010ca66315065cc 0xfee73fb8cde39f32 0xffb9cfee3378e7cc

def z748 : W := mkw 0x77f7a76da10c2d55 0x1dfde9db68430b55 0x8ee70780031c7fff 0x63b9c1e000c71fff

def z749 : W := mkw 0x63b8566610000001 0x18ee159984000000 0x57f807ff00000000 0xd5fe01ffc0000000

def z750 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0xfffffffff1001c00 0xfffffffffc400700

def z751 : W := mkw 0x54210f76f0000001 0x150843ddbc000000 0x3100c7fff0000000 0x8c4031fffc000000

def z752 : W := mkw 0x43b486ed0fb643c0 0x50ed21bb43ed90f0 0xd7f8c7ff0ffc63c0 0xf5fe31ffc3ff18f0

def z753 : W := mkw 0x90058189afb6c3e8 0x640160626bedb0fa 0xa807c000ffffe3ff 0x2a01f0003ffff8ff

def z754 : W := mkw 0x900105c0a40082a8 0x24004170290020aa 0xbb07c7c0fe03e3ff 0xeec1f1f03f80f8ff

def z755 : W := mkw 0x000000890fb403c0 0x4000002243ed00f0 0xb900c040fffc63ff 0xae4030103fff18ff

def z756 : W := mkw 0x0843218885619730 0x0210c862215865cc 0xfee73f80cde39f32 0xffb9cfe03378e7cc

def z757 : W := mkw 0x939585c0ae92c2a8 0x24e561702ba4b0aa 0xbb1fc7c0fe1fe3ff 0xeec7f1f03f87f8ff

def z758 : W := mkw 0x23da70000ad93800 0x88f69c0002b64e00 0xefff38000fff9c00 0xfbffce0003ffe700

def z759 : W := mkw 0x739ddd56f0000001 0x1ce77755bc000000 0x731ffffff0000000 0xdcc7fffffc000000

def z760 : W := mkw 0x77ffff76f00a6801 0x9dffffddbc029a00 0x77fffffff0006000 0xddfffffffc001800

def z761 : W := mkw 0x08000089056597f0 0x42000022415965fc 0x880000000de39ff2 0x220000000378e7fc

def z762 : W := mkw 0x77ffff76f04b7c15 0x9dffffddbc12df05 0x7ffffffff003fc3f 0xdffffffffc00ff0f

def z763 : W := mkw 0x54295f76f0082801 0x150a57ddbc020a00 0xf918fffff31c7c00 0xbe463ffffcc71f00

def z764 : W := mkw 0x57258f76f0000001 0x15c963ddbc000000 0x1100c7fff0000000 0x044031fffc000000

def z765 : W := mkw 0x43b006650a9400c0 0x50ec019942a50030 0xd7f807ff0ffc00c0 0xf5fe01ffc3ff0030

def z766 : W := mkw 0x930585c0ae92c2a8 0x24c161702ba4b0aa 0xbb07c7c0ffffe3ff 0xeec1f1f03ffff8ff

def z767 : W := mkw 0x43b85ef65eb82e94 0x50ee17bd97ae0ba5 0x2ee0ff80fce07c3f 0x4bb83fe03f381f0f

def z768 : W := mkw 0x77ffff76fa024001 0x1dffffddbe809000 0x77fffffff2006000 0xddfffffffc801800

def z769 : W := mkw 0x7fffff76f049bc35 0x1fffffddbc126f0d 0x7ffffffff003fc3f 0xdffffffffc00ff0f

def z770 : W := mkw 0x000000890fbc2bc4 0x4000002243ef0af1 0x800000000ffc63cd 0x2000000003ff18f3

def z771 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0xd6e73fb80de39f00 0xf5b9cfee0378e7c0

def z772 : W := mkw 0x0043210080411000 0x0010c84020104400 0xfee73f80cde39c00 0xffb9cfe03378e700

def z773 : W := mkw 0x930ddddbff0eeffc 0x24c37776ffc3bbff 0x421f3fbf0d1f9c00 0x5087cfefc347e700

def z774 : W := mkw 0xf7ffff76fa9a6889 0xbdffffddbea69a22 0x77fffffff21c60cd 0xddfffffffc871833

def z775 : W := mkw 0x90058180a402c228 0x240160602900b08a 0xbb07c7c0fe03e3ff 0xeec1f1f03f80f8ff

def z776 : W := mkw 0x7b9cd4ce35619731 0x1ee735338d5865cc 0x8918c0473de39f32 0x22463011cf78e7cc

def z777 : W := mkw 0x0c632bbbd5659774 0x0318caeef55965dd 0xffe7ffffffe3ffff 0xfff9fffffff8ffff

def z778 : W := mkw 0x800000890fb643c8 0x6000002243ed90f2 0x800000000ffc63cd 0x2000000003ff18f3

def z779 : W := mkw 0x344ff99bffb403c1 0x4d13fe66ffed00f0 0xa007f800fffc03c0 0x2801fe003fff00f0

def z780 : W := mkw 0x43b486ed0fb643c0 0x50ed21bb43ed90f0 0xd7ff07ff0fff83c0 0xf5ffc1ffc3ffe0f0

def z781 : W := mkw 0x00d2200000d11000 0x0034880000344400 0xeeff38000dff9c00 0xfbbfce00037fe700

def z782 : W := mkw 0x0c632bb9c56597f0 0x4318caee715965fc 0xfee73fb8cde39ff2 0xffb9cfee3378e7fc

def z783 : W := mkw 0x00000089052403c0 0x40000022414900f0 0x80000000031c03c0 0x2000000000c700f0

def z784 : W := mkw 0x3c4ff912f04bfc31 0x8f13fe44bc12ff0c 0x2807f800f003fc32 0x0a01fe003c00ff0c

def z785 : W := mkw 0x0c6323a885619730 0x0318c8ea215865cc 0xeee73f800de39f32 0xfbb9cfe00378e7cc

def z786 : W := mkw 0x40b002ad05b40340 0x502c00ab416d00d0 0xd7f807ff0ffc03c0 0xf5fe01ffc3ff00f0

def z787 : W := mkw 0x7fffff76f0419021 0x1fffffddbc106408 0x77fffffff0038000 0xddfffffffc00e000

def z788 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0xfffff840fffffc00 0xfffffe103fffff00

def z789 : W := mkw 0xd7258f76fa024089 0x35c963ddbe809022 0x1100c7fff20060cd 0x044031fffc801833

def z790 : W := mkw 0x080000890fffff74 0x8200002243ffffdd 0x880000000fffffff 0x2200000003ffffff

def z791 : W := mkw 0x77ffff76f0082c15 0x1dffffddbc020b05 0xfffffffff31c7c3f 0xfffffffffcc71f0f

def z792 : W := mkw 0x0c632bbbd5659774 0x0318caeef55965dd 0xfee73fbfcde39f32 0xffb9cfeff378e7cc

def z793 : W := mkw 0x43b85e7650082c14 0x10ee179d94020b05 0x7ff8fffff0007c3f 0xdffe3ffffc001f0f

def z794 : W := mkw 0x4cfa7a3f51fd3d54 0x533e9e8fd47f4f55 0x44f8383f01fc1c00 0x113e0e0fc07f0700

def z795 : W := mkw 0x64fa7e7650000001 0x193e9f9d94000000 0x54f83fff00000000 0x153e0fffc0000000

def z796 : W := mkw 0x4c210fffd52487f4 0x530843fff54921fd 0x100007fff00003ff 0x040001fffc0000ff

def z797 : W := mkw 0xb39cd4402a9a6888 0xace735100aa69a22 0x0118c000021c6000 0x0046300000871800

def z798 : W := mkw 0x44210b36d0000001 0x110842cdb4000000 0x100007bfc0000000 0x040001eff0000000

def z799 : W := mkw 0x54210f76fadb7801 0x950843ddbeb6de00 0x980007fffffffc00 0x260001ffffffff00

def z800 : W := mkw 0x639cd4471a9e68c4 0xd8e73511c6a79a31 0x0118c047321c60cd 0x00463011cc871833

def z801 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0xfffff87f0ffffc00 0xfffffe1fc3ffff00

def z802 : W := mkw 0x080000890ffdbff4 0x4200002243ff6ffd 0x880000000fffffff 0x2200000003ffffff

def z803 : W := mkw 0x20da700000d93800 0x88369c0000364e00 0xeffff8000ffffc00 0xfbfffe0003ffff00

def z804 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0xd6f807bf0dfc0300 0xf5be01efc37f00c0

def z805 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0xfee7ffb8fde3ff3f 0xffb9ffee3f78ffcf

def z806 : W := mkw 0x23d6a0890ff753c0 0xc8f5a82243fdd4f0 0x86e700000fff83c0 0x61b9c00003ffe0f0

def z807 : W := mkw 0x0c6b73a3946dba64 0x031adce8e51b6e99 0x07ffc7c73effe0cd 0x41fff1f1cfbff833

def z808 : W := mkw 0x74fb7f76f0000001 0x1d3edfddbc000000 0x44f83fbf00000000 0x113e0fefc0000000

def z809 : W := mkw 0x74fb7f76f0000001 0x1d3edfddbc000000 0x75f8fffff0000000 0x9d7e3ffffc000000

def z810 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0xf7f8c7fffffc03c0 0xfdfe31ffffff00f0

def z811 : W := mkw 0xd3b486642a024088 0x34ed21990a809022 0x57f8c7ff320060cd 0xd5fe31ffcc801833

def z812 : W := mkw 0x53bddf76f0000000 0x14ef77ddbc000000 0x77fffffff0000000 0xddfffffffc000000

def z813 : W := mkw 0x086222a805619730 0x021888aa015865cc 0xfee73fb80de39f32 0xffb9cfee0378e7cc

def z814 : W := mkw 0x746fff76f0000001 0x1d1bffddbc000000 0x711ffffff0000000 0x9c47fffffc000000

def z815 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0xfb1fc7fffe03e3ff 0xfec7f1ffff80f8ff

def z816 : W := mkw 0x0c632b38c1611510 0x0318cace30584544 0xfee73fb8cde39c00 0xffb9cfee3378e700

def z817 : W := mkw 0x800000890fb483e8 0x6000002243ed20fa 0x800000000ffc03ff 0x2000000003ff00ff

def z818 : W := mkw 0x739cd4473a9e68c1 0xdce73511cea79a30 0x0118c047321c60c0 0x00463011cc871830

def z819 : W := mkw 0x67fa7e765ad93801 0x99fe9f9d96b64e00 0xd7f83fff0ffc1c00 0xf5fe0fffc3ff0700

def z820 : W := mkw 0x000000890fb643c0 0x4000002243ed90f0 0x880000000fffe3c0 0x2200000003fff8f0

def z821 : W := mkw 0x43b0066400000000 0x10ec019900000000 0xfff8c7fff20063ff 0xfffe31fffc8018ff

def z822 : W := mkw 0xd3b006ed2fb403c8 0x74ec01bb4bed00f2 0xd7f807ff3ffc03cd 0xf5fe01ffcfff00f3

def z823 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0x6ee73fb8cde39c32 0x5bb9cfee3378e70c

def z824 : W := mkw 0x800000890f06c7fc 0x2000002243c1b1ff 0x880000000e03e3ff 0x220000000380f8ff

def z825 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0xfff8c7ff0ffc63c0 0xfffe31ffc3ff18f0

def z826 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0xfffffffff2006000 0xfffffffffc801800

def z827 : W := mkw 0x0c210bb9c52487f0 0x430842ee714921fc 0x100007b8c00003f2 0x040001ee300000fc

def z828 : W := mkw 0x43b0066400000000 0x10ec019900000000 0x77f8c7fff0000000 0xddfe31fffc000000

def z829 : W := mkw 0xd3b486ed2fb6c3e8 0x74ed21bb4bedb0fa 0xdff8c7ff3fffe3ff 0xf7fe31ffcffff8ff

def z830 : W := mkw 0x04632b30c0000000 0x0118cacc30000000 0x77ff3fffc0000000 0xddffcffff0000000

def z831 : W := mkw 0x64fb7b36d0000001 0x193edecdb4000000 0x77fffffff0000000 0xddfffffffc000000

def z832 : W := mkw 0x73b4866420000001 0x1ced219908000000 0x57f807ff00000000 0xd5fe01ffc0000000

def z833 : W := mkw 0x046b7b32d0493800 0x011adeccb4124e00 0xfffffffffffffc00 0xffffffffffffff00

def z834 : W := mkw 0x77fff764a0000001 0x1dfffdd928000000 0x77ffffff00000000 0xddffffffc0000000

def z835 : W := mkw 0x13058549a10c2d54 0x04c1615268430b55 0xbb07c7c0f31c7fff 0xeec1f1f03cc71fff

def z836 : W := mkw 0x63fefe7650000000 0x18ffbf9d94000000 0x77fffffff0000000 0xddfffffffc000000

def z837 : W := mkw 0x23d6a81b5bd75554 0x88f5aa06d6f5d555 0x16e7007ffce383ff 0x45b9c01fff38e0ff

def z838 : W := mkw 0x0c210bbbd5248774 0x030842eef54921dd 0x100007bfc0000332 0x040001eff00000cc

def z839 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x36e7fffff0000000 0x4db9fffffc000000

def z840 : W := mkw 0x77bddf76fa9a6801 0x9def77ddbea69a00 0x1118c7fff21c6000 0x044631fffc871800

def z841 : W := mkw 0x77ffff76fadb7801 0x9dffffddbeb6de00 0x7ffffffff21ffc00 0xdffffffffc87ff00

def z842 : W := mkw 0x0042200000d93800 0x8010880000364e00 0xeee738000dff9c00 0xfbb9ce00037fe700

def z843 : W := mkw 0x0c632bb0c4619220 0x0318caec31186488 0xfee73fb8cde39c00 0xffb9cfee3378e700

def z844 : W := mkw 0x03085c5250000000 0x00c2171494000000 0x7318fffff0000000 0xdcc63ffffc000000

def z845 : W := mkw 0x0000008905b403c0 0x40000022416d00f0 0x0000000001fc03c0 0x00000000007f00f0

def z846 : W := mkw 0x0800008905659774 0x02000022415965dd 0x880000000de39fff 0x220000000378e7ff

def z847 : W := mkw 0x43b006ed0fb483e0 0x50ec01bb43ed20f8 0xdff807ff0fff83f2 0xf7fe01ffc3ffe0fc

def z848 : W := mkw 0xb04ff912f04bfc3c 0xac13fe44bc12ff0f 0x2807f800f003fc3f 0x0a01fe003c00ff0f

def z849 : W := mkw 0x27fffb32d0000000 0x09fffeccb4000000 0x77fffffff0000000 0xddfffffffc000000

def z850 : W := mkw 0x004a70000adb7800 0x80129c0002b6de00 0xeffff8000ffffc00 0xfbfffe0003ffff00

def z851 : W := mkw 0x08000089056dbf74 0x02000022415b6fdd 0x880000000dff9f32 0x22000000037fe7cc

def z852 : W := mkw 0x54210f76f0000001 0x150843ddbc000000 0x000007bf00000000 0x000001efc0000000

def z853 : W := mkw 0x63def4440adb7800 0x98f7bd1102b6de00 0xeffff8470ffffc00 0xfbfffe11c3ffff00

def z854 : W := mkw 0x40285e7650000000 0x100a179d94000000 0x7118fffff0000000 0x9c463ffffc000000

def z855 : W := mkw 0x77ffff76f0082c15 0x1dffffddbc020b05 0xfffffffff2007fff 0xfffffffffc801fff

def z856 : W := mkw 0x23d6a0000ad35000 0x88f5a80002b4d400 0xefff38000fff9c00 0xfbffce0003ffe700

def z857 : W := mkw 0x0008589b5fbc2fd4 0x40021626d7ef0bf5 0xa800f800fffc7fff 0x2a003e003fff1fff

def z858 : W := mkw 0x54295f76f0000001 0x150a57ddbc000000 0x50183ffff0000000 0x14060ffffc000000

def z859 : W := mkw 0x77ffff76f0411001 0x1dffffddbc104400 0x77fffffff1e01c00 0xddfffffffc780700

def z860 : W := mkw 0x344ff912f0493801 0x8d13fe44bc124e00 0x2007f800f0001c00 0x0801fe003c000700

def z861 : W := mkw 0x2fbddbb8cfbaef30 0x8bef76ee33eebbcc 0x1118c7b8c21c6332 0x044631ee308718cc

def z862 : W := mkw 0x77ffff76f0493801 0x1dffffddbc124e00 0xfffffffffffffc00 0xffffffffffffff00

def z863 : W := mkw 0x000000890fb403c0 0x4000002243ed00f0 0x000000000dfc0000 0x00000000037f0000

def z864 : W := mkw 0x73fef66630000001 0x1cffbd998c000000 0x77ffffff30000000 0xddffffffcc000000

def z865 : W := mkw 0x00000089052407d4 0x40000022414901f5 0x00000000000003ff 0x00000000000000ff

def z866 : W := mkw 0x039850890fbc2fd4 0x40e6142243ef0bf5 0xeff8f8000ffc7fff 0xfbfe3e0003ff1fff

def z867 : W := mkw 0x77f7a764aad35001 0x9dfde9d92ab4d400 0xd7ff07ff0fff8000 0xf5ffc1ffc3ffe000

def z868 : W := mkw 0x900dd99bff0eeffc 0x24037666ffc3bbff 0xa807f800ff1fffff 0x2a01fe003fc7ffff

def z869 : W := mkw 0x20da70890ffd3bc0 0xc8369c2243ff4ef0 0xc4f838000ffc1fc0 0x313e0e0003ff07f0

def z870 : W := mkw 0xd0b5832da1b6c168 0x742d60cb686db05a 0x6cffc03ff1ffe03f 0x1b3ff00ffc7ff80f

def z871 : W := mkw 0x54632f76f0000001 0x1518cbddbc000000 0x16e707fff0000000 0x45b9c1fffc000000

def z872 : W := mkw 0x039004c90f9403c0 0x00e4013243e500f0 0xd7f807ff0ffc03c0 0xf5fe01ffc3ff00f0

def z873 : W := mkw 0x4fd32d55cad594f0 0x53f4cb5572b5653c 0x291f3847c21f9cf2 0x0a47ce11f087e73c

def z874 : W := mkw 0x43b0066d0bb40140 0x50ec019b42ed0050 0xd7f807ff0ffc0000 0xf5fe01ffc3ff0000

def z875 : W := mkw 0xf3def4463adb7889 0xbcf7bd118eb6de22 0xeffff8473ffffccd 0xfbfffe11cfffff33

def z876 : W := mkw 0x57b58f76f0000001 0x15ed63ddbc000000 0x77ffc7fff0000000 0xddfff1fffc000000

def z877 : W := mkw 0x00000089052c2fd4 0x40000022414b0bf5 0x88000000031c7fff 0x2200000000c71fff

def z878 : W := mkw 0x43b0066400000000 0x10ec019900000000 0xd7f807ff031c0000 0xf5fe01ffc0c70000

def z879 : W := mkw 0x77b58f76f0000001 0x1ded63ddbc000000 0x100007fff0000000 0x040001fffc000000

def z880 : W := mkw 0x9f66ae786b635598 0x27d9ab9e1ad8d566 0x45e0f87833e07ccd 0x11783e1e0cf81f33

def z881 : W := mkw 0x54210f76f0000001 0x150843ddbc000000 0xb900c7fff20063ff 0xae4031fffc8018ff

def z882 : W := mkw 0x00000089052c2f54 0x00000022414b0bd5 0x880000000ffc7fff 0x2200000003ff1fff

def z883 : W := mkw 0x00085009010c2940 0x0002140240430a50 0xf918f87ff31c7fff 0xbe463e1ffcc71fff

def z884 : W := mkw 0x63fef664004b7800 0x98ffbd990012de00 0x7fffffff0003fc00 0xdfffffffc000ff00

def z885 : W := mkw 0x64fa7a3f51dd3d55 0x993e9e8fd4774f55 0x44f8383f01fc1c00 0x113e0e0fc07f0700

def z886 : W := mkw 0x43b006e40eb00280 0x50ec01b903ac00a0 0xd7f807ff0ffc0000 0xf5fe01ffc3ff0000

def z887 : W := mkw 0x204ef0000adb7800 0x8813bc0002b6de00 0xeee7f8000ffffc00 0xfbb9fe0003ffff00

def z888 : W := mkw 0x67fb7f76d0000001 0x19fedfddb4000000 0x77ff3fffc0000000 0xddffcffff0000000

def z889 : W := mkw 0x000000890fb403c0 0x4000002243ed00f0 0x880000000ffc63ff 0x2200000003ff18ff

def z890 : W := mkw 0x739cd4442a9a6801 0x9ce735110aa69a00 0x0118c000021c6000 0x0046300000871800

def z891 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0xfee73ff8fde39fff 0xffb9cffe3f78e7ff

def z892 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0xf7fffffffde00000 0xfdffffffff780000

def z893 : W := mkw 0x0c4b799bd56dbf74 0x0312de66f55b6fdd 0xa807f800ffffffff 0x2a01fe003fffffff

def z894 : W := mkw 0x4ff32f74c0419430 0x13fccbdd3010650c 0x7fff3fffc0039c32 0xdfffcffff000e70c

def z895 : W := mkw 0x74b95f76f0000001 0x1d2e57ddbc000000 0x101807fff0000000 0x040601fffc000000

def z896 : W := mkw 0x3c4ff912f049bc35 0x0f13fe44bc126f0d 0x2807f800f003fc3f 0x0a01fe003c00ff0f

def z897 : W := mkw 0x80000089052483e8 0x60000022414920fa 0x00000000000003ff 0x00000000000000ff

def z898 : W := mkw 0x9c210ffbf52487fc 0x270843fefd4921ff 0x100007fff00003ff 0x040001fffc0000ff

def z899 : W := mkw 0x880000890ff7d7f8 0x6200002243fdf5fe 0x880000000fffffff 0x2200000003ffffff

def z900 : W := mkw 0x54295f76f0082c15 0x150a57ddbc020b05 0x3800fffff0007c3f 0x0e003ffffc001f0f

def z901 : W := mkw 0xf7f7a7e4aed3d2a9 0xbdfde9f92bb4f4aa 0x06e707800ce38000 0x41b9c1e00338e000

def z902 : W := mkw 0x33def0023adb7801 0x8cf7bc008eb6de00 0xeffff8003ffffc00 0xfbfffe000fffff00

def z903 : W := mkw 0x53b4866420000000 0x14ed219908000000 0x57f8c7ff30000000 0xd5fe31ffcc000000

def z904 : W := mkw 0x43b0066400900000 0x10ec019900240000 0x57f807ff01fc0000 0xd5fe01ffc07f0000

def z905 : W := mkw 0x04632b38c1411510 0x0118cace30504544 0xfee73fb8cde39f32 0xffb9cfee3378e7cc

def z906 : W := mkw 0x7fffff76f0008431 0x1fffffddbc00210c 0x77fffffff0000032 0xddfffffffc00000c

def z907 : W := mkw 0x57b10f76f0000001 0x15ec43ddbc000000 0x111807fff0000000 0x044601fffc000000

def z908 : W := mkw 0x77ffff76fadb7801 0x9dffffddbeb6de00 0x77fffffffdff9c00 0xddffffffff7fe700

def z909 : W := mkw 0x44632b36d0000001 0x1118cacdb4000000 0x76e73fbfc0000000 0xddb9cfeff0000000

def z910 : W := mkw 0x0c6323a084619220 0x0318c8e821186488 0x46e73f800de39c00 0x51b9cfe00378e700

def z911 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0xeeff38000dff9c00 0xfbbfce00037fe700

def z912 : W := mkw 0xd39585c4ae02c2a8 0x34e561712b80b0aa 0xbb1fc7c7fe03e3ff 0xeec7f1f1ff80f8ff

def z913 : W := mkw 0x57210f76f0000001 0x15c843ddbc000000 0x130007fff0000000 0xc4c001fffc000000

def z914 : W := mkw 0xe4fa7ab65e02c2a9 0x393e9ead9780b0aa 0xccf8383f0e03e3ff 0x333e0e0fc380f8ff

def z915 : W := mkw 0x40b002ad0fb403c0 0x502c00ab43ed00f0 0xd6f807bf0ffc03c0 0xf5be01efc3ff00f0

def z916 : W := mkw 0x67ffff74cadb7800 0x99ffffdd32b6de00 0xffffffffcffffc00 0xfffffffff3ffff00

def z917 : W := mkw 0x43b4866400000000 0x10ed219900000000 0x77ffc7ff00000000 0xddfff1ffc0000000

def z918 : W := mkw 0x63fa766400000000 0x18fe9d9900000000 0x57f83fff00000000 0xd5fe0fffc0000000

def z919 : W := mkw 0xb3def4402adb7888 0xacf7bd100ab6de22 0xfffff840ffffffff 0xfffffe103fffffff

def z920 : W := mkw 0x73bdd766b0000001 0x1cef75d9ac000000 0x77ffc7fff0000000 0xddfff1fffc000000

def z921 : W := mkw 0x339cd4402a9a6800 0x8ce735100aa69a00 0x0118c040321c6000 0x004630100c871800

def z922 : W := mkw 0x54210f76f0000001 0x150843ddbc000000 0x70003ffff0000000 0x9c000ffffc000000

def z923 : W := mkw 0x23def0890fff7fd4 0xc8f7bc2243ffdff5 0xeffff8000fffffff 0xfbfffe0003ffffff

def z924 : W := mkw 0x44210f74c0000000 0x110843dd30000000 0x100007ffc0000000 0x040001fff0000000

def z925 : W := mkw 0xc3b486ed0fb6c3e8 0x70ed21bb43edb0fa 0xffffc7ff0fffe3ff 0xfffff1ffc3fff8ff

def z926 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x77fffffff00003ff 0xddfffffffc0000ff

def z927 : W := mkw 0x10095d52f0000000 0x04025754bc000000 0x7118fffff0000000 0x9c463ffffc000000

def z928 : W := mkw 0x47b10f74c0000000 0x11ec43dd30000000 0x57f807ffc0000000 0xd5fe01fff0000000

def z929 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0x2800f800f0007fff 0x0a003e003c001fff

def z930 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0x76e73fb8cde39c00 0xddb9cfee3378e700

def z931 : W := mkw 0x64fb7b36d0000001 0x193edecdb4000000 0x46ff3fbf00000000 0x51bfcfefc0000000

def z932 : W := mkw 0x60fa7a3f51fd3d54 0xd83e9e8fd47f4f55 0x44f8383f01fc1c00 0x113e0e0fc07f0700

def z933 : W := mkw 0x04632bb0c4419220 0x0118caec31106488 0xfee73fb8cde39f32 0xffb9cfee3378e7cc

def z934 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0xffff3fb8cfff9f32 0xffffcfee33ffe7cc

def z935 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0xfffff8400fffffc0 0xfffffe1003fffff0

def z936 : W := mkw 0x000850890fbc2bc0 0x4002142243ef0af0 0xe918f8000ffc7fc0 0xba463e0003ff1ff0

def z937 : W := mkw 0x43f2266400411000 0x10fc899900104400 0xffff3fff0de39c00 0xffffcfffc378e700

def z938 : W := mkw 0x0c6323a084619220 0x0318c8e821186488 0xfee73f80cde39f32 0xffb9cfe03378e7cc

def z939 : W := mkw 0x53b486ed2fb403c0 0x54ed21bb4bed00f0 0xd7f8c7ff3ffc03c0 0xf5fe31ffcfff00f0

def z940 : W := mkw 0x439004cd0fb403c0 0x50e4013343ed00f0 0x800000000ffc03c0 0x2000000003ff00f0

def z941 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0x3918f87ff21c7fff 0x0e463e1ffc871fff

def z942 : W := mkw 0x030581808e02c220 0x00c160602380b088 0xbb07c7c0fe03e3ff 0xeec1f1f03f80f8ff

def z943 : W := mkw 0x77fff764aadb7801 0x9dfffdd92ab6de00 0xffffffff0ffffc00 0xffffffffc3ffff00

def z944 : W := mkw 0x63fefe765adb7800 0x98ffbf9d96b6de00 0xfffffffffffffc00 0xffffffffffffff00

def z945 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0xffff07ff0fff83c0 0xffffc1ffc3ffe0f0

def z946 : W := mkw 0x080000890ffffff0 0xc200002243fffffc 0x880000000ffffff2 0x2200000003fffffc

def z947 : W := mkw 0x23d6a0000adb7800 0x88f5a80002b6de00 0xeee738000ffffc00 0xfbb9ce0003ffff00

def z948 : W := mkw 0x57b10f76fa900001 0x15ec43ddbea40000 0xd7f807fffffc0000 0xf5fe01ffffff0000

def z949 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0x17f807ff0efc03c0 0x45fe01ffc3bf00f0

def z950 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x17ffc7fff0000000 0x45fff1fffc000000

def z951 : W := mkw 0x0800008905248774 0x02000022414921dd 0x00000000000003ff 0x00000000000000ff

def z952 : W := mkw 0x43b0066d0b940140 0x10ec019b42e50050 0xd7f807ff0ffc03c0 0xf5fe01ffc3ff00f0

def z953 : W := mkw 0x080000890fb487f0 0x4200002243ed21fc 0x800000000ffc03f2 0x2000000003ff00fc

def z954 : W := mkw 0x930585c0aeb2c2a8 0x64c161702bacb0aa 0xbb07c7c0fee3e3ff 0xeec1f1f03fb8f8ff

def z955 : W := mkw 0x7fffff76f0411411 0x1fffffddbc104504 0x77fffffff0001c00 0xddfffffffc000700

def z956 : W := mkw 0x03b002a90fb40340 0x00ec00aa43ed00d0 0xd7f807ff0ffc03c0 0xf5fe01ffc3ff00f0

def z957 : W := mkw 0x20def00000db7800 0x8837bc000036de00 0xeefff8000dfffc00 0xfbbffe00037fff00

def z958 : W := mkw 0xb0db75c0a4d9baa8 0xac36dd7029366eaa 0x54f83fc0f1fc1fff 0x153e0ff03c7f07ff

def z959 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0xffe7c7c0ffe3e3ff 0xfff9f1f03ff8f8ff

def z960 : W := mkw 0xd4258f76f002c029 0x350963ddbc00b00a 0x3807c7fff003e03f 0x0e01f1fffc00f80f

def z961 : W := mkw 0x74ffff76f0000001 0x1d3fffddbc000000 0x74fffffff0000000 0x1d3ffffffc000000

def z962 : W := mkw 0xf7ffff76fadb7889 0xbdffffddbeb6de22 0xfffffffffffffccd 0xffffffffffffff33

def z963 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0xeffff800fffffc3f 0xfbfffe003fffff0f

def z964 : W := mkw 0x40b006ed05b403c0 0x502c01bb416d00f0 0x44f807bf01fc0000 0x113e01efc07f0000

def z965 : W := mkw 0x0042200000493800 0x0010880000124e00 0xeee738000ffffc00 0xfbb9ce0003ffff00

def z966 : W := mkw 0x47f22e7440000000 0x11fc8b9d10000000 0x57f83fff00000000 0xd5fe0fffc0000000

def z967 : W := mkw 0x77ffff76fa924001 0x9dffffddbea49000 0x77fffffff0000000 0xddfffffffc000000

def z968 : W := mkw 0x746fff76f0000001 0x1d1bffddbc000000 0x76e7fffff0000000 0xddb9fffffc000000

def z969 : W := mkw 0x77fb7f76f0000001 0x1dfedfddbc000000 0x57f83ffff0000000 0xd5fe0ffffc000000

def z970 : W := mkw 0x0c632bb0c4619630 0x0318caec3118658c 0xeee73f80cde39c32 0xfbb9cfe03378e70c

def z971 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0xc7f807bf0ffc0000 0xf1fe01efc3ff0000

def z972 : W := mkw 0x67f2266400000001 0x19fc899900000000 0x57f807ff00000000 0xd5fe01ffc0000000

def z973 : W := mkw 0x77ffff76fa9a6801 0x9dffffddbea69a00 0xfffffffffe1fe000 0xffffffffff87f800

def z974 : W := mkw 0x40b0022d01b40140 0x502c008b406d0050 0x56f807bf01fc0000 0xd5be01efc07f0000

def z975 : W := mkw 0x23def0021adb7800 0x88f7bc0086b6de00 0xeffff8473ffffc00 0xfbfffe11cfffff00

def z976 : W := mkw 0x0c632bb0c4619630 0x0318caec3118658c 0x7ee73fb8cce39c32 0xdfb9cfee3338e70c

def z977 : W := mkw 0x742ddf76f0000001 0x1d0b77ddbc000000 0x1000c7fff0000000 0x040031fffc000000

def z978 : W := mkw 0x77ffff76fadb7801 0x9dffffddbeb6de00 0x77fffffffeffe000 0xddffffffffbff800

def z979 : W := mkw 0x2c4ff912d04bfc34 0x8b13fe44b412ff0d 0x2807f800f003fc3f 0x0a01fe003c00ff0f

def z980 : W := mkw 0x030105c08e0082a0 0x00c04170238020a8 0xbb07c7c0fe03e3ff 0xeec1f1f03f80f8ff

def z981 : W := mkw 0x5767af76f0000001 0x15d9ebddbc000000 0x77e7fffff0000000 0xddf9fffffc000000

def z982 : W := mkw 0x03d220000adb7800 0x80f4880002b6de00 0xefff38000ffffc00 0xfbffce0003ffff00

def z983 : W := mkw 0xf7ffff76f04bf829 0xbdffffddbc12fe0a 0x7ffffffff003fc3f 0xdffffffffc00ff0f

def z984 : W := mkw 0x4ff32ffccff19730 0x13fccbff33fc65cc 0xffff3fffcfff9f32 0xffffcffff3ffe7cc

def z985 : W := mkw 0x20def0000adb7800 0x8837bc0002b6de00 0xecfff8000ffffc00 0x3b3ffe0003ffff00

def z986 : W := mkw 0x77ffff76f0900001 0x1dffffddbc240000 0x77fffffff1fc0000 0xddfffffffc7f0000

def z987 : W := mkw 0x7fffff76f0611001 0x1fffffddbc184400 0x77fffffff0e00000 0xddfffffffc380000

def z988 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0xaee7f8000ffffc00 0x6bb9fe0003ffff00

def z989 : W := mkw 0x239cd0890fbe6bc0 0xc8e7342243ef9af0 0x8118c0000ffc63c0 0x2046300003ff18f0

def z990 : W := mkw 0x080000890ff517d0 0x4200002243fd45f4 0x800000000ffc1fc0 0x2000000003ff07f0

def z991 : W := mkw 0x0020022000000000 0x0008008800000000 0x57f807ff00000000 0xd5fe01ffc0000000

def z992 : W := mkw 0x64fb7b36d0d93801 0x993edecdb4364e00 0xfeff3fbfcdff9c00 0xffbfcfeff37fe700

def z993 : W := mkw 0x67fffb36d0000001 0x19fffecdb4000000 0x77ffffbfc0000000 0xddffffeff0000000

def z994 : W := mkw 0x0c632bbbd5659774 0x0318caeef55965dd 0xffff3fffffff9fff 0xffffcfffffffe7ff

def z995 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x57ff3fff00000000 0xd5ffcfffc0000000

def z996 : W := mkw 0x546b7f76f0000001 0x151adfddbc000000 0x77fffffff0000000 0xddfffffffc000000

def z997 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x47ffffff30000000 0x51ffffffcc000000

def z998 : W := mkw 0x74fb7f76f0d93801 0x9d3edfddbc364e00 0x54f83ffff1fc1c00 0x153e0ffffc7f0700

def z999 : W := mkw 0x03da70000ad93800 0x00f69c0002b64e00 0xeffff8000ffffc00 0xfbfffe0003ffff00

def z1000 : W := mkw 0x77ffff76fad35001 0x9dffffddbeb4d400 0xf7ffffffffff8000 0xfdffffffffffe000

def z1001 : W := mkw 0x04210b32d0000000 0x010842ccb4000000 0x100007fff0000000 0x040001fffc000000

def z1002 : W := mkw 0x53b58764aa924000 0x14ed61d92aa49000 0xffffc7ffffffe000 0xfffff1fffffff800

def z1003 : W := mkw 0xf7ffff76f0008029 0x3dffffddbc00200a 0x77fffffff000003f 0xddfffffffc00000f

def z1004 : W := mkw 0x746b7f76f0000001 0x1d1adfddbc000000 0x10003ffff0000000 0x04000ffffc000000

def z1005 : W := mkw 0x54258f76f0000001 0x150963ddbc000000 0x3007c7fff0000000 0x0c01f1fffc000000

def z1006 : W := mkw 0x6cfa7a3f516d3d55 0x1b3e9e8fd45b4f55 0x44f8383f01fc1c00 0x113e0e0fc07f0700

def z1007 : W := mkw 0x77bddf76f0000001 0x1def77ddbc000000 0x7118fffff0000000 0x9c463ffffc000000

def z1008 : W := mkw 0x77ffff76fadb7801 0x9dffffddbeb6de00 0x46ff3fbf0dff9c00 0x51bfcfefc37fe700

def z1009 : W := mkw 0x63bcd6640a9a6800 0x98ef359902a69a00 0x57f8c7ff021c6000 0xd5fe31ffc0871800

def z1010 : W := mkw 0x40b0066d01b40140 0x502c019b406d0050 0x54f807ff01fc0000 0x153e01ffc07f0000

def z1011 : W := mkw 0x93058540a002c028 0x24c161502800b00a 0xbb07c7c0f203e3ff 0xeec1f1f03c80f8ff

def z1012 : W := mkw 0x77ffff76f0082801 0x1dffffddbc020a00 0x77fffffff11c1c00 0xddfffffffc470700

def z1013 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0xceff38000ffffc00 0x73bfce0003ffff00

def z1014 : W := mkw 0x04632bb8c5611300 0x0118caee315844c0 0xfee73fb8cde39f00 0xffb9cfee3378e7c0

def z1015 : W := mkw 0x23def0890fb403c0 0x48f7bc2243ed00f0 0xe7fff8000ffc03c0 0xf9fffe0003ff00f0

def z1016 : W := mkw 0x77f7af76f0000001 0x1dfdebddbc000000 0x37e7c7fff0000000 0xcdf9f1fffc000000

def z1017 : W := mkw 0x43b006ed05b403c0 0x50ec01bb416d00f0 0x57f807ff01fc03c0 0xd5fe01ffc07f00f0

def z1018 : W := mkw 0x40b0022400000000 0x102c008900000000 0x56f807bf00000000 0xd5be01efc0000000

def z1019 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0xfb07ffc0ff03ffff 0xfec1fff03fc0ffff

def z1020 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0xd7f807fffffc03ff 0xf5fe01ffffff00ff

def z1021 : W := mkw 0x53258764a0000000 0x14c961d928000000 0x3307c7fff0000000 0xccc1f1fffc000000

def z1022 : W := mkw 0x639cd4440a9a6800 0x98e7351102a69a00 0x0118c047021c6000 0x00463011c0871800

def z1023 : W := mkw 0x000000890fb403c0 0x4000002243ed00f0 0x910000400ffc03c0 0xa440001003ff00f0

def z1024 : W := mkw 0x77ffff76fadb7801 0x9dffffddbeb6de00 0xffffffffffffffff 0xffffffffffffffff

def z1025 : W := mkw 0x5c632f76f0419431 0x1718cbddbc10650c 0x38073ffff0039c32 0x0e01cffffc00e70c

def z1026 : W := mkw 0x54210f76f0000001 0x150843ddbc000000 0x511807fff0000000 0x944601fffc000000

def z1027 : W := mkw 0x000000890fb403c0 0x4000002243ed00f0 0x00000000021c03c0 0x00000000008700f0

def z1028 : W := mkw 0x0c432999cff597f0 0x4310ca6673fd65fc 0xa8073800cfff9ff2 0x2a01ce0033ffe7fc

def z1029 : W := mkw 0xa3def0000adb7888 0xa8f7bc0002b6de22 0xeffff8000ffffccd 0xfbfffe0003ffff33

def z1030 : W := mkw 0x20da70000adb7800 0x88369c0002b6de00 0xeeff38000ffffc00 0xfbbfce0003ffff00

def z1031 : W := mkw 0x0c6b7b32d049bc34 0x031adeccb4126f0d 0x7ffffffff003fc3f 0xdffffffffc00ff0f

def z1032 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0xfee73fb8cfe3ffff 0xffb9cfee33f8ffff

def z1033 : W := mkw 0x1c632bbaf5619731 0x0718caeebd5865cc 0xfee73fb8fde39f32 0xffb9cfee3f78e7cc

def z1034 : W := mkw 0x43b006640a900000 0x10ec019902a40000 0x57f807ff0ce00000 0xd5fe01ffc3380000

def z1035 : W := mkw 0xd3b486ed2fb643c8 0x74ed21bb4bed90f2 0xd7f807ff0ffc03c0 0xf5fe01ffc3ff00f0

def z1036 : W := mkw 0x43b006640a000080 0x10ec019902800020 0x57f807ff020000c0 0xd5fe01ffc0800030

def z1037 : W := mkw 0x43b85e765a982800 0x10ee179d96a60a00 0xfff8fffffffc7c00 0xfffe3fffffff1f00

def z1038 : W := mkw 0x57b10764a0000001 0x15ec41d928000000 0x57f807ff00000000 0xd5fe01ffc0000000

def z1039 : W := mkw 0x13058d52f0000000 0x04c16354bc000000 0x3307c7fff0000000 0xccc1f1fffc000000

def z1040 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0xaa07c780fe03e3ff 0x6a81f1e03f80f8ff

def z1041 : W := mkw 0x0000008905b40340 0x40000022416d00d0 0x800000000dfc0300 0x20000000037f00c0

def z1042 : W := mkw 0x606ef6ed056f7bc0 0xd81bbdbb415bdef0 0x3807ffff0003ffc0 0x0e01ffffc000fff0

def z1043 : W := mkw 0x43b00e7650000000 0x10ec039d94000000 0x57f807fff0000000 0xd5fe01fffc000000

def z1044 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0x3907c7c0f203e3ff 0x0e41f1f03c80f8ff

def z1045 : W := mkw 0x0c632bbad5619730 0x0318caeeb55865cc 0xfee73ffffde39f32 0xffb9cfffff78e7cc

def z1046 : W := mkw 0x57b10f76f0000001 0x15ec43ddbc000000 0x16e007fff0000000 0x45b801fffc000000

def z1047 : W := mkw 0x000000890ff753c0 0xc000002243fdd4f0 0x800000000fff83c0 0x2000000003ffe0f0

def z1048 : W := mkw 0x57258f76f0000001 0x15c963ddbc000000 0x120707fff0000000 0x4481c1fffc000000

def z1049 : W := mkw 0x77ffff76f0d93801 0x9dffffddbc364e00 0xfffffffffdff9c00 0xffffffffff7fe700

def z1050 : W := mkw 0x43b006e40e900280 0x10ec01b903a400a0 0xd7f807ff0ffc03c0 0xf5fe01ffc3ff00f0

def z1051 : W := mkw 0x0020022000000000 0x0008008800000000 0xd6e007b80de00000 0xf5b801ee03780000

def z1052 : W := mkw 0x44f32b34c0000000 0x113ccacd30000000 0x76ff3fbfc0000000 0xddbfcfeff0000000

def z1053 : W := mkw 0x000000890fb407d0 0x4000002243ed01f4 0x880000000ffc1ff2 0x2200000003ff07fc

def z1054 : W := mkw 0x344ff912f04b7c15 0x8d13fe44bc12df05 0x2807f800f003fc3f 0x0a01fe003c00ff0f

def z1055 : W := mkw 0x33dffd52f0000000 0x0cf7ff54bc000000 0x77fffffff0000000 0xddfffffffc000000

def z1056 : W := mkw 0x43b00e7440000000 0x10ec039d10000000 0x77f83fffc0000000 0xddfe0ffff0000000

def z1057 : W := mkw 0x77ffff76fad11001 0x1dffffddbeb44400 0xffffffffffff9c00 0xffffffffffffe700

def z1058 : W := mkw 0x43b006ec0fb00300 0x10ec01bb03ec00c0 0xd7f807ff0ffc0300 0xf5fe01ffc3ff00c0

def z1059 : W := mkw 0x73fef6663adb7801 0x9cffbd998eb6de00 0xffffffff3ffffc00 0xffffffffcfffff00

def z1060 : W := mkw 0x374ffd52f0000001 0x0dd3ff54bc000000 0x731ffffff0000000 0xdcc7fffffc000000

def z1061 : W := mkw 0x77ffff76fa900001 0x1dffffddbea40000 0x77fffffffce00000 0xddffffffff380000

def z1062 : W := mkw 0x77ffff76f0435001 0x9dffffddbc10d400 0x77fffffff0038000 0xddfffffffc00e000

def z1063 : W := mkw 0x77ffff76fad93801 0x9dffffddbeb64e00 0xf7fffffffffc1c00 0xfdffffffffff0700

def z1064 : W := mkw 0x40b006ed05b403c0 0x502c01bb416d00f0 0xd5f807ff03fc03c0 0xb57e01ffc0ff00f0

def z1065 : W := mkw 0x53b0066630000001 0x14ec01998c000000 0x57f807ff30000000 0xd5fe01ffcc000000

def z1066 : W := mkw 0x73fff764a0000000 0x1cfffdd928000000 0x77fffffff0000000 0xddfffffffc000000

def z1067 : W := mkw 0x0008581250082800 0x0002160494020a00 0xf918f87ff31c7fff 0xbe463e1ffcc71fff

def z1068 : W := mkw 0x800000890fb6c3e8 0x6000002243edb0fa 0x800000000fff83c0 0x2000000003ffe0f0

def z1069 : W := mkw 0x57258f76fa024001 0x15c963ddbe809000 0xbb07c7fffe03e000 0xeec1f1ffff80f800

def z1070 : W := mkw 0x43b006640adb7800 0x90ec019902b6de00 0xdff807ff0ffffc00 0xf7fe01ffc3ffff00

def z1071 : W := mkw 0x54210764a0000001 0x150841d928000000 0x100007ff00000000 0x040001ffc0000000

def z1072 : W := mkw 0x77ffff76f0082801 0x1dffffddbc020a00 0x77fffffff21c6000 0xddfffffffc871800

def z1073 : W := mkw 0x10010d52f0000000 0x04004354bc000000 0x100007fff0000000 0x040001fffc000000

def z1074 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0xfff8f87ffffc7fff 0xfffe3e1fffff1fff

def z1075 : W := mkw 0xa3def0890fdffffc 0xa8f7bc2243f7ffff 0xeffff8000fffffff 0xfbfffe0003ffffff

def z1076 : W := mkw 0x43b006ed05240340 0x10ec01bb414900d0 0xd7f807ff0ffc03c0 0xf5fe01ffc3ff00f0

def z1077 : W := mkw 0xb3def0002adb7808 0xacf7bc000ab6de02 0xeffff8003ffffc0d 0xfbfffe000fffff03

def z1078 : W := mkw 0xffffff76f043d439 0x3fffffddbc10f50e 0x7ffffffff003fc3f 0xdffffffffc00ff0f

def z1079 : W := mkw 0x0c432990c4419630 0x0310ca643110658c 0xfee73f80cde39f32 0xffb9cfe03378e7cc

def z1080 : W := mkw 0x4c632bbed5619731 0x1318caefb55865cc 0xfee73fbfcde39f32 0xffb9cfeff378e7cc

def z1081 : W := mkw 0x900585c0a402c2a8 0x240161702900b0aa 0xb907c7c0f203e3ff 0xae41f1f03c80f8ff

def z1082 : W := mkw 0x43b0066d0bb401c0 0x50ec019b42ed0070 0x57f807ff03fc00c0 0xd5fe01ffc0ff0030

def z1083 : W := mkw 0x00000089052403c0 0x40000022414900f0 0x800000000de003c0 0x20000000037800f0

def z1084 : W := mkw 0x43b486ed0fb643c0 0x50ed21bb43ed90f0 0xffffc7ffffffe3ff 0xfffff1fffffff8ff

def z1085 : W := mkw 0x800000890ffffbe8 0xe000002243fffefa 0x880000000fffffff 0x2200000003ffffff

def z1086 : W := mkw 0x43b006ed0fb643c0 0x50ec01bb43ed90f0 0xdff807ff0fffe3c0 0xf7fe01ffc3fff8f0

def z1087 : W := mkw 0x27fffb32dadb7800 0x89fffeccb6b6de00 0xfffffffffffffc00 0xffffffffffffff00

def z1088 : W := mkw 0x13058540a0000000 0x04c1615028000000 0x731fc7fff0000000 0xdcc7f1fffc000000

def z1089 : W := mkw 0x67fa7e7650000001 0x19fe9f9d94000000 0x77f8fffff0000000 0xddfe3ffffc000000

def z1090 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0xeffff8000fffffff 0xfbfffe0003ffffff

def z1091 : W := mkw 0x080000890ff593e0 0x4200002243fd64f8 0x800000000fff83c0 0x2000000003ffe0f0

def z1092 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0xf7fffffff31c0000 0xfdfffffffcc70000

def z1093 : W := mkw 0xd0210ffff52487fc 0x740843fffd4921ff 0x100007fff00003ff 0x040001fffc0000ff

def z1094 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0x5118f87ff31c7fff 0x14463e1ffcc71fff

def z1095 : W := mkw 0x00285a3250000000 0x000a168c94000000 0x77f8fffff0000000 0xddfe3ffffc000000

def z1096 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0x56e73fb8cde39f32 0x55b9cfee3378e7cc

def z1097 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0xc6f807bf0ffc03c0 0x71be01efc3ff00f0

def z1098 : W := mkw 0x0c4b7912d049bc34 0x0312de44b4126f0d 0x28073800c0039c32 0x0a01ce003000e70c

def z1099 : W := mkw 0x13058540aa024000 0x04c161502a809000 0xbb07c7c0fe03e3ff 0xeec1f1f03f80f8ff

def z1100 : W := mkw 0x800000890f06c3e8 0x2000002243c1b0fa 0x880000000f1fe3ff 0x2200000003c7f8ff

def z1101 : W := mkw 0x7fffff76fadbfc31 0x9fffffddbeb6ff0c 0xfffffffffffffc32 0xffffffffffffff0c

def z1102 : W := mkw 0xd4210f76f0008029 0x350843ddbc00200a 0x100007fff000003f 0x040001fffc00000f

def z1103 : W := mkw 0x5020066630000001 0x140801998c000000 0x100007ff30000000 0x040001ffcc000000

def z1104 : W := mkw 0x900585c0ae02c2a8 0x240161702b80b0aa 0xb807c7c0fe03e3ff 0x2e01f1f03f80f8ff

def z1105 : W := mkw 0x0000000000000000 0x0000000000000000 0xd118007f031c0000 0xb446001fc0c70000

def z1106 : W := mkw 0x77f7af76f0000001 0x1dfdebddbc000000 0x06e707bf00000000 0x41b9c1efc0000000

def z1107 : W := mkw 0x47f3276480000000 0x11fcc9d920000000 0x57ff07ff00000000 0xd5ffc1ffc0000000

def z1108 : W := mkw 0x000000890fb483e0 0x4000002243ed20f8 0x880000000fff83f2 0x2200000003ffe0fc

def z1109 : W := mkw 0xf39cd4463a9a6889 0xbce735118ea69a22 0x0118c047321c60cd 0x00463011cc871833

def z1110 : W := mkw 0x800101808e02c2a8 0x200040602380b0aa 0xbb07c7c0fe03e3ff 0xeec1f1f03f80f8ff

def z1111 : W := mkw 0x43b8566610000000 0x10ee159984000000 0x57f8c7ff30000000 0xd5fe31ffcc000000

def z1112 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x56ff3ffff0000000 0x55bfcffffc000000

def z1113 : W := mkw 0x739cd4473a9e6845 0x9ce73511cea79a11 0x0118c047321c60cd 0x00463011cc871833

def z1114 : W := mkw 0x40b006ed05b403c0 0x502c01bb416d00f0 0xd6f807ff0dfc03c0 0xf5be01ffc37f00f0

def z1115 : W := mkw 0x0000081941040550 0x0000020650410154 0xf918f87ff31c7fff 0xbe463e1ffcc71fff

def z1116 : W := mkw 0x43b0066400000000 0x10ec019900000000 0x46f807bf00000000 0x51be01efc0000000

def z1117 : W := mkw 0x77ffff76f0d11001 0x9dffffddbc344400 0x77fffffff0e00000 0xddfffffffc380000

def z1118 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0x67fff8000dff9c00 0xd9fffe00037fe700

def z1119 : W := mkw 0x0c6323a084619220 0x0318c8e821186488 0x2ee73f800ce39c00 0x4bb9cfe00338e700

def z1120 : W := mkw 0x77ffff76fa024001 0x1dffffddbe809000 0x77fffffffc038000 0xddffffffff00e000

def z1121 : W := mkw 0xdff7a7e4aef3d2a8 0x77fde9f92bbcf4aa 0x06e707800ce38000 0x41b9c1e00338e000

def z1122 : W := mkw 0x0042200000411000 0x0010880000104400 0xefff38000fff9c00 0xfbffce0003ffe700

def z1123 : W := mkw 0x746fff76f04b7801 0x9d1bffddbc12de00 0x3807fffff003fc00 0x0e01fffffc00ff00

def z1124 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0xdff807ff0ffc63ff 0xf7fe01ffc3ff18ff

def z1125 : W := mkw 0x57f7af74e0000000 0x15fdebdd38000000 0x77fffffff0000000 0xddfffffffc000000

def z1126 : W := mkw 0x239cd4400a9a6880 0x88e7351002a69a20 0x0118c040021c60c0 0x0046301000871830

def z1127 : W := mkw 0x176fff72f0000000 0x05dbffdcbc000000 0x77fffffff0000000 0xddfffffffc000000

def z1128 : W := mkw 0x000000890ff513c0 0x4000002243fd44f0 0x880000000fff9fc0 0x2200000003ffe7f0

def z1129 : W := mkw 0x0c622ab845611710 0x03188aae115845c4 0xfee73fb80de39f00 0xffb9cfee0378e7c0

def z1130 : W := mkw 0x80000089050487fc 0x20000022414121ff 0x00000000000003ff 0x00000000000000ff

def z1131 : W := mkw 0x77f7a764a0000001 0x1dfde9d928000000 0x77ffc7fff0000000 0xddfff1fffc000000

def z1132 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0x57f807ff0dfc0000 0xd5fe01ffc37f0000

def z1133 : W := mkw 0x63def4440adb7880 0xd8f7bd1102b6de20 0xeffff8000ffffc00 0xfbfffe0003ffff00

def z1134 : W := mkw 0x032006e90f2403c0 0x00c801ba43c900f0 0xd7f807ff0ffc03c0 0xf5fe01ffc3ff00f0

def z1135 : W := mkw 0x77ffff76f0082801 0x1dffffddbc020a00 0xfffffffff31c7fff 0xfffffffffcc71fff

def z1136 : W := mkw 0x130585c0a4008220 0x04c1617029002088 0xbb07c7c0fe03e3ff 0xeec1f1f03f80f8ff

def z1137 : W := mkw 0x939585c0ae92c2a8 0x24e561702ba4b0aa 0xbfe7c7c0fee3e3ff 0xeff9f1f03fb8f8ff

def z1138 : W := mkw 0x54632f76f0411001 0x1518cbddbc104400 0xfee73ffffde39c00 0xffb9cfffff78e700

def z1139 : W := mkw 0xdc210ffde52487f8 0x770843ff794921fe 0x100007fff00003ff 0x040001fffc0000ff

def z1140 : W := mkw 0x54210f76f0000001 0x150843ddbc000000 0x320707fff0000000 0xcc81c1fffc000000

def z1141 : W := mkw 0x77ffff76f0411001 0x1dffffddbc104400 0x7ffffffff0039c00 0xdffffffffc00e700

def z1142 : W := mkw 0xd3b58764a002c028 0x34ed61d92800b00a 0x7fffc7fff003e03f 0xdffff1fffc00f80f

def z1143 : W := mkw 0xb39cd4433a9e68cc 0xace73510cea79a33 0x0118c047321c60cd 0x00463011cc871833

def z1144 : W := mkw 0x2bdef0890fffff74 0x8af7bc2243ffffdd 0xeffff8000fffffff 0xfbfffe0003ffffff

def z1145 : W := mkw 0x43b006e50eb402c0 0x50ec01b943ad00b0 0x57f807ff0efc00c0 0xd5fe01ffc3bf0030

def z1146 : W := mkw 0x830cd0890f0eeffc 0x20c3342243c3bbff 0xeb1ff8000f1fffff 0xfac7fe0003c7ffff

def z1147 : W := mkw 0x90058180a402c2a8 0x240160602900b0aa 0x2807c000f003e3ff 0x0a01f0003c00f8ff

def z1148 : W := mkw 0x030004400a000000 0x00c0011002800000 0x930007c00e000000 0xe4c001f003800000

def z1149 : W := mkw 0x77ffff76f0493801 0x9dffffddbc124e00 0x77fffffff0001c00 0xddfffffffc000700

def z1150 : W := mkw 0x0c632bbad5619734 0x0318caeeb55865cd 0xfee73fb8fde39f3f 0xffb9cfee3f78e7cf

def z1151 : W := mkw 0x4c210bbdc5248770 0x530842ef714921dc 0x100007bfc0000332 0x040001eff00000cc

def z1152 : W := mkw 0x0c210bb9c5248770 0x030842ee714921dc 0x100007ffc00003f2 0x040001fff00000fc

def z1153 : W := mkw 0x43b0066d01b40140 0x50ec019b406d0050 0x46f807bf01fc0000 0x51be01efc07f0000

def z1154 : W := mkw 0x046b7b32d0000000 0x011adeccb4000000 0x76ff3fbfc0000000 0xddbfcfeff0000000

def z1155 : W := mkw 0xd3b486ed2fb643c8 0x74ed21bb4bed90f2 0xfff8c7fffffc63ff 0xfffe31ffffff18ff

def z1156 : W := mkw 0x54210f76f0000001 0x150843ddbc000000 0x100007fff00003ff 0x040001fffc0000ff

def z1157 : W := mkw 0x000000890fbc2fd4 0x4000002243ef0bf5 0x800000000ffc1fc0 0x2000000003ff07f0

def z1158 : W := mkw 0x006222a004611200 0x001888a801184480 0xeee73f800de39c00 0xfbb9cfe00378e700

def z1159 : W := mkw 0x000000890fb403c0 0x4000002243ed00f0 0xc6e000000ffc03c0 0xf1b8000003ff00f0

def z1160 : W := mkw 0x77ffff76f04b7801 0x9dffffddbc12de00 0xfffffffffde3fc00 0xffffffffff78ff00

def z1161 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0xeffff8403ffffccd 0xfbfffe100fffff33

def z1162 : W := mkw 0x930484c92fb643c8 0x64c121324bed90f2 0x8100c0403ffc63cd 0x204030100fff18f3

def z1163 : W := mkw 0x57b95f76f0000001 0x15ee57ddbc000000 0x77f8fffff0000000 0xddfe3ffffc000000

def z1164 : W := mkw 0x77f7af76f0000001 0x1dfdebddbc000000 0x76e73ffff0000000 0xddb9cffffc000000

def z1165 : W := mkw 0x4bb006ed0fb487f0 0x52ec01bb43ed21fc 0xd7f807ff0ffc03f2 0xf5fe01ffc3ff00fc

def z1166 : W := mkw 0x77ffff76fa435001 0x1dffffddbe90d400 0xffffffffffe3fc00 0xfffffffffff8ff00

def z1167 : W := mkw 0x77ffff76fa9a6801 0x9dffffddbea69a00 0xfffffffff31c7c00 0xfffffffffcc71f00

def z1168 : W := mkw 0x54210f76f0000001 0x150843ddbc000000 0x56e007fff0000000 0xd5b801fffc000000

def z1169 : W := mkw 0xc3b006ed0fb483e8 0x70ec01bb43ed20fa 0xd7f807ff0ffc03ff 0xf5fe01ffc3ff00ff

def z1170 : W := mkw 0x572ddf76f0000001 0x15cb77ddbc000000 0x731ffffff0000000 0xdcc7fffffc000000

def z1171 : W := mkw 0x23def00000493800 0x08f7bc0000124e00 0xeffff8000ffffc00 0xfbfffe0003ffff00

def z1172 : W := mkw 0x00000089050caf74 0x0000002241432bdd 0x880000000f1fffff 0x2200000003c7ffff

def z1173 : W := mkw 0x77ffff76fa900081 0x5dffffddbea40020 0x77fffffff0000000 0xddfffffffc000000

def z1174 : W := mkw 0x0c6323a885619320 0x0318c8ea215864c8 0xfee73fb80de39f00 0xffb9cfee0378e7c0

def z1175 : W := mkw 0x7fffff76f04bfc31 0x9fffffddbc12ff0c 0x7ffffffff003fc32 0xdffffffffc00ff0c

def z1176 : W := mkw 0x90058180ae02c2a8 0x240160602b80b0aa 0xba07c780fe03e3ff 0xee81f1e03f80f8ff

def z1177 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x77fffffff20060cd 0xddfffffffc801833

def z1178 : W := mkw 0x77ffff76f0b00001 0x5dffffddbc2c0000 0x77fffffff0e00000 0xddfffffffc380000

def z1179 : W := mkw 0x77ffff76f0008021 0x1dffffddbc002008 0x7ffffffff0038032 0xdffffffffc00e00c

def z1180 : W := mkw 0x73bcd6663a9a6801 0x9cef35998ea69a00 0xd7f8c7ff3ffc6000 0xf5fe31ffcfff1800

def z1181 : W := mkw 0x000000890f2403c0 0x4000002243c900f0 0x800000000e0003c0 0x20000000038000f0

def z1182 : W := mkw 0x23def4400adb7800 0x88f7bd1002b6de00 0xffffffc00ffffc00 0xfffffff003ffff00

def z1183 : W := mkw 0x002002a905240340 0x000800aa414900d0 0xd6f807bf0dfc0300 0xf5be01efc37f00c0

def z1184 : W := mkw 0x67fffb36dadb7801 0x99fffecdb6b6de00 0xffffffbfcffffc00 0xffffffeff3ffff00

def z1185 : W := mkw 0x880000890f6ffffc 0x2200002243dbffff 0x880000000fffffff 0x2200000003ffffff

def z1186 : W := mkw 0xf7ffff76fa024089 0x3dffffddbe809022 0x77fffffff0000000 0xddfffffffc000000

def z1187 : W := mkw 0x67fa7e7650000001 0x19fe9f9d94000000 0x46f83fbf00000000 0x51be0fefc0000000

def z1188 : W := mkw 0x800858925e02c2a8 0x200216249780b0aa 0xf918f87ffe03e3ff 0xbe463e1fff80f8ff

def z1189 : W := mkw 0x74fb7f76f0000001 0x1d3edfddbc000000 0x76ff3ffff0000000 0xddbfcffffc000000

def z1190 : W := mkw 0x77ffff76fa000001 0x1dffffddbe800000 0xf7fffffffe000000 0xfdffffffff800000

def z1191 : W := mkw 0xf7ffff76f002c029 0x3dffffddbc00b00a 0x77fffffff0038000 0xddfffffffc00e000

def z1192 : W := mkw 0x00210bb8c5208730 0x000842ee314821cc 0xfee73fb8cde39f32 0xffb9cfee3378e7cc

def z1193 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0xffe7fff8fde39f32 0xfff9fffe3f78e7cc

def z1194 : W := mkw 0xd3b587e4ae92c2a8 0x34ed61f92ba4b0aa 0xffffc7ffffffe3ff 0xfffff1fffffff8ff

def z1195 : W := mkw 0x40b0066400000000 0x102c019900000000 0x54f807ff00000000 0x153e01ffc0000000

def z1196 : W := mkw 0x04632b32d0000000 0x0118caccb4000000 0x76e73ffff0000000 0xddb9cffffc000000

def z1197 : W := mkw 0x5c210ffff5248775 0x170843fffd4921dd 0x100007fff00003ff 0x040001fffc0000ff

def z1198 : W := mkw 0x40b002ad05b40340 0x502c00ab416d00d0 0x54f807bf01fc0300 0x153e01efc07f00c0

def z1199 : W := mkw 0x57f32f76f0000001 0x15fccbddbc000000 0x77ff3ffff0000000 0xddffcffffc000000

def z1200 : W := mkw 0x43b002ad0fb40340 0x50ec00ab43ed00d0 0xd7f807bf0ffc0300 0xf5fe01efc3ff00c0

def z1201 : W := mkw 0x000000890fb407d4 0x4000002243ed01f5 0x800000000ffc03ff 0x2000000003ff00ff

def z1202 : W := mkw 0x77ffff76f0000415 0x1dffffddbc000105 0x77fffffff000003f 0xddfffffffc00000f

def z1203 : W := mkw 0x039000890fb403c0 0x40e4002243ed00f0 0x86e000000ffc03c0 0x61b8000003ff00f0

def z1204 : W := mkw 0x54295f76f0000001 0x150a57ddbc000000 0x3000fffff0000000 0x0c003ffffc000000

def z1205 : W := mkw 0x43b0066400000000 0x10ec019900000000 0x111807ff00000000 0x044601ffc0000000

def z1206 : W := mkw 0x009000890fb403c0 0x4024002243ed00f0 0xc4f800000ffc03c0 0x313e000003ff00f0

def z1207 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0xfb1fc7c0ff1fe3ff 0xfec7f1f03fc7f8ff

def z1208 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0xeee73fb80de39c00 0xfbb9cfee0378e700

def z1209 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x7ffffffff000603f 0xdffffffffc00180f

def z1210 : W := mkw 0xf7ffff76f0024009 0x3dffffddbc009002 0x77fffffff000600d 0xddfffffffc001803

def z1211 : W := mkw 0xb39585c0ae92c2a8 0xace561702ba4b0aa 0xbb07c7c0fe03e3ff 0xeec1f1f03f80f8ff

def z1212 : W := mkw 0x43b8566400000000 0x10ee159900000000 0x77f8ffff00000000 0xddfe3fffc0000000

def z1213 : W := mkw 0x67fefe7650000001 0x19ffbf9d94000000 0x77ffffff00000000 0xddffffffc0000000

def z1214 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0x47fff8000ffffc00 0x51fffe0003ffff00

def z1215 : W := mkw 0x77f7a764a0000001 0x1dfde9d928000000 0x46ff07bf00000000 0x51bfc1efc0000000

def z1216 : W := mkw 0x63f6a6640ad35000 0x98fda99902b4d400 0x57ff07ff0ce38000 0xd5ffc1ffc338e000

def z1217 : W := mkw 0x43b0066400000000 0x10ec019900000000 0xd7f807ff020003c0 0xf5fe01ffc08000f0

def z1218 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0x55f807ff03fc03c0 0x157e01ffc0ff00f0

def z1219 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0xd7f8c7ff3ffc63cd 0xf5fe31ffcfff18f3

def z1220 : W := mkw 0xd39cd4473a9e68cc 0x74e73511cea79a33 0x0118c047321c60cd 0x00463011cc871833

def z1221 : W := mkw 0x43b486ed0fb403c0 0x50ed21bb43ed00f0 0xf7ffc7ff0ffc03c0 0xfdfff1ffc3ff00f0

def z1222 : W := mkw 0x40b0022400900000 0x102c008900240000 0x44f8003f01fc0000 0x113e000fc07f0000

def z1223 : W := mkw 0x73b486ed2fb403c1 0x5ced21bb4bed00f0 0xd7f807ff0ffc03c0 0xf5fe01ffc3ff00f0

def z1224 : W := mkw 0x034ef0000a4b7800 0x00d3bc000292de00 0xeffff8000ffffc00 0xfbfffe0003ffff00

def z1225 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x67ffffbf00000000 0xd9ffffefc0000000

def z1226 : W := mkw 0x64fa7a3650000001 0x193e9e8d94000000 0x56f83fbf00000000 0xd5be0fefc0000000

def z1227 : W := mkw 0xf7ffff76f00aec3d 0x3dffffddbc02bb0f 0x7ffffffff003fc3f 0xdffffffffc00ff0f

def z1228 : W := mkw 0xf3f7a7e4aef3d2a8 0xfcfde9f92bbcf4aa 0x06e707800ce38000 0x41b9c1e00338e000

def z1229 : W := mkw 0x43b486640a024000 0x10ed219902809000 0xffffc7ff0e03e000 0xfffff1ffc380f800

def z1230 : W := mkw 0x000000890fff7fd4 0xc000002243ffdff5 0x880000000fffffff 0x2200000003ffffff

def z1231 : W := mkw 0x9c632bb8e5619738 0x2718caee395865ce 0xfee73fb8fde39f3f 0xffb9cfee3f78e7cf

def z1232 : W := mkw 0x77ffff76fa024001 0x1dffffddbe809000 0xfffffffffe03e3ff 0xffffffffff80f8ff

def z1233 : W := mkw 0x0c432998c5619730 0x0310ca66315865cc 0x28073800c0039f32 0x0a01ce003000e7cc

def z1234 : W := mkw 0x5c210f76f0008431 0x170843ddbc00210c 0x100007fff0000032 0x040001fffc00000c

def z1235 : W := mkw 0x0c632bb9c5659770 0x0318caee715965dc 0xfee73fffcde39ff2 0xffb9cffff378e7fc

def z1236 : W := mkw 0x43f2266400000000 0x10fc899900000000 0x77ff3fff00000000 0xddffcfffc0000000

def z1237 : W := mkw 0x77ffff76f0000411 0x1dffffddbc000104 0x7ffffffff0001c32 0xdffffffffc00070c

def z1238 : W := mkw 0xf7ffff76fa02c029 0x3dffffddbe80b00a 0xfffffffffe03e03f 0xffffffffff80f80f

def z1239 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0xf7fffffff20003c0 0xfdfffffffc8000f0

def z1240 : W := mkw 0x4320066400000000 0x10c8019900000000 0x130007ff00000000 0xc4c001ffc0000000

def z1241 : W := mkw 0x04295b32d0000000 0x010a56ccb4000000 0x7118fffff0000000 0x9c463ffffc000000

def z1242 : W := mkw 0x77ffff76f0db7801 0x9dffffddbc36de00 0x7ffffffff1fffc00 0xdffffffffc7fff00

def z1243 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0x56f807ff0dfc03c0 0x55be01ffc37f00f0

def z1244 : W := mkw 0xf7ffff76f002c029 0x3dffffddbc00b00a 0xfffffffff203e3ff 0xfffffffffc80f8ff

def z1245 : W := mkw 0x0008581b510c2d54 0x00021606d4430b55 0xfb1ff87fff1fffff 0xfec7fe1fffc7ffff

def z1246 : W := mkw 0x54b10f76f0000001 0x152c43ddbc000000 0x54f807fff0000000 0x153e01fffc000000

def z1247 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0xfffffffffc038000 0xffffffffff00e000

def z1248 : W := mkw 0x77ffff76f0411001 0x1dffffddbc104400 0x77fffffffce38000 0xddffffffff38e000

def z1249 : W := mkw 0x43b006640a900080 0x50ec019902a40020 0x57f807ff00000000 0xd5fe01ffc0000000

def z1250 : W := mkw 0x43b0066d01b40140 0x50ec019b406d0050 0xd7f807ff03fc03c0 0xf5fe01ffc0ff00f0

def z1251 : W := mkw 0x08000089052caf74 0x02000022414b2bdd 0x88000000031c7fff 0x2200000000c71fff

def z1252 : W := mkw 0x77ffff76f0982801 0x9dffffddbc260a00 0x77fffffff01c0000 0xddfffffffc070000

def z1253 : W := mkw 0x004220890ff513c0 0x4010882243fd44f0 0xeee738000fff9fc0 0xfbb9ce0003ffe7f0

def z1254 : W := mkw 0x77ffff76fadb7801 0x9dffffddbeb6de00 0x77fffffff3fc7c00 0xddfffffffcff1f00

def z1255 : W := mkw 0x54632f76f0000001 0x1518cbddbc000000 0x54e03ffff0000000 0x15380ffffc000000

def z1256 : W := mkw 0x73fff764aadb7800 0x9cfffdd92ab6de00 0xfffffffffffffc00 0xffffffffffffff00

def z1257 : W := mkw 0xf39585c4ae02c2a9 0x3ce561712b80b0aa 0xbb07c7c0fe03e3ff 0xeec1f1f03f80f8ff

def z1258 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0xfffffffff0000332 0xfffffffffc0000cc

def z1259 : W := mkw 0x77ffff76fa900001 0x1dffffddbea40000 0x77fffffff21c0000 0xddfffffffc870000

def z1260 : W := mkw 0x439004440a900000 0x10e4011102a40000 0x01180047021c0000 0x00460011c0870000

def z1261 : W := mkw 0xb3def4402adb7888 0xacf7bd100ab6de22 0xeffff8000ffffc00 0xfbfffe0003ffff00

def z1262 : W := mkw 0x4020066400000000 0x1008019900000000 0x511807ff00000000 0x944601ffc0000000

def z1263 : W := mkw 0x73bcd66630000001 0x1cef35998c000000 0x1118c7ff30000000 0x044631ffcc000000

def z1264 : W := mkw 0x0042208004411200 0x0010882001104480 0xfee73f800de39f00 0xffb9cfe00378e7c0

def z1265 : W := mkw 0x53b10764a0000000 0x14ec41d928000000 0x57f807fff0000000 0xd5fe01fffc000000

def z1266 : W := mkw 0xa3def0890ffffbe8 0xe8f7bc2243fffefa 0xeffff8000fffffff 0xfbfffe0003ffffff

def z1267 : W := mkw 0x43b006ed0fb407d0 0x50ec01bb43ed01f4 0xdff807ff0ffc1ff2 0xf7fe01ffc3ff07fc

def z1268 : W := mkw 0x4c632bbdc5659770 0x5318caef715965dc 0xfee73fbfcde39f32 0xffb9cfeff378e7cc

def z1269 : W := mkw 0x839480890fb6c3e8 0x60e5202243edb0fa 0xefffc0000fffe3ff 0xfbfff00003fff8ff

def z1270 : W := mkw 0x402006ed052403c0 0x500801bb414900f0 0xd7f807ff0ffc03c0 0xf5fe01ffc3ff00f0

def z1271 : W := mkw 0x77fefe7670000001 0x1dffbf9d9c000000 0x57f8ffff30000000 0xd5fe3fffcc000000

def z1272 : W := mkw 0x23def4400adb7880 0x88f7bd1002b6de20 0xeffff8400ffffcc0 0xfbfffe1003ffff30

def z1273 : W := mkw 0x43b1076480000000 0x10ec41d920000000 0x77ff07ffc0000000 0xddffc1fff0000000

def z1274 : W := mkw 0x639cd4440a9a6880 0xd8e7351102a69a20 0x0118c000021c6000 0x0046300000871800

def z1275 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0x1307c7c0fe03e3ff 0x44c1f1f03f80f8ff

def z1276 : W := mkw 0x77f7af76fad35001 0x9dfdebddbeb4d400 0x16e707fffce38000 0x45b9c1ffff38e000

def z1277 : W := mkw 0x63bcd66400000000 0x18ef359900000000 0x57f8c7ff00000000 0xd5fe31ffc0000000

def z1278 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0xaee73f80cde39f32 0x6bb9cfe03378e7cc

def z1279 : W := mkw 0x23def0021adb7804 0x88f7bc0086b6de01 0xeffff8003ffffc0d 0xfbfffe000fffff03

def z1280 : W := mkw 0x43b0066400000000 0x10ec019900000000 0x16e007ff00000000 0x45b801ffc0000000

def z1281 : W := mkw 0x33dffd52fadb7800 0x8cf7ff54beb6de00 0xfffffffffffffc00 0xffffffffffffff00

def z1282 : W := mkw 0x800000890f26c3e8 0x6000002243c9b0fa 0x880000000e03e3ff 0x220000000380f8ff

def z1283 : W := mkw 0x63b486ed0fb643c0 0xd8ed21bb43ed90f0 0xd7f807ff0ffc03c0 0xf5fe01ffc3ff00f0

def z1284 : W := mkw 0x43b0066400000000 0x10ec019900000000 0xd7f807ff0de00000 0xf5fe01ffc3780000

def z1285 : W := mkw 0xf7ffff76f0000089 0x3dffffddbc000022 0x77fffffff00000cd 0xddfffffffc000033

def z1286 : W := mkw 0x20da700000d93800 0x88369c0000364e00 0x46ff38000dff9c00 0x51bfce00037fe700

def z1287 : W := mkw 0x77bddf76f0000001 0x1def77ddbc000000 0x331fc7fff0000000 0xccc7f1fffc000000

def z1288 : W := mkw 0x77ffff76fa9a6801 0x9dffffddbea69a00 0xf7fffffffffc6000 0xfdffffffffff1800

def z1289 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0x3ee73fb8cce39f32 0x4fb9cfee3338e7cc

def z1290 : W := mkw 0x004a700000493800 0x00129c0000124e00 0xeeff38000dff9c00 0xfbbfce00037fe700

def z1291 : W := mkw 0x23def0000ad11000 0x08f7bc0002b44400 0xeffff8000fff9c00 0xfbfffe0003ffe700

def z1292 : W := mkw 0x43b006640a900000 0x10ec019902a40000 0x57f807ff021c0000 0xd5fe01ffc0870000

def z1293 : W := mkw 0x039cd0000a9a6800 0x00e7340002a69a00 0xeffff8000ffffc00 0xfbfffe0003ffff00

def z1294 : W := mkw 0xd4210f76f0000089 0x350843ddbc000022 0x100007fff00000cd 0x040001fffc000033

def z1295 : W := mkw 0x000000890fb403c0 0x4000002243ed00f0 0xc11800000ffc03c0 0xb046000003ff00f0

def z1296 : W := mkw 0x40b006ed0fb403c0 0x502c01bb43ed00f0 0xd4f807ff0ffc03c0 0x353e01ffc3ff00f0

def z1297 : W := mkw 0x939585c0ae02c2a8 0x24e561702b80b0aa 0xffffc7c0fe03e3ff 0xfffff1f03f80f8ff

def z1298 : W := mkw 0x006323a885619320 0x0018c8ea215864c8 0xfee73fb8cde39f32 0xffb9cfee3378e7cc

def z1299 : W := mkw 0x0800008905f59770 0x42000022417d65dc 0x880000000dff9f32 0x22000000037fe7cc

def z1300 : W := mkw 0x800000890fdffffc 0xa000002243f7ffff 0x880000000fffffff 0x2200000003ffffff

def z1301 : W := mkw 0x54632f76f0000001 0x1518cbddbc000000 0x30073ffff0000000 0x0c01cffffc000000

def z1302 : W := mkw 0x204ef0890fff7bc0 0xc813bc2243ffdef0 0xa807f8000fffffc0 0x2a01fe0003fffff0

def z1303 : W := mkw 0x63f6a66400000000 0x18fda99900000000 0x57ff07ff00000000 0xd5ffc1ffc0000000

def z1304 : W := mkw 0x930ddd52f00aec3c 0x24c37754bc02bb0f 0x7b1ffffff003fc3f 0xdec7fffffc00ff0f

def z1305 : W := mkw 0x77ffff76fa0a6801 0x1dffffddbe829a00 0xffffffffff1ffc00 0xffffffffffc7ff00

def z1306 : W := mkw 0x030004c90fb403c0 0x40c0013243ed00f0 0x810000400ffc03c0 0x2040001003ff00f0

def z1307 : W := mkw 0x47fb7f76d0000000 0x11fedfddb4000000 0x77fffffff0000000 0xddfffffffc000000

def z1308 : W := mkw 0x40b002ad0fb403c0 0x502c00ab43ed00f0 0x84e000000ffc03c0 0x2138000003ff00f0

def z1309 : W := mkw 0x000000890fb403c0 0x4000002243ed00f0 0x000000000ce003c0 0x00000000033800f0

def z1310 : W := mkw 0x43b006640a000000 0x10ec019902800000 0xd7f807ff0e000000 0xf5fe01ffc3800000

def z1311 : W := mkw 0x77ffff76fa000081 0x1dffffddbe800020 0x77fffffff20000c0 0xddfffffffc800030

def z1312 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0xffe7ffb8cfe3ff32 0xfff9ffee33f8ffcc

def z1313 : W := mkw 0x000000890f0403c0 0x0000002243c100f0 0x800000000f1c03c0 0x2000000003c700f0

def z1314 : W := mkw 0x44632f74c0000000 0x1118cbdd30000000 0x76e73fffc0000000 0xddb9cffff0000000

def z1315 : W := mkw 0x77ffff76fadb7801 0x9dffffddbeb6de00 0x7ffffffffce3fc00 0xdfffffffff38ff00

def z1316 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x66ffffbff0000000 0x59bfffeffc000000

def z1317 : W := mkw 0x77bddf76f0000001 0x1def77ddbc000000 0x57f8c7fff0000000 0xd5fe31fffc000000

def z1318 : W := mkw 0xf7ffff76fa024089 0x3dffffddbe809022 0xfffffffff20063ff 0xfffffffffc8018ff

def z1319 : W := mkw 0x33def4402adb7800 0x8cf7bd100ab6de00 0xeffff8403ffffc00 0xfbfffe100fffff00

def z1320 : W := mkw 0x0c632bb9c5659770 0x0318caee715965dc 0xffffffffffffffff 0xffffffffffffffff

def z1321 : W := mkw 0x43b0066400b00000 0x50ec0199002c0000 0x57f807ff00e00000 0xd5fe01ffc0380000

def z1322 : W := mkw 0x0c632bb0c4619630 0x0318caec3118658c 0xbee73f80cce39f32 0xefb9cfe03338e7cc

def z1323 : W := mkw 0x930585c0ae02c2a8 0x24c161702b80b0aa 0x3a07c7c0fc03e3ff 0x4e81f1f03f00f8ff

def z1324 : W := mkw 0x00622ab845611710 0x00188aae115845c4 0xfee73fb8cde39f32 0xffb9cfee3378e7cc

def z1325 : W := mkw 0x000000890fbe6bc0 0xc000002243ef9af0 0x800000000ffc63c0 0x2000000003ff18f0

def z1326 : W := mkw 0x2bdef0890ffffff0 0xcaf7bc2243fffffc 0xeffff8000ffffff2 0xfbfffe0003fffffc

def z1327 : W := mkw 0xf7ffff76fadbf829 0xbdffffddbeb6fe0a 0xfffffffffffffc3f 0xffffffffffffff0f

def z1328 : W := mkw 0x77ffff76fad35001 0x9dffffddbeb4d400 0xfffffffffde39c00 0xffffffffff78e700

def z1329 : W := mkw 0x0043218084419220 0x0010c86021106488 0xeee73f800de39c00 0xfbb9cfe00378e700

def z1330 : W := mkw 0x204ef000004b7800 0x8813bc000012de00 0xeffff8000ffffc00 0xfbfffe0003ffff00

def z1331 : W := mkw 0xc3b006ed0fb6c3e8 0x70ec01bb43edb0fa 0xd7f807ff0fff83c0 0xf5fe01ffc3ffe0f0

def z1332 : W := mkw 0x43b85e7650000000 0x10ee179d94000000 0x57f83fff00000000 0xd5fe0fffc0000000

def z1333 : W := mkw 0x00095912d0000000 0x00025644b4000000 0x731ffffff0000000 0xdcc7fffffc000000

def z1334 : W := mkw 0x77ffff76fa982801 0x1dffffddbea60a00 0xfffffffffffc7c00 0xffffffffffff1f00

def z1335 : W := mkw 0x77ffff76f04b7801 0x9dffffddbc12de00 0xfffffffff31ffc00 0xfffffffffcc7ff00

def z1336 : W := mkw 0xf39cd4452a9e68c8 0xfce735114aa79a32 0x0118c047321c60cd 0x00463011cc871833

def z1337 : W := mkw 0x77f7af76f0000001 0x1dfdebddbc000000 0x57ff07fff0000000 0xd5ffc1fffc000000

def z1338 : W := mkw 0x64fb7b36d0000001 0x193edecdb4000000 0x54f83fbfc0000000 0x153e0feff0000000

def z1339 : W := mkw 0x4020066400000000 0x1008019900000000 0x56e007ff00000000 0xd5b801ffc0000000

def z1340 : W := mkw 0x0346a0000adb7800 0x80d1a80002b6de00 0xefe7f8000ffffc00 0xfbf9fe0003ffff00

def z1341 : W := mkw 0x23def0000adb7800 0x88f7bc0002b6de00 0xc7ff38000fff9c00 0xf1ffce0003ffe700

def z1342 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0xcee73fb80de39f32 0x73b9cfee0378e7cc

def z1343 : W := mkw 0x74fffb36f0000001 0x1d3ffecdbc000000 0x76ffffbff0000000 0xddbfffeffc000000

def z1344 : W := mkw 0x0000008905240340 0x00000022414900d0 0x800000000ffc03c0 0x2000000003ff00f0

def z1345 : W := mkw 0x77f7af74e0000001 0x1dfdebdd38000000 0x77ff3fffc0000000 0xddffcffff0000000

def z1346 : W := mkw 0xd3b486ed2fb643c8 0x74ed21bb4bed90f2 0xffffc7ff3fffe3cd 0xfffff1ffcffff8f3

def z1347 : W := mkw 0x77ffff76fa924001 0x1dffffddbea49000 0xffffffffffffe000 0xfffffffffffff800

def z1348 : W := mkw 0x73bcde7670000001 0x1cef379d9c000000 0x77f8fffff0000000 0xddfe3ffffc000000

def z1349 : W := mkw 0x800000890fbeeffc 0x6000002243efbbff 0x880000000fffffff 0x2200000003ffffff

def z1350 : W := mkw 0x0c210bb9c5248774 0x030842ee714921dd 0x100007b8c00003ff 0x040001ee300000ff

def z1351 : W := mkw 0xc3b006ed0fb643c8 0x70ec01bb43ed90f2 0xd7f807ff0ffc63cd 0xf5fe01ffc3ff18f3

def z1352 : W := mkw 0x40b002ad05b40340 0x502c00ab416d00d0 0x46f807bf0dfc0000 0x51be01efc37f0000

def z1353 : W := mkw 0xd39585c4ae92c2a8 0x74e561712ba4b0aa 0xbb07c7c0fe03e3ff 0xeec1f1f03f80f8ff

def z1354 : W := mkw 0x23def00000d93800 0x88f7bc0000364e00 0xeffff8000dff9c00 0xfbfffe00037fe700

def z1355 : W := mkw 0x7fffff76f0419431 0x1fffffddbc10650c 0xfffffffffde39c32 0xffffffffff78e70c

def z1356 : W := mkw 0xf7ffff76fa02c0a9 0x3dffffddbe80b02a 0x7ffffffff203e0ff 0xdffffffffc80f83f

def z1357 : W := mkw 0x53b58764a0000000 0x14ed61d928000000 0x57ff07ff00000000 0xd5ffc1ffc0000000

def z1358 : W := mkw 0x900585c0a402c2a8 0x240161702900b0aa 0xba07c7c0fc03e3ff 0xee81f1f03f00f8ff

def z1359 : W := mkw 0x77ffff76fadb7c15 0x9dffffddbeb6df05 0xfffffffffffffc3f 0xffffffffffffff0f

def z1360 : W := mkw 0xc3b006ed0fb6c3e8 0x70ec01bb43edb0fa 0xfff8c7ffffffe3ff 0xfffe31fffffff8ff

def z1361 : W := mkw 0x43b006ed05b40340 0x50ec01bb416d00d0 0xd7f807ff0dfc0300 0xf5fe01ffc37f00c0

def z1362 : W := mkw 0x63def0061adb7801 0x98f7bc0186b6de00 0xeffff8070ffffc00 0xfbfffe01c3ffff00

def z1363 : W := mkw 0x74f32f76f0000001 0x1d3ccbddbc000000 0x14e007fff0000000 0x053801fffc000000

def z1364 : W := mkw 0x77ffff76f0000001 0x1dffffddbc000000 0x311ffffff0000000 0x0c47fffffc000000

def z1365 : W := mkw 0x084a7089056dbf74 0x02129c22415b6fdd 0xeffff8000fffffff 0xfbfffe0003ffffff

def z1366 : W := mkw 0x54295f76f0000001 0x150a57ddbc000000 0x1118c7fff0000000 0x044631fffc000000

def z1367 : W := mkw 0x77ffff76f0082805 0x1dffffddbc020a01 0x77fffffff000600d 0xddfffffffc001803

def z1368 : W := mkw 0x7467af76f0000001 0x1d19ebddbc000000 0x100707fff0000000 0x0401c1fffc000000

def z1369 : W := mkw 0x50210764a0000000 0x140841d928000000 0x100007fff0000000 0x040001fffc000000

def z1370 : W := mkw 0x776fff76f0000001 0x1ddbffddbc000000 0x3307fffff0000000 0xccc1fffffc000000

def z1371 : W := mkw 0x2cfa7a3b51fd3d54 0x8b3e9e8ed47f4f55 0x44f8383f01fc1c00 0x113e0e0fc07f0700

def z1372 : W := mkw 0x03d6a0000ad35000 0x00f5a80002b4d400 0xeffff8000ffffc00 0xfbfffe0003ffff00

def z1373 : W := mkw 0x67fefe765adb7801 0x99ffbf9d96b6de00 0xffffffff0ffffc00 0xffffffffc3ffff00

def z1374 : W := mkw 0x63fa766400d93800 0x98fe9d9900364e00 0x57f83fff01fc1c00 0xd5fe0fffc07f0700

def z1375 : W := mkw 0x030000890fb403c0 0x40c0002243ed00f0 0x830000000ffc03c0 0xe0c0000003ff00f0

def z1376 : W := mkw 0x030480890fb643c0 0x40c1202243ed90f0 0xab07c0000fffe3c0 0xeac1f00003fff8f0

def z1377 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0x47f807ff0ffc00c0 0x51fe01ffc3ff0030

def z1378 : W := mkw 0x0c632bb8c5619730 0x0318caee315865cc 0xffe73ff8cfe39ff2 0xfff9cffe33f8e7fc

def z1379 : W := mkw 0x77ffff76f0d93801 0x9dffffddbc364e00 0xfffffffff3fc7c00 0xfffffffffcff1f00

def z1380 : W := mkw 0x0463232080411000 0x0118c8c820104400 0xeee73f800de39c00 0xfbb9cfe00378e700

def z1381 : W := mkw 0x5c210ffff52487f1 0x570843fffd4921fc 0x100007fff00003f2 0x040001fffc0000fc

def z1382 : W := mkw 0x43b006ed0fb403c0 0x50ec01bb43ed00f0 0xfff807ffcffc03f2 0xfffe01fff3ff00fc

def z1383 : W := mkw 0x40200e7650000000 0x1008039d94000000 0x100007fff0000000 0x040001fffc000000

def z1384 : W := mkw 0x77f7a764a0000001 0x1dfde9d928000000 0x16e707ff00000000 0x45b9c1ffc0000000

def z1385 : W := mkw 0x43b8566400082800 0x10ee159900020a00 0xfff8ffff031c7c00 0xfffe3fffc0c71f00

def z1386 : W := mkw 0x67ffff74c0000000 0x19ffffdd30000000 0x77ffffffc0000000 0xddfffffff0000000

def z1387 : W := mkw 0x47b00e7650000001 0x11ec039d94000000 0x57f807ff00000000 0xd5fe01ffc0000000

def z1388 : W := mkw 0x0c632bb0c4619630 0x0318caec3118658c 0x06e73f800ce39c00 0x41b9cfe00338e700

def z1389 : W := mkw 0x43b85e7f5b9c2d54 0x10ee179fd6e70b55 0xfff8fffffffc7fff 0xfffe3fffffff1fff

def z1390 : W := mkw 0x77ffff76fadb7801 0x9dffffddbeb6de00 0xefffffbf0ffffc00 0xfbffffefc3ffff00

def z1391 : W := mkw 0x000000890f0c2fd4 0x0000002243c30bf5 0x880000000f1c7fff 0x2200000003c71fff

def z1392 : W := mkw 0x80000089050caffc 0x2000002241432bff 0x88000000031c7fff 0x2200000000c71fff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z7,z1,z2,z4,z8,z6]),(0,[z0,z9,z1,z10,z4,z5,z6]),(0,[z0,z1,z2,z4,z11,z5,z6]),(0,[z0,z1,z2,z12,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z13,z6]),(0,[z0,z14,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z15,z16,z6]),(0,[z0,z17,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z18]),(0,[z0,z1,z2,z4,z5,z6,z19])],[(0,[z20,z21,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z22,z5,z6]),(0,[z0,z23,z1,z2,z24,z5,z6])],[(0,[z7,z0,z1,z2,z4,z25,z6]),(0,[z0,z1,z2,z26,z4,z8,z6]),(0,[z0,z1,z2,z4,z27,z8,z6]),(0,[z0,z1,z2,z28,z26,z4,z6]),(0,[z0,z29,z1,z2,z4,z30,z6]),(0,[z31,z0,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z32,z26,z5,z6])],[(0,[z33,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z34,z4,z5,z6]),(0,[z0,z1,z2,z4,z35,z5,z6]),(0,[z0,z1,z2,z4,z36,z5,z6]),(0,[z0,z1,z2,z37,z4,z5,z6]),(0,[z0,z1,z2,z32,z4,z38,z6]),(0,[z0,z1,z2,z4,z15,z39,z6])],[(0,[z0,z1,z2,z4,z5,z40,z6]),(0,[z0,z41,z2,z4,z11,z5,z6]),(0,[z0,z42,z1,z2,z4,z5,z6]),(1,[z0,z43,z2,z4,z5,z44]),(0,[z0,z1,z2,z4,z45,z44,z6]),(0,[z0,z1,z2,z4,z15,z15,z6]),(0,[z0,z1,z2,z4,z15,z6,z46])],[],[(0,[z0,z47,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z48,z5,z6]),(0,[z0,z43,z1,z2,z4,z38,z6]),(1,[z0,z1,z2,z37,z4,z6])]],
   [[(0,[z0,z1,z2,z4,z49,z5,z6]),(0,[z50,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z51,z6]),(0,[z0,z29,z1,z2,z4,z52,z6]),(0,[z0,z53,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z38,z6,z46]),(0,[z0,z54,z1,z2,z4,z5,z6])],[(0,[z0,z55,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z56]),(0,[z0,z1,z2,z57,z4,z5,z6]),(0,[z0,z1,z2,z4,z58,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z59]),(0,[z0,z1,z2,z60,z4,z5,z6])],[(0,[z61,z0,z1,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z62,z6])],[(0,[z0,z1,z63,z4,z5,z6,z46]),(0,[z0,z1,z2,z4,z5,z8,z6]),(0,[z64,z65,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z66,z6]),(1,[z0,z1,z2,z67,z5,z6]),(1,[z0,z1,z68,z4,z38,z6]),(0,[z0,z1,z2,z2,z4,z15,z6])],[(0,[z0,z69,z1,z2,z4,z11,z6]),(0,[z0,z1,z2,z4,z5,z70,z6]),(0,[z71,z0,z1,z2,z26,z4,z6])],[(0,[z72,z0,z1,z2,z4,z5,z6]),(0,[z20,z0,z1,z73,z2,z4,z6]),(0,[z0,z1,z2,z4,z74,z5,z6]),(0,[z75,z0,z1,z2,z4,z5,z6]),(0,[z0,z23,z1,z2,z76,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z77])],[(0,[z0,z78,z1,z2,z4,z5,z6]),(0,[z79,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z80,z2,z4,z5,z6]),(0,[z0,z9,z1,z2,z4,z15,z6]),(0,[z0,z81,z1,z2,z4,z15,z6]),(1,[z0,z1,z2,z4,z15,z6]),(0,[z0,z1,z2,z4,z82,z6,z83])],[(0,[z84,z20,z0,z1,z2,z4,z6]),(0,[z0,z73,z2,z4,z5,z44,z6]),(0,[z0,z1,z2,z4,z5,z85,z6]),(0,[z0,z1,z2,z4,z5,z6,z86]),(0,[z0,z43,z1,z2,z4,z5,z87]),(0,[z0,z1,z2,z4,z5,z88,z6]),(0,[z0,z1,z89,z2,z26,z4,z6]),(0,[z0,z90,z1,z2,z4,z5,z83])]],
   [[(0,[z91,z0,z41,z2,z4,z5,z6]),(1,[z0,z1,z4,z74,z5,z6]),(0,[z0,z92,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z93]),(0,[z0,z1,z2,z76,z4,z5,z6]),(0,[z0,z1,z2,z4,z94,z5,z6])],[(0,[z0,z1,z2,z95,z4,z5,z6]),(1,[z0,z96,z2,z4,z5,z6]),(1,[z0,z1,z2,z97,z5,z6]),(0,[z0,z1,z4,z52,z74,z5,z6]),(0,[z98,z0,z1,z2,z4,z5,z6])],[(0,[z7,z0,z1,z2,z4,z99,z6]),(0,[z20,z0,z100,z1,z2,z4,z6]),(0,[z20,z0,z1,z2,z4,z16,z6]),(0,[z0,z1,z68,z2,z4,z15,z6]),(0,[z0,z1,z2,z4,z38,z101,z6]),(0,[z0,z1,z2,z4,z102,z5,z6]),(0,[z103,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z104,z6]),(0,[z0,z1,z2,z4,z5,z6,z105]),(0,[z0,z1,z2,z106,z4,z5,z6]),(0,[z0,z107,z1,z2,z4,z5,z6]),(0,[z0,z108,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z109]),(0,[z0,z110,z2,z4,z5,z30,z6]),(0,[z111,z0,z1,z2,z4,z15,z6]),(0,[z0,z1,z2,z112,z26,z4,z6]),(1,[z0,z1,z2,z4,z6,z113])],[(0,[z0,z1,z2,z114,z4,z5,z6]),(0,[z0,z9,z1,z4,z5,z6,z46]),(0,[z0,z1,z2,z26,z4,z115,z6])],[(0,[z116,z0,z1,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z15,z6]),(0,[z20,z0,z1,z2,z4,z6,z46]),(0,[z0,z1,z2,z4,z5,z117,z118]),(0,[z20,z0,z1,z2,z119,z5,z6])],[(0,[z0,z1,z120,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z121,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z122]),(0,[z123,z0,z1,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z124,z5,z6]),(0,[z0,z1,z2,z32,z4,z5,z83])]],
   [[(0,[z0,z1,z2,z125,z4,z5,z6]),(0,[z20,z0,z29,z1,z2,z4,z6]),(0,[z0,z1,z2,z126,z4,z5,z6]),(1,[z0,z2,z4,z127,z38,z6]),(0,[z0,z23,z1,z2,z26,z4,z6]),(0,[z0,z128,z1,z2,z26,z4,z6])],[(0,[z91,z0,z1,z2,z26,z4,z6]),(1,[z0,z47,z1,z2,z4,z6]),(0,[z129,z0,z100,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z130,z6]),(0,[z7,z0,z1,z2,z4,z38,z6]),(0,[z0,z1,z131,z2,z4,z5,z6]),(0,[z0,z132,z1,z2,z4,z5,z6])],[(0,[z133,z0,z1,z2,z4,z38,z6]),(0,[z0,z1,z2,z26,z4,z4,z6]),(0,[z20,z0,z1,z134,z2,z4,z6])],[(0,[z0,z1,z2,z63,z4,z38,z6]),(0,[z0,z1,z2,z135,z4,z5,z6]),(0,[z0,z136,z1,z2,z4,z15,z6]),(0,[z0,z1,z2,z4,z38,z6,z137]),(0,[z0,z90,z1,z2,z4,z15,z6])],[(0,[z0,z1,z138,z2,z4,z5,z6]),(0,[z0,z1,z139,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z140,z15,z6]),(0,[z0,z1,z2,z26,z4,z6,z141]),(0,[z20,z0,z142,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z143,z6]),(0,[z0,z1,z2,z4,z15,z144,z6]),(0,[z0,z1,z145,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z146,z4,z5,z6]),(0,[z21,z0,z1,z2,z4,z147,z6]),(0,[z0,z1,z2,z148,z4,z38,z6]),(0,[z0,z9,z1,z2,z4,z5,z6]),(0,[z0,z110,z1,z2,z4,z38,z6]),(0,[z0,z1,z2,z5,z44,z6,z149])],[(0,[z150,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z135,z4,z5,z6]),(0,[z0,z142,z1,z2,z11,z5,z6]),(0,[z0,z1,z2,z4,z16,z5,z6]),(0,[z151,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z152,z2,z4,z5,z6]),(0,[z0,z1,z153,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z8,z6]),(0,[z0,z1,z2,z4,z38,z144,z6]),(0,[z0,z1,z134,z2,z4,z38,z6])]],
   [[(0,[z154,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z155,z2,z4,z5,z6])],[(1,[z0,z156,z1,z2,z5,z6]),(0,[z65,z0,z1,z2,z4,z5,z141]),(0,[z0,z157,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z158,z6]),(0,[z0,z1,z159,z2,z4,z5,z6]),(0,[z0,z81,z1,z4,z16,z5,z6]),(0,[z0,z2,z4,z160,z16,z5,z6]),(0,[z0,z1,z68,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z161,z38,z6])],[(0,[z0,z162,z1,z2,z4,z5,z6]),(0,[z129,z0,z9,z1,z4,z5,z6]),(1,[z0,z1,z2,z163,z4,z6]),(0,[z0,z1,z2,z4,z164,z5,z6])],[(0,[z165,z0,z29,z1,z2,z4,z6]),(0,[z166,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z44,z6,z167]),(0,[z0,z1,z2,z32,z4,z15,z6]),(0,[z20,z0,z1,z2,z32,z4,z6])],[(0,[z0,z43,z120,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z141]),(0,[z168,z0,z1,z2,z4,z5,z6]),(0,[z0,z100,z1,z89,z4,z5,z6]),(0,[z0,z1,z169,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z170,z5,z6]),(0,[z0,z1,z171,z2,z4,z5,z6])],[(0,[z21,z0,z136,z1,z2,z5,z6]),(0,[z0,z1,z2,z172,z4,z5,z6]),(0,[z0,z1,z2,z4,z44,z6,z173]),(0,[z0,z1,z2,z174,z26,z4,z6]),(0,[z20,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z27,z5,z137])],[(0,[z0,z9,z2,z28,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z149])],[(0,[z0,z175,z1,z2,z4,z5,z6]),(0,[z150,z0,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z4,z15,z30,z6]),(1,[z0,z176,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z177,z6]),(0,[z0,z1,z178,z2,z4,z5,z6])],[(0,[z165,z7,z1,z2,z4,z5,z6]),(0,[z0,z179,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z180,z5,z6]),(0,[z0,z81,z1,z2,z4,z181,z6]),(0,[z0,z1,z2,z4,z24,z5,z6]),(0,[z20,z0,z1,z2,z4,z6,z137]),(0,[z0,z1,z2,z32,z5,z118,z6])],[(1,[z0,z162,z1,z2,z4,z6]),(0,[z0,z1,z2,z182,z4,z5,z6]),(0,[z21,z0,z1,z2,z148,z5,z6]),(0,[z0,z1,z73,z2,z4,z183,z6]),(0,[z0,z136,z1,z2,z4,z5,z6]),(0,[z0,z184,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z185,z6]),(0,[z0,z1,z186,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z140,z5,z6]),(0,[z65,z0,z1,z2,z4,z38,z6]),(0,[z0,z1,z2,z4,z187,z5,z6]),(0,[z0,z1,z2,z4,z5,z188,z6])],[(0,[z0,z1,z2,z189,z4,z5,z6]),(1,[z0,z78,z1,z2,z5,z6]),(0,[z0,z1,z190,z2,z4,z5,z6]),(0,[z0,z1,z2,z26,z4,z30,z6]),(0,[z0,z1,z2,z4,z15,z52,z6]),(0,[z0,z1,z2,z4,z191,z5,z6])],[(0,[z192,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z181,z6]),(0,[z0,z1,z10,z4,z16,z5,z6]),(0,[z0,z1,z193,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z144,z6]),(0,[z0,z1,z2,z4,z5,z194,z6])],[(1,[z0,z1,z2,z4,z195,z6]),(0,[z0,z1,z2,z26,z4,z6,z87])],[(0,[z0,z196,z1,z2,z4,z5,z6]),(0,[z21,z0,z1,z2,z140,z5,z6]),(1,[z0,z1,z2,z4,z197,z6]),(0,[z0,z1,z2,z198,z4,z5,z6]),(1,[z0,z1,z2,z4,z6,z173]),(0,[z0,z1,z2,z4,z199,z5,z6]),(0,[z0,z1,z200,z2,z4,z5,z6]),(0,[z201,z20,z0,z1,z2,z4,z6])]],
   [[(0,[z202,z0,z41,z2,z4,z5,z6]),(0,[z21,z0,z142,z1,z2,z5,z6]),(0,[z165,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z203,z5,z6]),(0,[z0,z1,z2,z4,z5,z204,z6]),(0,[z0,z1,z2,z4,z205,z5,z6]),(0,[z0,z206,z1,z2,z4,z5,z6])],[(0,[z207,z0,z1,z63,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z208,z6]),(0,[z7,z0,z1,z2,z4,z8,z6]),(0,[z0,z1,z2,z4,z209,z5,z6]),(0,[z0,z1,z2,z210,z4,z15,z6])],[(0,[z0,z211,z1,z2,z4,z5,z6]),(0,[z212,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z213,z5,z6]),(0,[z64,z0,z2,z4,z5,z6,z87]),(0,[z0,z1,z2,z4,z5,z214,z6])],[(0,[z0,z1,z2,z4,z5,z6,z215]),(0,[z0,z136,z2,z28,z4,z5,z6]),(0,[z0,z29,z1,z2,z4,z5,z6]),(0,[z0,z29,z2,z4,z52,z5,z6]),(0,[z0,z1,z2,z216,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z217])],[(0,[z207,z0,z55,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z30,z6]),(0,[z0,z1,z2,z4,z218,z5,z6]),(0,[z0,z219,z1,z2,z4,z15,z6])],[(0,[z0,z1,z89,z63,z4,z5,z6]),(0,[z220,z0,z1,z2,z4,z5,z6]),(0,[z0,z136,z1,z2,z5,z6,z83]),(0,[z0,z1,z2,z4,z5,z221,z6]),(0,[z0,z1,z2,z4,z222,z5,z6])],[(0,[z91,z0,z120,z2,z4,z5,z6]),(0,[z0,z1,z223,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z0,z1,z2,z4,z224,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z225]),(0,[z0,z9,z1,z73,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z87]),(1,[z0,z1,z2,z4,z226,z6])],[(0,[z7,z0,z110,z1,z2,z4,z6]),(0,[z0,z136,z1,z2,z11,z5,z6]),(0,[z0,z29,z1,z2,z4,z6,z137]),(0,[z0,z1,z2,z4,z5,z227,z6])]],
   [[(0,[z228,z0,z1,z2,z4,z5,z6]),(0,[z229,z0,z1,z2,z4,z5,z6]),(1,[z84,z1,z2,z140,z5,z6]),(0,[z0,z1,z2,z4,z230,z5,z6]),(0,[z0,z1,z200,z2,z26,z4,z6])],[(0,[z0,z1,z231,z2,z4,z38,z6]),(0,[z165,z0,z1,z2,z26,z4,z6]),(0,[z165,z20,z0,z1,z2,z4,z6]),(0,[z0,z1,z232,z2,z4,z5,z6]),(0,[z133,z0,z1,z2,z4,z15,z6]),(0,[z0,z233,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z115,z5,z6])],[(0,[z0,z1,z2,z4,z5,z234,z6]),(0,[z84,z21,z1,z2,z4,z5,z6]),(1,[z0,z110,z2,z4,z30,z6]),(0,[z0,z1,z235,z2,z26,z4,z6]),(0,[z0,z236,z1,z2,z4,z38,z6])],[(1,[z0,z237,z1,z2,z4,z6]),(0,[z0,z238,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z239,z5,z6])],[(0,[z240,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z241,z4,z5,z6]),(0,[z0,z1,z242,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z15,z62,z6]),(0,[z0,z1,z2,z4,z243,z5,z6]),(0,[z0,z110,z1,z2,z4,z15,z6]),(0,[z0,z29,z1,z2,z26,z4,z6]),(1,[z0,z1,z2,z4,z244,z6])],[(0,[z0,z1,z2,z4,z5,z6,z245]),(0,[z0,z29,z1,z2,z4,z27,z6]),(0,[z20,z0,z1,z2,z4,z52,z6]),(0,[z0,z246,z1,z2,z4,z5,z6]),(0,[z0,z237,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z26,z4,z247,z6]),(0,[z0,z1,z2,z4,z5,z82,z6]),(0,[z0,z1,z2,z32,z4,z5,z118])],[(0,[z0,z1,z2,z4,z5,z248,z6]),(0,[z0,z1,z2,z249,z4,z5,z6]),(0,[z0,z250,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z251,z4,z5,z6]),(0,[z0,z1,z134,z2,z4,z15,z6])],[(1,[z0,z252,z1,z4,z5,z6]),(0,[z0,z253,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z254,z5,z6]),(1,[z0,z1,z4,z243,z5,z6]),(0,[z0,z1,z2,z4,z255,z5,z6]),(0,[z0,z1,z2,z4,z5,z256,z6]),(0,[z257,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z258,z1,z2,z4,z5,z6]),(0,[z0,z259,z1,z2,z4,z5,z6]),(0,[z64,z0,z9,z2,z4,z5,z6]),(0,[z0,z1,z2,z210,z4,z5,z6]),(0,[z260,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z10,z4,z5,z6]),(0,[z261,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z262,z5,z6]),(0,[z0,z1,z2,z4,z15,z117,z6]),(1,[z20,z0,z1,z2,z119,z6])],[(0,[z0,z41,z1,z2,z4,z38,z6]),(0,[z263,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z264,z6,z141]),(0,[z0,z265,z2,z4,z5,z6,z46])],[(0,[z0,z266,z1,z2,z4,z5,z6]),(0,[z267,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z268,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z147,z6]),(0,[z21,z0,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z269,z4,z5,z6]),(0,[z0,z1,z2,z270,z4,z5,z6]),(0,[z0,z9,z1,z210,z4,z5,z6]),(0,[z0,z1,z2,z119,z32,z5,z6])],[(0,[z271,z0,z1,z2,z4,z5,z6]),(0,[z0,z9,z2,z4,z5,z44,z6]),(0,[z0,z100,z1,z10,z4,z5,z6]),(0,[z0,z110,z73,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z38,z117,z6]),(1,[z0,z1,z2,z4,z272,z6]),(0,[z273,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z274,z6]),(0,[z0,z142,z1,z2,z4,z15,z6]),(0,[z0,z81,z1,z2,z10,z5,z6]),(0,[z275,z0,z1,z2,z4,z15,z6]),(1,[z0,z1,z2,z26,z6,z83]),(1,[z0,z1,z2,z4,z276,z6])],[(0,[z0,z1,z2,z28,z4,z38,z6])],[(0,[z129,z0,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z277,z4,z5,z6]),(0,[z0,z1,z2,z4,z278,z5,z6])]],
   [[(1,[z0,z1,z2,z4,z279,z6]),(0,[z0,z9,z1,z2,z4,z279,z6]),(1,[z0,z1,z2,z4,z280,z6]),(0,[z0,z81,z1,z2,z16,z5,z6])],[(0,[z0,z281,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z25,z5,z6]),(0,[z0,z1,z2,z4,z5,z282,z6]),(0,[z0,z1,z2,z4,z5,z62,z6]),(0,[z0,z283,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z26,z4,z16,z6]),(0,[z284,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z10,z26,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z285])],[(0,[z286,z0,z1,z2,z4,z5,z6]),(0,[z0,z287,z1,z2,z4,z5,z6]),(0,[z288,z0,z1,z2,z4,z5,z6])],[(0,[z84,z0,z223,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z289,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z83]),(1,[z0,z1,z2,z290,z5,z6])],[(0,[z0,z1,z2,z4,z5,z291,z6]),(1,[z0,z292,z2,z4,z5,z6])],[(0,[z20,z202,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z26,z148,z4,z6]),(0,[z0,z1,z2,z4,z25,z6,z137]),(0,[z150,z0,z292,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z293,z5,z6]),(0,[z0,z142,z73,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z294,z6]),(0,[z0,z1,z2,z26,z4,z15,z6]),(0,[z0,z1,z2,z26,z4,z6,z46]),(0,[z271,z0,z1,z2,z26,z4,z6]),(0,[z271,z20,z0,z1,z2,z4,z6])],[(0,[z207,z0,z1,z2,z4,z38,z6]),(0,[z295,z0,z1,z2,z4,z140,z6]),(0,[z0,z2,z28,z4,z11,z5,z6]),(0,[z296,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z297,z5,z6]),(0,[z0,z1,z2,z119,z4,z38,z6]),(0,[z0,z1,z2,z4,z298,z15,z6]),(0,[z299,z0,z1,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z2,z5,z6,z149]),(0,[z0,z1,z2,z37,z26,z4,z6]),(0,[z33,z20,z0,z1,z2,z4,z6])],[(0,[z0,z47,z1,z120,z2,z4,z6]),(0,[z300,z0,z1,z2,z4,z5,z6]),(0,[z295,z0,z1,z2,z4,z5,z6]),(0,[z0,z81,z1,z2,z119,z5,z6])],[(0,[z0,z120,z73,z2,z4,z5,z6]),(0,[z84,z0,z1,z2,z4,z38,z6]),(0,[z21,z1,z2,z148,z4,z5,z6]),(0,[z0,z1,z2,z4,z8,z6,z137]),(0,[z0,z100,z1,z2,z4,z15,z6]),(0,[z0,z43,z1,z2,z4,z5,z44]),(0,[z0,z1,z301,z4,z5,z44,z6]),(0,[z0,z1,z89,z2,z4,z38,z6]),(0,[z0,z1,z2,z290,z4,z38,z6]),(0,[z20,z0,z1,z2,z4,z117,z6])],[(0,[z0,z1,z2,z4,z5,z302,z6]),(0,[z0,z1,z2,z4,z5,z303,z6]),(0,[z20,z0,z1,z68,z2,z4,z6]),(1,[z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z4,z304,z5,z6])],[(0,[z129,z1,z2,z63,z4,z5,z6]),(0,[z275,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z305,z4,z5,z6]),(0,[z0,z1,z2,z306,z4,z5,z6]),(0,[z0,z1,z2,z307,z4,z5,z6]),(0,[z0,z142,z1,z2,z4,z5,z6]),(0,[z0,z308,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z309,z5,z6]),(0,[z0,z1,z2,z4,z5,z310,z6]),(0,[z0,z1,z2,z311,z4,z5,z6]),(0,[z0,z1,z2,z312,z4,z5,z6]),(0,[z0,z313,z1,z2,z4,z5,z6])],[(0,[z0,z1,z73,z2,z4,z15,z6]),(0,[z0,z1,z2,z4,z5,z6,z46])],[(0,[z202,z0,z120,z2,z4,z5,z6]),(0,[z0,z1,z2,z314,z4,z5,z6]),(0,[z315,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z26,z4,z316,z6]),(1,[z0,z1,z2,z32,z26,z6]),(0,[z20,z0,z1,z145,z2,z4,z6]),(0,[z0,z317,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z318,z5,z6]),(0,[z0,z319,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z320]),(0,[z0,z1,z2,z4,z15,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z321,z6]),(0,[z0,z322,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z323,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z324]),(0,[z0,z100,z1,z4,z5,z6,z46]),(0,[z0,z1,z2,z4,z118,z6,z113]),(0,[z0,z1,z134,z2,z4,z5,z137])],[(0,[z0,z100,z73,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z38,z118,z6])],[(0,[z20,z0,z1,z2,z4,z25,z6]),(0,[z0,z1,z2,z4,z5,z6,z325]),(0,[z326,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z195,z5,z6]),(0,[z0,z23,z1,z2,z4,z38,z6]),(0,[z0,z1,z2,z4,z15,z6,z137]),(0,[z0,z1,z2,z4,z5,z6,z113])],[(0,[z91,z0,z1,z2,z4,z38,z6]),(0,[z0,z1,z2,z4,z244,z16,z6]),(0,[z0,z1,z2,z4,z38,z99,z6]),(1,[z0,z2,z4,z5,z6,z327]),(0,[z0,z1,z2,z26,z4,z5,z6]),(0,[z0,z328,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z27,z5,z6])],[(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z329,z5,z6]),(0,[z0,z1,z2,z32,z16,z5,z6]),(0,[z0,z1,z2,z4,z127,z5,z6]),(0,[z0,z1,z2,z330,z4,z5,z6]),(0,[z0,z1,z331,z2,z4,z5,z6])],[(0,[z0,z156,z1,z2,z4,z5,z6]),(0,[z0,z110,z1,z2,z4,z30,z6]),(1,[z0,z1,z2,z76,z5,z6]),(0,[z0,z1,z4,z5,z117,z6,z46]),(0,[z0,z1,z2,z4,z5,z316,z6])],[(0,[z332,z0,z1,z2,z4,z5,z6]),(0,[z207,z0,z1,z231,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z333,z6]),(0,[z0,z1,z96,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z101,z6]),(0,[z0,z334,z1,z2,z4,z5,z6]),(0,[z0,z142,z1,z2,z5,z6,z83]),(0,[z0,z1,z2,z106,z26,z4,z6])]],
   [[(0,[z0,z9,z41,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z335,z6]),(0,[z0,z9,z2,z4,z52,z5,z6]),(0,[z0,z81,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z26,z4,z6,z137]),(0,[z0,z1,z2,z4,z336,z5,z6]),(0,[z0,z337,z1,z2,z4,z5,z6])],[(0,[z0,z41,z1,z2,z4,z15,z6]),(0,[z150,z0,z1,z2,z4,z335,z6]),(0,[z150,z0,z1,z2,z4,z5,z62]),(0,[z0,z100,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z338,z4,z5,z6]),(0,[z0,z339,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z15,z27,z6]),(1,[z20,z0,z1,z2,z26,z6])],[(0,[z0,z340,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z341]),(0,[z0,z176,z1,z2,z4,z38,z6]),(0,[z0,z342,z1,z2,z4,z5,z6]),(0,[z0,z1,z343,z2,z4,z5,z6])],[(0,[z0,z1,z120,z2,z26,z4,z6])],[(0,[z344,z0,z1,z2,z4,z5,z6]),(0,[z0,z252,z1,z120,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z0,z1,z345,z2,z4,z5,z6]),(1,[z0,z1,z2,z163,z5,z6]),(0,[z0,z1,z2,z26,z4,z144,z6])],[(1,[z202,z41,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z140,z6]),(0,[z346,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z347,z5,z6])],[(1,[z0,z1,z2,z4,z348,z6]),(0,[z165,z0,z1,z2,z4,z25,z6]),(0,[z0,z1,z349,z2,z4,z5,z6]),(0,[z0,z1,z350,z2,z4,z5,z6]),(0,[z111,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z351,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z352])],[(0,[z150,z65,z1,z2,z4,z5,z6]),(0,[z0,z9,z100,z2,z4,z5,z6]),(0,[z0,z1,z353,z2,z4,z5,z6]),(0,[z354,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z26,z5,z6,z83]),(0,[z0,z1,z2,z355,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z356]),(0,[z0,z334,z1,z2,z26,z4,z6]),(1,[z0,z1,z2,z32,z5,z118]),(0,[z0,z1,z2,z4,z5,z6,z137])],[(0,[z0,z1,z357,z2,z4,z5,z6]),(0,[z0,z41,z73,z2,z4,z5,z6]),(0,[z20,z207,z0,z1,z2,z4,z6]),(0,[z0,z9,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z4,z358,z5,z6]),(0,[z0,z43,z1,z2,z4,z15,z6]),(0,[z0,z81,z1,z2,z26,z4,z6]),(0,[z0,z359,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z26,z4,z6]),(1,[z20,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z360,z6]),(0,[z1,z231,z2,z63,z4,z5,z6]),(0,[z150,z20,z0,z1,z2,z4,z6]),(0,[z0,z9,z110,z2,z4,z5,z6]),(0,[z0,z81,z1,z235,z4,z5,z6]),(0,[z0,z246,z2,z4,z16,z5,z6]),(0,[z0,z1,z2,z4,z16,z38,z6]),(0,[z20,z0,z1,z2,z4,z99,z6]),(0,[z361,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z362])],[(0,[z0,z1,z2,z4,z5,z363,z6]),(0,[z0,z1,z2,z140,z5,z6,z83]),(0,[z0,z1,z2,z4,z364,z5,z6]),(0,[z0,z342,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z365])],[(0,[z0,z1,z2,z4,z366,z5,z6]),(0,[z0,z162,z1,z120,z2,z4,z6]),(0,[z0,z1,z367,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z144,z6]),(0,[z20,z0,z1,z368,z2,z4,z6])],[(0,[z0,z136,z41,z2,z4,z5,z6]),(0,[z129,z0,z1,z63,z4,z5,z6]),(0,[z207,z0,z1,z2,z4,z15,z6]),(0,[z0,z369,z1,z2,z4,z5,z6]),(0,[z123,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z68,z2,z26,z4,z6]),(0,[z0,z90,z1,z2,z4,z5,z6])],[(0,[z91,z1,z120,z2,z4,z5,z6]),(0,[z0,z370,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z119,z4,z15,z6]),(0,[z0,z1,z89,z2,z4,z88,z6]),(0,[z346,z20,z0,z1,z2,z4,z6])],[(0,[z20,z0,z1,z120,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z371,z6]),(0,[z0,z1,z2,z4,z5,z6,z372]),(0,[z0,z1,z2,z4,z5,z373,z6]),(0,[z65,z1,z2,z4,z5,z62,z6]),(0,[z133,z0,z9,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z374,z6]),(0,[z0,z1,z2,z4,z244,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z375])]],
   [[(0,[z0,z1,z376,z120,z2,z4,z5]),(0,[z377,z0,z1,z2,z4,z5,z6]),(0,[z378,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z379,z4,z5,z6]),(0,[z84,z0,z1,z2,z4,z15,z6]),(0,[z20,z0,z1,z2,z26,z4,z6]),(0,[z0,z1,z380,z2,z4,z5,z6]),(0,[z20,z20,z0,z1,z2,z4,z6])],[(0,[z0,z1,z381,z2,z4,z6,z141]),(0,[z382,z0,z1,z2,z4,z5,z6]),(0,[z201,z0,z1,z2,z4,z38,z6]),(0,[z20,z0,z1,z2,z4,z27,z6])],[(0,[z0,z1,z2,z4,z38,z383,z6]),(1,[z0,z176,z2,z4,z38,z6])],[(0,[z0,z1,z376,z2,z4,z5,z6]),(0,[z150,z0,z1,z2,z4,z384,z6]),(0,[z0,z1,z2,z26,z4,z52,z6]),(0,[z0,z1,z385,z2,z4,z5,z6]),(0,[z0,z1,z386,z2,z4,z5,z6])],[(0,[z165,z0,z1,z2,z4,z99,z6]),(0,[z0,z1,z2,z4,z335,z5,z6]),(0,[z0,z1,z2,z4,z5,z387,z6]),(0,[z0,z1,z2,z4,z5,z388,z6]),(0,[z0,z1,z2,z4,z389,z15,z6]),(0,[z0,z1,z2,z32,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z390,z4,z5,z6]),(0,[z391,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z392]),(0,[z0,z136,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z173]),(0,[z0,z1,z2,z4,z393,z5,z6]),(0,[z0,z90,z1,z2,z26,z4,z6]),(0,[z0,z394,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z395,z4,z5,z6]),(0,[z0,z1,z2,z4,z396,z5,z6]),(1,[z0,z1,z2,z4,z22,z6]),(0,[z0,z81,z1,z2,z4,z22,z6]),(1,[z201,z0,z1,z2,z4,z6]),(0,[z0,z370,z1,z2,z26,z4,z6])]],
   [[(1,[z0,z1,z376,z2,z4,z5]),(0,[z84,z1,z2,z4,z140,z5,z6]),(0,[z0,z1,z2,z397,z4,z5,z6]),(0,[z0,z1,z2,z4,z38,z398,z6]),(0,[z0,z1,z2,z4,z5,z399,z6]),(0,[z0,z90,z1,z2,z5,z6,z83])],[(0,[z0,z1,z2,z4,z400,z5,z6]),(0,[z0,z1,z89,z2,z4,z5,z46])],[(0,[z401,z0,z1,z2,z4,z5,z6]),(0,[z402,z0,z1,z2,z4,z5,z6]),(0,[z0,z73,z2,z210,z4,z5,z6]),(0,[z0,z100,z1,z73,z4,z5,z6]),(0,[z0,z403,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z404,z6])],[(0,[z405,z0,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z2,z4,z15,z6]),(0,[z0,z406,z1,z2,z4,z5,z6]),(0,[z0,z1,z407,z2,z4,z5,z6])],[(0,[z202,z0,z1,z2,z4,z38,z6]),(0,[z64,z0,z1,z2,z4,z38,z6]),(0,[z0,z1,z235,z2,z26,z5,z6])],[(0,[z0,z1,z2,z63,z4,z15,z6]),(0,[z0,z1,z2,z4,z5,z408,z6]),(0,[z7,z0,z29,z1,z2,z4,z6]),(0,[z0,z1,z235,z2,z4,z38,z6])],[(0,[z0,z409,z1,z2,z4,z5,z6]),(0,[z0,z81,z100,z1,z4,z5,z6]),(1,[z0,z142,z2,z11,z5,z6]),(0,[z410,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z32,z26,z4,z6])],[(0,[z0,z1,z2,z148,z4,z15,z6]),(0,[z7,z0,z1,z134,z2,z4,z6]),(0,[z0,z29,z1,z2,z4,z38,z6]),(1,[z123,z0,z1,z2,z4,z6]),(0,[z0,z411,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z412,z1,z2,z4,z5,z6]),(1,[z0,z100,z73,z4,z5,z6]),(1,[z0,z413,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z52,z38,z6]),(0,[z0,z1,z2,z290,z5,z38,z6]),(0,[z0,z1,z414,z2,z4,z5,z6])],[(0,[z150,z0,z43,z1,z2,z4,z5]),(1,[z0,z1,z2,z4,z415,z6]),(0,[z0,z9,z1,z2,z4,z415,z6]),(1,[z0,z81,z1,z2,z26,z6]),(0,[z0,z1,z416,z2,z4,z15,z6]),(0,[z0,z417,z1,z2,z4,z5,z6])],[(0,[z0,z23,z1,z2,z4,z5,z46]),(0,[z0,z1,z418,z2,z4,z5,z6])],[(0,[z150,z64,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z419,z6]),(0,[z0,z1,z2,z4,z420,z5,z6]),(0,[z0,z1,z2,z4,z15,z421,z6]),(0,[z0,z422,z1,z2,z4,z5,z6])],[(0,[z20,z7,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z26,z4,z62,z6]),(0,[z0,z423,z1,z2,z4,z5,z6]),(0,[z64,z0,z1,z2,z4,z5,z44]),(0,[z64,z0,z1,z2,z4,z5,z87]),(0,[z0,z1,z2,z16,z5,z6,z83])],[(0,[z0,z1,z2,z4,z5,z6,z424]),(1,[z0,z1,z425,z4,z5,z6]),(1,[z0,z29,z2,z4,z52,z6]),(0,[z0,z1,z235,z2,z4,z393,z6]),(0,[z426,z0,z1,z2,z4,z5,z6]),(0,[z133,z0,z1,z4,z15,z5,z6])],[(0,[z0,z9,z120,z2,z4,z5,z6]),(0,[z21,z0,z1,z2,z4,z38,z6]),(0,[z150,z0,z1,z425,z4,z5,z6]),(0,[z0,z219,z1,z2,z4,z5,z6]),(0,[z427,z0,z1,z2,z4,z5,z6]),(0,[z201,z0,z1,z2,z10,z4,z6])],[(0,[z0,z100,z1,z210,z4,z5,z6]),(0,[z428,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z136,z1,z2,z28,z5,z6]),(0,[z0,z1,z2,z4,z38,z44,z6]),(0,[z0,z429,z1,z2,z4,z5,z6]),(0,[z0,z1,z430,z2,z4,z5,z6]),(0,[z431,z0,z1,z2,z4,z5,z6])],[(0,[z20,z0,z1,z2,z63,z4,z6]),(0,[z150,z1,z2,z4,z5,z6,z141]),(1,[z0,z1,z2,z4,z432,z6]),(0,[z0,z1,z433,z2,z4,z5,z6]),(0,[z0,z434,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z163,z4,z38,z6]),(0,[z0,z1,z2,z26,z4,z117,z6]),(0,[z0,z1,z2,z435,z4,z5,z6])],[(0,[z129,z0,z1,z2,z4,z38,z6]),(0,[z0,z1,z2,z4,z5,z147,z6]),(0,[z7,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z436,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z437]),(0,[z0,z1,z2,z4,z278,z118,z6])],[(1,[z0,z139,z2,z4,z5,z6]),(0,[z133,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z272,z6]),(1,[z0,z1,z2,z60,z5,z6])],[(0,[z0,z1,z2,z210,z26,z4,z6])],[(0,[z438,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z15,z25,z6]),(0,[z65,z0,z1,z2,z4,z15,z6]),(0,[z0,z439,z1,z2,z4,z5,z6]),(0,[z440,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z441,z5,z6])],[(0,[z0,z1,z2,z4,z5,z442,z6]),(0,[z0,z110,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z443]),(1,[z0,z265,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z197,z140,z6]),(0,[z0,z1,z444,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z445,z5,z6]),(0,[z0,z1,z2,z4,z5,z280,z6]),(0,[z0,z1,z2,z4,z11,z38,z6]),(0,[z0,z446,z1,z2,z4,z5,z6]),(0,[z0,z23,z1,z89,z4,z5,z6]),(0,[z427,z20,z0,z1,z2,z4,z6])]],
   [[(0,[z0,z1,z2,z447,z4,z5,z6]),(1,[z0,z9,z1,z4,z38,z6]),(0,[z0,z1,z2,z4,z160,z5,z6]),(0,[z0,z1,z134,z2,z4,z5,z6]),(0,[z0,z448,z1,z2,z4,z5,z6])],[(0,[z20,z0,z81,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z117,z6]),(0,[z0,z1,z2,z449,z4,z5,z6])],[(0,[z0,z1,z2,z4,z197,z5,z6]),(0,[z0,z1,z2,z4,z5,z450,z6]),(0,[z0,z1,z2,z4,z27,z25,z6]),(0,[z0,z110,z1,z2,z4,z6,z137]),(0,[z0,z1,z2,z451,z4,z5,z6]),(2,[z0,z1,z2,z163,z6])],[(0,[z0,z136,z120,z2,z4,z5,z6]),(0,[z452,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z243,z11,z5,z6])],[(0,[z20,z0,z1,z231,z2,z4,z6]),(0,[z0,z1,z2,z4,z45,z5,z6]),(0,[z133,z0,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z26,z4,z6,z453]),(0,[z0,z1,z134,z2,z4,z6,z137]),(1,[z0,z1,z2,z5,z6,z362])],[(0,[z0,z1,z2,z454,z4,z5,z6]),(0,[z0,z1,z2,z4,z25,z38,z6])],[(0,[z455,z0,z1,z2,z4,z5,z6]),(0,[z84,z0,z196,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z456,z5,z6]),(1,[z0,z9,z210,z4,z5,z6]),(0,[z0,z136,z1,z2,z4,z432,z6]),(0,[z20,z0,z1,z2,z4,z44,z6])],[(0,[z457,z0,z1,z2,z4,z5,z6]),(0,[z0,z110,z1,z2,z26,z4,z6]),(0,[z0,z1,z301,z2,z4,z5,z6]),(1,[z0,z1,z2,z290,z38,z6]),(0,[z0,z1,z2,z4,z247,z5,z6])]],
   [[(0,[z0,z1,z458,z2,z4,z5,z6]),(0,[z0,z1,z2,z459,z4,z5,z6])],[(0,[z460,z0,z1,z2,z4,z5,z6]),(0,[z461,z0,z1,z2,z4,z5,z6]),(0,[z462,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z134,z2,z26,z4,z6]),(0,[z0,z1,z2,z463,z4,z5,z6])],[(0,[z0,z78,z1,z120,z2,z5,z6]),(0,[z0,z1,z2,z4,z464,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z465]),(0,[z0,z1,z2,z4,z15,z118,z6]),(0,[z466,z0,z1,z2,z4,z5,z6])],[(0,[z202,z0,z1,z2,z4,z15,z6]),(0,[z0,z1,z231,z2,z4,z15,z6]),(0,[z21,z0,z1,z2,z4,z456,z6]),(0,[z0,z1,z2,z467,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z468,z6]),(0,[z64,z0,z1,z2,z4,z15,z6]),(1,[z0,z23,z1,z4,z5,z46]),(0,[z0,z1,z89,z2,z4,z102,z6]),(0,[z0,z1,z2,z469,z4,z5,z6]),(0,[z0,z470,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z471]),(0,[z0,z1,z2,z26,z4,z140,z6]),(0,[z65,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z15,z99,z6]),(0,[z0,z1,z2,z4,z5,z6,z453])],[(0,[z0,z1,z2,z4,z472,z5,z6]),(0,[z0,z142,z136,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z195,z11,z6]),(0,[z0,z1,z2,z4,z473,z5,z6]),(0,[z0,z1,z2,z4,z27,z5,z99])],[(0,[z0,z120,z2,z4,z5,z6,z87]),(0,[z0,z1,z2,z4,z5,z6,z474])],[(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z0,z1,z2,z475,z4,z5,z6]),(0,[z0,z1,z2,z5,z99,z6,z362])]],
   [[(0,[z0,z142,z1,z2,z26,z4,z6]),(0,[z0,z1,z476,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z118,z46]),(0,[z0,z1,z477,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z478,z6])],[(0,[z0,z1,z2,z4,z5,z479,z6]),(0,[z0,z1,z2,z4,z298,z5,z6]),(1,[z0,z1,z301,z4,z5,z6]),(0,[z0,z1,z2,z4,z27,z99,z6])],[(0,[z0,z1,z2,z480,z4,z5,z6]),(0,[z0,z1,z481,z2,z4,z5,z6]),(0,[z0,z1,z231,z2,z4,z130,z6]),(1,[z0,z81,z1,z16,z5,z6]),(0,[z0,z1,z2,z482,z4,z5,z6])],[(0,[z483,z0,z1,z120,z2,z4,z5]),(0,[z129,z0,z1,z2,z4,z484,z6]),(0,[z207,z0,z9,z1,z4,z5,z6]),(0,[z0,z485,z1,z2,z4,z5,z6]),(0,[z150,z0,z1,z2,z4,z5,z141]),(0,[z64,z0,z73,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z15,z38,z6]),(0,[z0,z1,z486,z2,z4,z15,z6]),(0,[z0,z487,z1,z2,z4,z5,z6])],[(0,[z488,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z489,z5,z6]),(0,[z0,z490,z1,z2,z4,z5,z6]),(0,[z0,z1,z491,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z492,z6]),(0,[z0,z81,z1,z2,z4,z5,z341]),(0,[z0,z1,z2,z493,z4,z5,z6]),(0,[z0,z494,z1,z2,z4,z5,z6]),(0,[z20,z0,z495,z1,z2,z4,z6]),(1,[z0,z1,z2,z463,z4,z6])],[(0,[z0,z1,z120,z2,z4,z38,z6]),(0,[z0,z1,z89,z231,z4,z5,z6]),(0,[z0,z1,z2,z496,z4,z5,z6]),(0,[z0,z142,z2,z4,z11,z5,z6]),(0,[z0,z110,z1,z2,z4,z52,z6]),(0,[z0,z1,z2,z4,z5,z6,z497]),(0,[z0,z1,z2,z4,z38,z6,z87]),(0,[z0,z498,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z38,z38,z6]),(1,[z0,z1,z4,z15,z38,z6]),(0,[z0,z1,z2,z4,z39,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z499])],[(0,[z483,z0,z1,z2,z4,z5,z6]),(1,[z295,z0,z1,z2,z4,z6]),(0,[z0,z1,z73,z2,z4,z5,z6]),(0,[z0,z142,z9,z2,z4,z5,z6]),(0,[z0,z500,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z37,z10,z4,z6])]],
   [[(0,[z501,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z32,z148,z5,z6]),(0,[z0,z502,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z28,z4,z15,z6]),(0,[z0,z1,z2,z503,z4,z5,z6]),(0,[z0,z1,z2,z26,z26,z4,z6])],[(1,[z0,z258,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z504,z6]),(1,[z65,z1,z2,z4,z5,z62]),(0,[z133,z0,z100,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z127,z38,z6]),(0,[z0,z1,z2,z2,z4,z38,z6]),(0,[z0,z1,z2,z4,z226,z5,z6]),(0,[z0,z1,z2,z26,z4,z27,z6])],[(0,[z0,z1,z2,z4,z5,z6,z505]),(0,[z20,z0,z1,z2,z4,z11,z6]),(0,[z0,z1,z2,z4,z506,z5,z6]),(0,[z0,z1,z2,z4,z15,z507,z6]),(0,[z0,z1,z2,z4,z5,z6,z327])],[(0,[z0,z120,z2,z4,z11,z5,z6]),(0,[z0,z1,z2,z4,z5,z508,z6]),(0,[z20,z0,z1,z2,z4,z118,z6]),(0,[z0,z1,z2,z4,z5,z6,z509]),(1,[z0,z1,z2,z4,z278,z6]),(1,[z0,z1,z2,z4,z27,z99])],[(0,[z0,z1,z2,z4,z5,z6,z510]),(0,[z0,z511,z1,z2,z4,z5,z6]),(0,[z0,z9,z1,z2,z4,z38,z6]),(0,[z512,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z513]),(1,[z0,z1,z2,z4,z38,z6]),(0,[z0,z514,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z32,z140,z5,z6]),(0,[z150,z0,z1,z2,z4,z38,z6]),(0,[z0,z100,z1,z2,z26,z4,z6]),(0,[z0,z136,z1,z2,z32,z5,z6]),(0,[z20,z0,z1,z2,z463,z4,z6])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z515,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z516]),(0,[z0,z1,z2,z517,z4,z5,z6]),(0,[z518,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z519,z6]),(0,[z0,z1,z2,z4,z11,z15,z6]),(0,[z0,z1,z2,z4,z5,z6,z520]),(0,[z0,z1,z2,z4,z5,z6,z167]),(1,[z0,z246,z2,z4,z5,z6]),(0,[z0,z1,z2,z521,z4,z5,z6])],[(0,[z0,z1,z2,z4,z522,z5,z6]),(0,[z523,z0,z1,z2,z4,z5,z6]),(0,[z0,z9,z2,z210,z4,z5,z6]),(0,[z0,z1,z2,z524,z4,z5,z6])]],
   [[(0,[z0,z525,z1,z2,z4,z5,z6]),(0,[z0,z526,z1,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z210,z4,z6]),(0,[z0,z1,z73,z2,z26,z4,z6]),(1,[z0,z1,z2,z4,z5,z527]),(0,[z0,z81,z1,z2,z4,z5,z527]),(0,[z0,z528,z1,z2,z4,z5,z6]),(0,[z529,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z68,z2,z4,z38,z6]),(0,[z0,z1,z2,z4,z5,z6,z530]),(0,[z0,z1,z531,z2,z4,z5,z6])],[(0,[z1,z2,z148,z4,z140,z5,z6]),(0,[z0,z1,z2,z97,z4,z5,z6]),(0,[z1,z2,z4,z5,z62,z6,z141]),(0,[z0,z1,z532,z2,z4,z5,z6]),(0,[z0,z1,z533,z2,z4,z5,z6]),(1,[z0,z1,z4,z5,z6,z167]),(0,[z0,z1,z2,z4,z38,z6,z83])],[(0,[z534,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z425,z2,z4,z5,z6]),(0,[z0,z142,z1,z2,z28,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z535]),(0,[z0,z1,z2,z4,z38,z6,z536])],[(0,[z0,z41,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z537,z4,z5,z6]),(0,[z0,z1,z538,z2,z4,z5,z6]),(1,[z150,z1,z2,z4,z5,z141]),(1,[z0,z1,z2,z4,z264,z6]),(0,[z0,z9,z1,z4,z5,z38,z6]),(0,[z0,z539,z1,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z26,z5,z6]),(1,[z0,z1,z2,z26,z144,z6])],[(1,[z165,z1,z2,z4,z25,z6]),(0,[z0,z540,z1,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z6,z87]),(0,[z0,z1,z235,z2,z4,z185,z6]),(0,[z20,z0,z1,z2,z4,z38,z6]),(0,[z0,z1,z89,z2,z4,z15,z6]),(0,[z0,z1,z2,z4,z5,z6,z541])],[(0,[z0,z292,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z542,z6]),(0,[z0,z1,z2,z4,z5,z6,z543]),(0,[z0,z1,z2,z544,z4,z5,z6])],[(0,[z0,z545,z1,z2,z4,z5,z6]),(0,[z0,z546,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z384,z6]),(0,[z547,z0,z1,z2,z4,z5,z6])],[(0,[z0,z548,z1,z2,z4,z5,z6]),(0,[z0,z1,z549,z2,z4,z5,z6]),(0,[z0,z1,z2,z28,z4,z5,z6]),(0,[z0,z413,z1,z4,z52,z5,z6]),(0,[z0,z1,z2,z163,z5,z38,z6]),(0,[z20,z0,z1,z89,z2,z4,z6])]],
   [[(0,[z0,z1,z2,z550,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z551])],[(0,[z0,z552,z1,z2,z4,z5,z6]),(0,[z0,z553,z1,z2,z4,z5,z6]),(0,[z0,z554,z1,z2,z4,z5,z6]),(0,[z0,z136,z1,z2,z4,z38,z6]),(0,[z0,z1,z186,z2,z4,z38,z6]),(0,[z0,z1,z2,z4,z507,z5,z6]),(0,[z0,z495,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z555,z4,z5,z6]),(0,[z0,z1,z2,z4,z556,z5,z6])],[(0,[z0,z1,z2,z4,z140,z38,z6]),(0,[z0,z1,z2,z4,z5,z384,z6]),(0,[z0,z9,z81,z1,z4,z5,z6]),(0,[z557,z0,z1,z2,z4,z5,z6])],[(0,[z0,z43,z41,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z15,z8,z6]),(0,[z0,z43,z1,z2,z4,z5,z6]),(0,[z558,z0,z1,z2,z4,z5,z6])],[(0,[z0,z559,z1,z2,z4,z5,z6]),(0,[z0,z41,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z4,z484,z5,z6]),(0,[z0,z1,z2,z4,z348,z5,z6]),(0,[z560,z0,z1,z2,z4,z5,z6]),(0,[z20,z0,z23,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z561,z5,z6])],[(0,[z0,z1,z2,z4,z562,z5,z6]),(0,[z0,z23,z1,z2,z4,z15,z6])],[(0,[z91,z0,z1,z2,z4,z15,z6]),(0,[z0,z1,z2,z4,z38,z8,z6]),(0,[z0,z1,z2,z4,z5,z6,z563]),(0,[z0,z1,z89,z2,z4,z5,z117]),(0,[z0,z1,z2,z5,z118,z6,z83]),(0,[z0,z1,z2,z4,z276,z6,z83])],[(0,[z207,z0,z1,z2,z4,z5,z6]),(0,[z165,z0,z1,z2,z4,z38,z6]),(0,[z564,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z52,z5,z30,z6]),(0,[z20,z0,z1,z2,z4,z6,z83]),(0,[z0,z565,z1,z2,z4,z5,z6]),(1,[z0,z90,z1,z2,z5,z83]),(0,[z0,z1,z2,z60,z5,z99,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z383,z6]),(0,[z566,z0,z1,z2,z4,z5,z6]),(0,[z71,z0,z1,z2,z4,z5,z6]),(0,[z165,z1,z2,z4,z25,z5,z6]),(0,[z0,z1,z2,z4,z183,z5,z6]),(0,[z0,z1,z2,z567,z4,z5,z6]),(0,[z0,z1,z2,z119,z4,z5,z6])],[(1,[z0,z1,z2,z4,z456,z6]),(0,[z568,z0,z1,z2,z4,z5,z6]),(0,[z569,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z368,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z570,z6]),(0,[z20,z547,z0,z1,z2,z4,z6]),(0,[z20,z0,z1,z2,z4,z6,z18])],[(0,[z84,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z571,z6]),(0,[z0,z1,z2,z10,z32,z5,z6]),(0,[z0,z1,z2,z4,z218,z38,z6]),(0,[z0,z1,z2,z290,z4,z5,z6]),(0,[z0,z1,z89,z2,z4,z5,z6]),(0,[z0,z1,z572,z2,z4,z5,z6])],[(0,[z41,z1,z120,z2,z4,z5,z6]),(0,[z573,z0,z1,z2,z4,z5,z6]),(0,[z20,z129,z0,z1,z2,z4,z6]),(1,[z0,z136,z2,z28,z5,z6]),(1,[z64,z0,z2,z4,z5,z87]),(0,[z0,z43,z1,z2,z26,z4,z6]),(1,[z133,z0,z1,z4,z15,z6]),(0,[z0,z23,z1,z4,z5,z6,z46]),(0,[z0,z1,z2,z574,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z575,z6])],[(0,[z0,z1,z120,z2,z4,z15,z6]),(0,[z576,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z484,z6]),(0,[z0,z1,z2,z4,z5,z577,z6]),(0,[z0,z578,z1,z2,z4,z5,z6]),(0,[z579,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z580,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z398,z6]),(0,[z581,z0,z1,z2,z4,z5,z6])],[],[(0,[z0,z582,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z583,z5,z6]),(1,[z21,z1,z2,z148,z5,z6]),(0,[z0,z1,z2,z4,z389,z5,z6]),(0,[z0,z23,z1,z2,z4,z5,z117]),(0,[z0,z1,z2,z26,z4,z164,z6]),(0,[z0,z1,z584,z2,z4,z5,z6])]],
   [[(0,[z20,z0,z41,z1,z2,z4,z6]),(1,[z129,z1,z63,z4,z5,z6]),(0,[z207,z0,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z4,z5,z415,z6]),(0,[z0,z1,z2,z4,z15,z44,z6]),(0,[z20,z0,z1,z2,z10,z4,z6]),(1,[z0,z1,z2,z4,z88,z6]),(0,[z0,z1,z2,z112,z4,z5,z6])],[(0,[z0,z1,z2,z119,z26,z4,z6])],[(1,[z0,z100,z1,z4,z38,z6]),(0,[z0,z69,z1,z2,z4,z5,z6]),(0,[z585,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z586,z5,z6])],[(0,[z0,z1,z587,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z588,z5,z6]),(1,[z0,z1,z2,z4,z164,z6]),(0,[z0,z1,z2,z119,z5,z6,z83])],[(0,[z84,z0,z1,z2,z26,z4,z6]),(0,[z20,z0,z1,z2,z4,z8,z6]),(0,[z150,z0,z1,z2,z4,z15,z6]),(0,[z0,z1,z2,z4,z5,z6,z589]),(1,[z0,z2,z4,z127,z5,z6]),(0,[z0,z23,z1,z2,z4,z5,z6]),(0,[z0,z128,z1,z2,z4,z5,z6])],[(0,[z91,z0,z1,z2,z4,z5,z6]),(0,[z590,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z570,z5,z6]),(0,[z0,z1,z2,z4,z591,z5,z6]),(0,[z0,z1,z2,z26,z4,z44,z6])],[(0,[z0,z1,z2,z4,z592,z5,z6]),(0,[z0,z1,z2,z593,z4,z5,z6]),(0,[z0,z1,z2,z594,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z595,z6]),(0,[z0,z1,z2,z596,z4,z5,z6]),(0,[z20,z0,z136,z1,z2,z4,z6])],[(0,[z0,z1,z2,z63,z4,z5,z6]),(0,[z597,z0,z1,z2,z4,z5,z6]),(0,[z150,z0,z96,z2,z4,z5,z6]),(0,[z150,z0,z1,z2,z97,z5,z6]),(0,[z0,z1,z2,z210,z4,z38,z6]),(0,[z0,z136,z1,z2,z4,z570,z6]),(0,[z0,z1,z2,z10,z4,z38,z6])]],
   [[(0,[z0,z598,z1,z2,z4,z5,z6]),(0,[z599,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z432,z6])],[(0,[z0,z1,z2,z148,z4,z5,z6]),(0,[z0,z1,z235,z10,z4,z5,z6]),(0,[z0,z600,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z46,z83]),(0,[z0,z1,z134,z2,z4,z5,z99])],[(0,[z91,z202,z1,z2,z4,z5,z6]),(0,[z0,z1,z601,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z130,z6]),(0,[z0,z1,z2,z4,z602,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z603]),(0,[z0,z1,z604,z2,z4,z5,z6]),(0,[z0,z1,z73,z2,z4,z280,z6]),(0,[z0,z605,z1,z2,z4,z5,z6]),(0,[z20,z0,z110,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z606,z6]),(0,[z20,z0,z1,z2,z148,z4,z6]),(0,[z0,z1,z2,z4,z607,z5,z6]),(0,[z0,z1,z235,z2,z10,z5,z6]),(0,[z271,z0,z1,z2,z4,z38,z6]),(0,[z0,z176,z1,z2,z4,z5,z6]),(0,[z0,z1,z416,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z421,z6]),(0,[z428,z20,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z15,z6,z141]),(0,[z20,z65,z0,z1,z2,z4,z6]),(0,[z20,z0,z1,z2,z119,z4,z6])],[(0,[z608,z0,z1,z2,z4,z5,z6]),(0,[z0,z609,z1,z2,z4,z5,z6]),(0,[z129,z0,z1,z2,z4,z248,z6]),(1,[z0,z55,z2,z4,z5,z6]),(0,[z0,z1,z2,z26,z4,z25,z6]),(0,[z0,z1,z2,z4,z5,z44,z6]),(0,[z0,z1,z610,z2,z4,z5,z6]),(0,[z0,z176,z2,z4,z5,z38,z6]),(0,[z0,z1,z2,z4,z161,z5,z6]),(0,[z0,z1,z2,z26,z5,z144,z6])],[(0,[z0,z1,z2,z4,z5,z611,z6]),(0,[z7,z0,z1,z2,z26,z4,z6]),(0,[z1,z2,z4,z25,z5,z8,z6]),(0,[z612,z0,z1,z2,z4,z5,z6]),(0,[z20,z0,z43,z1,z2,z4,z6]),(0,[z0,z1,z235,z2,z16,z5,z6])],[(0,[z0,z1,z2,z4,z613,z5,z6]),(0,[z165,z0,z1,z2,z4,z8,z6]),(0,[z0,z1,z2,z4,z38,z6,z141]),(0,[z0,z142,z1,z2,z32,z5,z6]),(0,[z133,z20,z0,z1,z2,z4,z6]),(0,[z0,z1,z614,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z63,z26,z4,z6]),(0,[z0,z615,z1,z2,z4,z5,z6]),(0,[z20,z0,z9,z1,z2,z4,z6]),(0,[z0,z1,z2,z616,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z617,z6]),(0,[z20,z64,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z618,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z619]),(0,[z0,z1,z2,z4,z5,z620,z6])],[(0,[z0,z1,z2,z174,z4,z5,z6]),(0,[z599,z20,z0,z1,z2,z4,z6])],[(0,[z621,z0,z1,z2,z4,z5,z6])],[(1,[z91,z120,z2,z4,z5,z6]),(0,[z0,z1,z622,z2,z4,z5,z6]),(0,[z623,z0,z1,z2,z4,z5,z6]),(0,[z0,z110,z1,z2,z4,z27,z6]),(1,[z0,z1,z89,z4,z5,z117]),(1,[z0,z1,z134,z2,z4,z137]),(0,[z0,z1,z2,z4,z99,z6,z137])],[(0,[z0,z1,z2,z148,z5,z6,z83]),(0,[z150,z0,z1,z135,z4,z5,z6]),(0,[z0,z2,z4,z127,z5,z38,z6])],[(0,[z0,z1,z624,z2,z4,z5,z6]),(0,[z207,z0,z100,z1,z4,z5,z6]),(0,[z165,z0,z110,z1,z2,z4,z6]),(0,[z296,z0,z1,z2,z4,z38,z6]),(0,[z20,z0,z565,z1,z2,z4,z6]),(0,[z0,z1,z134,z2,z4,z27,z6])],[(0,[z129,z0,z1,z231,z4,z5,z6]),(1,[z207,z1,z231,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z625]),(0,[z0,z1,z626,z2,z4,z5,z6]),(0,[z165,z0,z1,z2,z4,z15,z6]),(0,[z0,z110,z29,z2,z4,z5,z6]),(0,[z0,z1,z627,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z628,z5,z6]),(0,[z0,z1,z2,z67,z5,z44,z6]),(0,[z0,z1,z2,z629,z4,z5,z6]),(0,[z0,z1,z4,z15,z5,z38,z6]),(0,[z0,z265,z1,z2,z4,z5,z6])],[(0,[z65,z0,z1,z2,z4,z5,z62]),(0,[z0,z1,z2,z4,z630,z5,z6]),(0,[z0,z1,z235,z2,z4,z15,z6]),(0,[z0,z1,z235,z2,z119,z5,z6])]],
   [[(0,[z20,z91,z0,z1,z2,z4,z6]),(0,[z631,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z632]),(1,[z0,z1,z381,z2,z4,z6]),(0,[z0,z9,z1,z89,z4,z5,z6]),(1,[z0,z69,z1,z2,z4,z6]),(0,[z0,z413,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z633,z6])],[(0,[z0,z1,z2,z4,z5,z6,z634]),(0,[z0,z1,z635,z2,z4,z5,z6]),(0,[z0,z1,z2,z26,z4,z11,z6]),(0,[z0,z29,z1,z2,z4,z15,z6]),(0,[z0,z1,z2,z4,z276,z5,z6])],[(0,[z0,z1,z2,z4,z5,z636,z6]),(0,[z165,z0,z1,z134,z2,z4,z6]),(0,[z0,z1,z2,z637,z4,z5,z6]),(0,[z0,z1,z2,z4,z638,z5,z6]),(0,[z0,z43,z2,z4,z5,z44,z6]),(0,[z0,z1,z2,z26,z4,z118,z6]),(0,[z639,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z640,z4,z5,z6]),(0,[z0,z641,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z183,z6]),(0,[z0,z142,z1,z2,z4,z38,z6]),(0,[z0,z1,z2,z642,z4,z5,z6]),(1,[z0,z1,z2,z4,z185,z6]),(0,[z201,z0,z1,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z4,z6]),(0,[z20,z0,z90,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z6,z643]),(0,[z644,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z645,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z341]),(0,[z0,z1,z2,z26,z4,z99,z6])],[(0,[z0,z1,z231,z4,z5,z6,z46]),(0,[z0,z1,z2,z646,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z647]),(0,[z20,z0,z1,z2,z4,z6,z141]),(0,[z648,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z38,z214,z6]),(0,[z0,z23,z1,z2,z4,z226,z6]),(0,[z0,z2,z4,z5,z6,z327,z46]),(0,[z461,z20,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z15,z6,z87]),(1,[z0,z1,z2,z4,z181,z6]),(0,[z0,z1,z2,z4,z5,z649,z6])],[(0,[z202,z41,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z650,z6]),(0,[z0,z1,z2,z4,z5,z6,z651]),(0,[z0,z1,z2,z4,z38,z30,z6])]],
   [[(0,[z0,z1,z652,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z653,z5,z6]),(1,[z0,z223,z2,z4,z5,z6]),(0,[z21,z0,z1,z2,z4,z15,z6]),(0,[z65,z0,z1,z2,z26,z4,z6]),(0,[z0,z73,z2,z4,z52,z5,z6]),(0,[z0,z1,z2,z4,z654,z5,z6]),(0,[z0,z655,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z656])],[(0,[z0,z252,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z657,z5,z6]),(0,[z0,z658,z1,z2,z4,z5,z6]),(0,[z0,z238,z1,z2,z4,z15,z6])],[(0,[z0,z156,z1,z120,z2,z5,z6]),(0,[z207,z0,z139,z2,z4,z5,z6]),(0,[z133,z0,z1,z68,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z118,z6])],[(0,[z0,z1,z2,z4,z5,z659,z6]),(0,[z0,z660,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z26,z4,z38,z6]),(0,[z0,z1,z2,z4,z27,z38,z6]),(0,[z0,z237,z1,z2,z4,z15,z6]),(0,[z639,z20,z0,z1,z2,z4,z6]),(0,[z661,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z662,z2,z4,z5,z6]),(0,[z663,z0,z1,z2,z4,z5,z6]),(0,[z129,z0,z1,z2,z4,z15,z6]),(0,[z0,z664,z1,z2,z4,z5,z6]),(0,[z0,z283,z1,z4,z11,z5,z6]),(0,[z20,z0,z1,z2,z4,z188,z6]),(0,[z0,z1,z2,z4,z5,z99,z6])],[(0,[z202,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z231,z2,z4,z5,z6]),(0,[z0,z1,z2,z665,z4,z5,z6]),(0,[z64,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z45,z6])],[(0,[z0,z236,z1,z2,z4,z5,z6]),(0,[z0,z1,z235,z2,z4,z5,z6]),(0,[z0,z81,z1,z2,z26,z5,z6]),(0,[z0,z1,z666,z2,z4,z5,z6]),(1,[z0,z1,z235,z2,z26,z6]),(0,[z0,z1,z2,z10,z4,z15,z6]),(0,[z0,z1,z2,z4,z667,z5,z6])],[(0,[z0,z2,z4,z5,z44,z6,z87]),(0,[z0,z81,z1,z2,z4,z38,z6]),(0,[z668,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z669,z0,z1,z2,z4,z5,z6]),(0,[z670,z0,z1,z2,z4,z5,z6]),(1,[z0,z196,z2,z4,z5,z6]),(0,[z0,z671,z1,z2,z4,z5,z6]),(0,[z0,z100,z1,z2,z4,z38,z6]),(0,[z0,z1,z2,z4,z672,z5,z6]),(0,[z0,z1,z2,z4,z5,z117,z83]),(0,[z0,z90,z1,z2,z32,z5,z6])],[(0,[z0,z1,z2,z4,z673,z5,z6]),(0,[z84,z0,z136,z1,z2,z5,z6]),(0,[z0,z73,z2,z28,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z674,z6]),(0,[z0,z1,z2,z4,z52,z5,z6]),(0,[z0,z1,z2,z4,z15,z6,z83])],[(0,[z271,z0,z1,z2,z4,z15,z6]),(0,[z0,z90,z1,z2,z4,z5,z118])],[(0,[z207,z1,z231,z2,z4,z5,z6]),(0,[z0,z1,z231,z2,z4,z348,z6]),(0,[z0,z1,z73,z2,z4,z38,z6]),(0,[z0,z1,z675,z2,z4,z5,z6]),(1,[z0,z1,z2,z163,z38,z6]),(0,[z0,z1,z2,z4,z5,z38,z6]),(0,[z0,z1,z2,z4,z5,z6,z676]),(0,[z0,z23,z1,z2,z4,z272,z6])],[(0,[z0,z1,z2,z4,z5,z6,z677]),(0,[z0,z1,z2,z4,z5,z6,z678])],[(0,[z0,z1,z2,z4,z679,z5,z6]),(0,[z0,z1,z381,z2,z4,z5,z6]),(0,[z0,z1,z2,z680,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z30,z6]),(0,[z0,z1,z486,z2,z4,z5,z6]),(0,[z681,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z37,z4,z15,z6]),(1,[z0,z1,z2,z4,z102,z6]),(0,[z0,z1,z2,z682,z4,z5,z6])],[(0,[z202,z0,z1,z2,z26,z4,z6]),(0,[z683,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z231,z2,z26,z4,z6]),(0,[z84,z0,z1,z2,z148,z5,z6]),(0,[z0,z684,z1,z2,z4,z5,z6]),(0,[z64,z0,z1,z2,z26,z4,z6]),(0,[z685,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z15,z187,z6]),(0,[z0,z1,z2,z26,z4,z6,z83]),(0,[z0,z1,z2,z119,z5,z144,z6]),(1,[z0,z1,z2,z4,z82,z6])],[(1,[z0,z1,z2,z4,z248,z6]),(0,[z21,z0,z1,z2,z4,z5,z6]),(0,[z0,z100,z1,z4,z5,z38,z6]),(1,[z0,z283,z1,z4,z5,z6]),(1,[z0,z1,z2,z4,z393,z6]),(0,[z0,z1,z89,z4,z5,z117,z6])]],
   [[(0,[z0,z41,z2,z4,z5,z6,z87]),(0,[z207,z129,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z686,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z687]),(0,[z0,z1,z2,z4,z5,z688,z6])],[(0,[z689,z0,z1,z2,z4,z5,z6]),(0,[z690,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z691,z6]),(0,[z0,z1,z2,z4,z5,z527,z6]),(0,[z0,z1,z2,z4,z15,z6,z285]),(0,[z0,z1,z2,z4,z692,z5,z6])],[(0,[z0,z1,z2,z4,z5,z264,z6]),(0,[z0,z1,z2,z693,z4,z5,z6]),(0,[z694,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z68,z4,z5,z38,z6]),(0,[z0,z1,z2,z163,z4,z5,z6]),(0,[z31,z0,z1,z2,z4,z5,z6])],[(0,[z129,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z695]),(0,[z84,z0,z1,z2,z140,z5,z6]),(0,[z0,z1,z2,z696,z4,z5,z6]),(0,[z0,z1,z2,z4,z279,z5,z6]),(0,[z0,z697,z1,z2,z4,z5,z6]),(0,[z64,z0,z43,z2,z4,z5,z6]),(0,[z523,z0,z1,z2,z4,z38,z6]),(0,[z0,z1,z2,z4,z293,z15,z6]),(0,[z0,z1,z2,z4,z5,z6,z698])],[(0,[z84,z0,z142,z1,z2,z5,z6]),(1,[z0,z1,z2,z602,z5,z6]),(0,[z0,z1,z2,z4,z38,z62,z6]),(0,[z0,z699,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z67,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z700]),(0,[z0,z90,z1,z2,z4,z38,z6])],[(1,[z483,z0,z1,z2,z4,z5]),(0,[z150,z0,z1,z2,z602,z5,z6])],[(0,[z0,z258,z1,z120,z4,z5,z6]),(0,[z701,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z702,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z28,z4,z6]),(0,[z20,z0,z1,z235,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z83]),(0,[z0,z1,z703,z2,z4,z5,z6])],[(0,[z0,z704,z1,z2,z4,z5,z6]),(0,[z65,z0,z43,z1,z2,z4,z5]),(0,[z0,z705,z1,z2,z4,z5,z6]),(1,[z0,z2,z4,z160,z5,z6]),(0,[z0,z1,z2,z706,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z536])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[],[(0,[z0,z78,z1,z2,z15,z6]),(0,[z0,z1,z4,z707,z5,z6]),(0,[z0,z1,z2,z4,z99,z122]),(0,[z0,z1,z2,z67,z6,z173]),(0,[z0,z2,z26,z4,z160,z6]),(0,[z0,z1,z2,z5,z6,z708])],[(0,[z0,z1,z709,z4,z5,z6]),(0,[z710,z0,z1,z2,z4,z6]),(0,[z0,z9,z1,z4,z248,z6]),(0,[z0,z1,z425,z4,z384,z6]),(0,[z0,z1,z2,z4,z711,z6]),(0,[z0,z712,z1,z2,z4,z6]),(0,[z0,z713,z1,z4,z243,z6]),(0,[z0,z136,z2,z5,z6,z509]),(0,[z0,z1,z2,z67,z45,z6]),(0,[z0,z2,z4,z160,z244,z6])],[(0,[z0,z1,z538,z4,z38,z6]),(0,[z0,z68,z4,z127,z38,z6]),(0,[z0,z2,z163,z127,z38,z6]),(0,[z0,z1,z2,z26,z6,z619])],[(0,[z0,z1,z2,z4,z5,z714])],[(0,[z0,z715,z1,z2,z5,z6]),(0,[z207,z1,z231,z4,z5,z6]),(0,[z0,z55,z2,z26,z4,z6]),(0,[z0,z716,z2,z26,z4,z6])],[(0,[z0,z1,z2,z4,z717,z6]),(0,[z0,z1,z2,z4,z718,z6])],[(0,[z0,z1,z2,z4,z719,z6]),(0,[z0,z78,z1,z376,z2,z5]),(0,[z0,z720,z1,z2,z4,z6]),(0,[z0,z1,z721,z2,z4,z6]),(0,[z0,z81,z1,z244,z16,z6]),(0,[z0,z2,z4,z38,z722,z6])],[(0,[z0,z723,z2,z4,z5,z6]),(0,[z0,z1,z2,z724,z5,z6]),(0,[z20,z0,z96,z2,z4,z6])],[(0,[z20,z0,z1,z2,z249,z6]),(0,[z0,z9,z210,z4,z38,z6])],[(0,[z0,z1,z2,z5,z6,z725]),(0,[z0,z1,z2,z4,z726,z6]),(0,[z0,z1,z2,z4,z183,z6])],[(0,[z0,z1,z2,z4,z727,z6]),(0,[z0,z176,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z728,z6]),(0,[z0,z1,z159,z4,z15,z6]),(0,[z20,z0,z1,z4,z6,z167]),(0,[z0,z370,z1,z4,z164,z6])],[(0,[z0,z1,z186,z2,z163,z6]),(0,[z0,z729,z2,z4,z38,z6])],[(0,[z0,z1,z2,z4,z181,z6]),(0,[z0,z1,z2,z164,z6,z83]),(0,[z0,z730,z1,z4,z5,z6])],[(0,[z0,z1,z2,z4,z731,z6]),(0,[z207,z1,z231,z26,z4,z6]),(0,[z0,z1,z2,z6,z149,z173]),(0,[z0,z81,z1,z16,z5,z341]),(0,[z0,z1,z2,z26,z163,z6]),(0,[z0,z1,z68,z4,z164,z6]),(0,[z0,z732,z2,z4,z5,z6])],[(0,[z0,z1,z2,z733,z5,z6]),(0,[z0,z1,z2,z4,z181,z341]),(0,[z0,z176,z2,z4,z6,z137]),(0,[z0,z1,z2,z32,z26,z316])]],
   [[(1,[z0,z9,z1,z163,z6]),(0,[z201,z0,z176,z2,z4,z6])],[(0,[z165,z0,z1,z2,z60,z6]),(0,[z0,z734,z1,z2,z4,z6]),(0,[z0,z1,z2,z163,z181,z6])],[(0,[z0,z1,z735,z4,z5,z6]),(0,[z123,z0,z2,z4,z160,z6]),(0,[z736,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z32,z278,z6])],[(0,[z0,z1,z2,z4,z6,z173]),(0,[z20,z0,z1,z2,z205,z6]),(0,[z0,z1,z2,z4,z737,z6])],[(0,[z0,z252,z1,z4,z15,z6]),(0,[z0,z1,z2,z738,z4,z6]),(0,[z0,z739,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z45,z6]),(0,[z0,z176,z2,z26,z4,z6])],[(0,[z7,z0,z176,z2,z4,z6]),(0,[z0,z81,z1,z16,z38,z6]),(0,[z0,z1,z2,z740,z163,z6])],[],[(0,[z0,z196,z2,z4,z5,z6]),(0,[z0,z741,z1,z2,z4,z5]),(0,[z0,z742,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z6,z743]),(0,[z0,z1,z2,z26,z5,z341]),(0,[z71,z1,z2,z4,z115,z6]),(0,[z0,z732,z2,z26,z4,z6])],[(0,[z0,z744,z2,z4,z5,z6])],[(0,[z0,z81,z1,z16,z5,z527]),(0,[z0,z1,z2,z4,z745,z6]),(0,[z0,z1,z2,z4,z746,z6])],[(0,[z0,z747,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z748,z6]),(0,[z165,z565,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z27,z504]),(0,[z0,z1,z2,z163,z6,z87]),(0,[z0,z236,z2,z4,z127,z6])],[(0,[z0,z1,z270,z4,z15,z6])],[(0,[z103,z1,z2,z140,z5,z6]),(0,[z0,z9,z637,z4,z5,z6]),(0,[z0,z1,z2,z4,z749,z6]),(0,[z0,z1,z4,z6,z167,z173]),(0,[z201,z0,z1,z2,z163,z6]),(0,[z0,z1,z2,z4,z102,z6])],[(0,[z0,z1,z2,z4,z750,z6]),(0,[z0,z1,z2,z4,z751,z6]),(0,[z0,z1,z2,z752,z5,z6]),(0,[z0,z1,z2,z26,z753,z6]),(0,[z0,z1,z2,z4,z82,z6]),(0,[z20,z0,z730,z1,z4,z6])],[(0,[z207,z340,z1,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z754]),(0,[z755,z0,z1,z2,z4,z6])]],
   [[(0,[z0,z196,z2,z26,z4,z6]),(0,[z0,z1,z2,z4,z244,z6]),(0,[z0,z1,z2,z290,z15,z6]),(0,[z0,z756,z2,z4,z5,z6])],[(0,[z0,z1,z63,z4,z164,z6]),(0,[z0,z1,z2,z4,z748,z6]),(0,[z7,z0,z1,z2,z163,z6]),(0,[z0,z1,z2,z4,z5,z757]),(0,[z0,z1,z758,z4,z5,z6])],[(0,[z0,z1,z2,z4,z759,z6]),(0,[z1,z2,z4,z748,z8,z6]),(0,[z0,z1,z2,z4,z760,z6]),(0,[z0,z761,z1,z2,z4,z6]),(0,[z461,z0,z495,z2,z4,z6])],[(0,[z0,z1,z2,z4,z762,z6]),(0,[z0,z1,z4,z243,z5,z6])],[(0,[z0,z1,z2,z4,z763,z6]),(0,[z0,z292,z2,z97,z5,z6]),(0,[z201,z0,z9,z1,z4,z6]),(0,[z0,z1,z301,z4,z764,z6]),(0,[z0,z1,z2,z765,z38,z6]),(0,[z20,z0,z1,z2,z4,z766])],[(0,[z20,z0,z1,z2,z119,z6])],[(0,[z21,z1,z2,z767,z5,z6]),(0,[z0,z2,z4,z160,z5,z6]),(0,[z0,z1,z2,z4,z768,z6])],[(0,[z0,z1,z2,z15,z6,z149])],[(0,[z0,z78,z1,z2,z769,z6]),(0,[z20,z483,z0,z1,z2,z4]),(0,[z770,z0,z1,z2,z4,z6]),(0,[z0,z9,z210,z4,z15,z6])],[(0,[z0,z771,z2,z4,z5,z6]),(0,[z0,z1,z2,z32,z570,z6])],[(0,[z0,z219,z176,z4,z38,z6]),(0,[z0,z772,z2,z4,z5,z6])],[(0,[z483,z0,z1,z2,z4,z38]),(0,[z483,z0,z1,z2,z26,z4]),(0,[z296,z1,z2,z4,z8,z6]),(1,[z1,z2,z4,z5,z773]),(0,[z0,z1,z2,z38,z6,z362]),(0,[z0,z2,z4,z6,z327,z774])],[(0,[z0,z1,z2,z4,z5,z775]),(0,[z1,z2,z4,z767,z5,z6]),(0,[z0,z2,z4,z52,z776,z6]),(0,[z0,z265,z23,z4,z5,z46]),(0,[z0,z777,z2,z4,z5,z6])],[(0,[z0,z9,z1,z163,z4,z6]),(0,[z0,z1,z2,z778,z6,z149]),(0,[z20,z0,z1,z2,z779,z6])],[(0,[z0,z1,z2,z780,z5,z6]),(0,[z0,z1,z2,z4,z99,z18]),(0,[z0,z781,z1,z4,z5,z6])],[(0,[z0,z283,z1,z4,z195,z6]),(0,[z0,z110,z2,z4,z247,z6]),(0,[z0,z782,z2,z4,z5,z6])]],
   [[(0,[z0,z292,z2,z4,z5,z6]),(0,[z207,z139,z231,z4,z5,z6]),(0,[z783,z0,z1,z2,z4,z6])],[(0,[z427,z0,z1,z2,z163,z6])],[(0,[z0,z1,z2,z163,z8,z6]),(0,[z0,z1,z2,z784,z5,z6]),(0,[z0,z1,z2,z67,z5,z6]),(0,[z0,z1,z68,z4,z38,z6])],[(0,[z0,z785,z2,z4,z5,z6])],[],[(0,[z0,z1,z2,z786,z5,z6]),(0,[z0,z2,z26,z4,z127,z6])],[(0,[z0,z1,z2,z4,z787,z6]),(0,[z0,z1,z788,z4,z5,z6]),(0,[z0,z100,z73,z4,z38,z6]),(0,[z0,z1,z2,z32,z5,z419]),(0,[z0,z110,z2,z4,z776,z6]),(0,[z0,z413,z1,z4,z38,z6]),(0,[z0,z1,z2,z4,z6,z789]),(0,[z0,z1,z2,z37,z32,z6]),(0,[z0,z1,z68,z163,z38,z6])],[(0,[z0,z790,z1,z2,z4,z6]),(0,[z0,z1,z4,z74,z5,z6]),(0,[z0,z136,z2,z28,z38,z6]),(0,[z64,z0,z2,z4,z38,z87]),(0,[z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z4,z791,z6]),(0,[z0,z1,z2,z32,z26,z453])],[(0,[z0,z792,z2,z4,z5,z6]),(0,[z0,z96,z2,z4,z335,z6]),(0,[z0,z1,z2,z97,z335,z6]),(0,[z0,z1,z2,z26,z6,z77])],[(0,[z0,z1,z2,z4,z793,z6])],[(0,[z0,z252,z47,z1,z4,z6]),(0,[z0,z1,z2,z4,z794,z5]),(0,[z0,z1,z2,z4,z161,z99])],[(0,[z0,z1,z425,z4,z38,z6]),(0,[z0,z1,z2,z4,z795,z6]),(0,[z0,z1,z414,z4,z38,z6])],[(0,[z91,z47,z120,z2,z4,z6]),(0,[z0,z1,z4,z796,z5,z6]),(0,[z201,z0,z1,z2,z290,z6])],[(0,[z0,z2,z4,z5,z6,z797]),(0,[z0,z1,z4,z798,z6,z167]),(0,[z0,z1,z4,z799,z38,z6])],[(0,[z65,z1,z232,z2,z4,z5])],[(0,[z0,z2,z4,z800,z5,z6]),(0,[z0,z1,z801,z4,z5,z6]),(1,[z0,z176,z2,z163,z6])]],
   [[(0,[z0,z802,z1,z2,z4,z6]),(0,[z0,z1,z803,z4,z5,z6]),(0,[z0,z1,z2,z163,z161,z6])],[(0,[z0,z1,z2,z804,z5,z6]),(0,[z0,z805,z2,z4,z5,z6]),(0,[z0,z142,z2,z630,z5,z6])],[(0,[z0,z9,z2,z67,z5,z6]),(0,[z0,z1,z2,z76,z5,z6])],[],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z91,z156,z120,z2,z5,z6]),(0,[z0,z1,z806,z2,z4,z6])],[(0,[z91,z807,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z808,z6]),(0,[z0,z1,z2,z4,z809,z6]),(0,[z0,z1,z2,z810,z5,z6])],[(0,[z0,z1,z2,z4,z6,z811]),(0,[z0,z81,z1,z200,z26,z6])],[(0,[z0,z1,z2,z4,z812,z6]),(0,[z0,z9,z4,z74,z5,z6]),(0,[z0,z813,z2,z4,z5,z6])],[(0,[z0,z55,z2,z4,z38,z6]),(0,[z0,z1,z2,z4,z814,z6]),(0,[z0,z1,z2,z4,z5,z815]),(0,[z0,z1,z425,z602,z5,z6]),(0,[z0,z4,z127,z74,z5,z6]),(0,[z0,z816,z2,z4,z38,z6]),(0,[z0,z1,z2,z4,z817,z6])],[(0,[z202,z41,z2,z4,z5,z6]),(0,[z0,z2,z28,z213,z5,z6]),(0,[z0,z2,z4,z818,z38,z6]),(0,[z0,z1,z2,z4,z819,z6]),(0,[z820,z0,z1,z2,z24,z6])],[(0,[z0,z156,z73,z2,z5,z6]),(0,[z0,z1,z2,z821,z4,z6]),(0,[z0,z1,z2,z5,z6,z822])],[(0,[z0,z823,z2,z4,z5,z6]),(0,[z0,z96,z2,z4,z384,z6]),(0,[z0,z1,z2,z97,z384,z6])],[(0,[z0,z1,z2,z4,z824,z6]),(0,[z0,z1,z2,z32,z5,z118])],[(0,[z0,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z825,z5,z6]),(0,[z0,z1,z2,z4,z826,z6]),(0,[z0,z1,z2,z210,z163,z6]),(0,[z0,z827,z1,z4,z5,z6])],[(0,[z0,z1,z2,z828,z4,z6]),(0,[z0,z1,z2,z5,z6,z829]),(1,[z0,z81,z1,z164,z6]),(0,[z0,z176,z2,z4,z127,z6]),(0,[z0,z1,z163,z15,z38,z6]),(0,[z0,z1,z2,z469,z5,z118])],[(0,[z91,z78,z120,z2,z5,z6]),(0,[z0,z1,z120,z2,z163,z6]),(0,[z0,z830,z223,z2,z4,z6]),(0,[z84,z1,z2,z767,z5,z6])]],
   [[(0,[z0,z142,z2,z667,z5,z6]),(0,[z0,z2,z4,z776,z30,z6])],[(0,[z0,z162,z1,z2,z4,z6]),(0,[z207,z1,z231,z4,z38,z6]),(1,[z0,z2,z4,z776,z6])],[(1,[z807,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z831,z6]),(0,[z0,z176,z2,z163,z5,z6]),(0,[z275,z1,z2,z4,z39,z6])],[(0,[z0,z78,z1,z2,z832,z6]),(0,[z0,z833,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z834,z6]),(0,[z0,z1,z835,z2,z4,z6]),(0,[z0,z9,z1,z4,z280,z6]),(0,[z20,z0,z1,z89,z4,z117])],[(0,[z0,z1,z2,z4,z836,z6]),(0,[z0,z9,z4,z127,z5,z6]),(0,[z0,z723,z2,z4,z38,z6]),(0,[z0,z1,z89,z2,z163,z6])],[(0,[z129,z526,z1,z4,z5,z6]),(0,[z65,z1,z2,z4,z5,z773]),(0,[z0,z1,z2,z26,z6,z651]),(0,[z0,z100,z73,z4,z15,z6]),(0,[z0,z413,z1,z4,z15,z6]),(0,[z0,z1,z301,z4,z45,z6])],[(0,[z0,z1,z837,z4,z5,z6]),(0,[z0,z838,z1,z4,z5,z6]),(0,[z0,z334,z2,z4,z247,z6])],[(0,[z0,z1,z2,z4,z839,z6]),(0,[z0,z1,z2,z4,z840,z6]),(0,[z0,z1,z2,z4,z841,z6]),(0,[z201,z0,z1,z463,z4,z6])],[(0,[z0,z176,z2,z4,z27,z6]),(0,[z0,z842,z1,z4,z5,z6])],[(0,[z0,z843,z2,z4,z38,z6]),(0,[z0,z844,z1,z2,z4,z6])],[(0,[z0,z1,z425,z4,z15,z6]),(0,[z0,z1,z290,z15,z38,z6]),(0,[z0,z237,z1,z2,z26,z6]),(0,[z845,z0,z1,z2,z4,z6])],[(0,[z0,z846,z139,z2,z4,z6]),(0,[z0,z223,z2,z4,z38,z6]),(0,[z0,z1,z646,z4,z38,z6]),(0,[z0,z1,z4,z15,z489,z6]),(0,[z0,z1,z2,z163,z30,z6]),(0,[z0,z1,z2,z847,z5,z6]),(0,[z0,z1,z2,z4,z22,z6]),(0,[z201,z0,z1,z2,z4,z6])],[(0,[z0,z1,z376,z2,z4,z5]),(0,[z0,z1,z2,z5,z6,z848]),(0,[z296,z0,z176,z2,z4,z6])],[(0,[z0,z1,z2,z849,z4,z6]),(0,[z0,z850,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z27,z143]),(0,[z0,z1,z2,z4,z181,z527]),(0,[z0,z1,z2,z779,z26,z6])],[(0,[z0,z9,z120,z4,z38,z6]),(0,[z0,z136,z2,z28,z26,z6]),(0,[z0,z1,z2,z26,z117,z83])],[(0,[z0,z851,z1,z2,z4,z6])]],
   [[(0,[z0,z1,z2,z4,z852,z6]),(0,[z0,z1,z4,z853,z5,z6]),(0,[z0,z1,z2,z854,z4,z6]),(0,[z20,z0,z1,z2,z32,z118]),(0,[z0,z1,z2,z4,z855,z6])],[(0,[z129,z0,z1,z2,z163,z6])],[(0,[z91,z252,z120,z4,z5,z6]),(0,[z0,z1,z856,z4,z5,z6]),(0,[z0,z857,z1,z2,z4,z6]),(0,[z0,z43,z96,z2,z4,z5]),(0,[z0,z1,z2,z4,z858,z6]),(0,[z0,z142,z2,z11,z5,z6]),(0,[z0,z219,z1,z4,z74,z6]),(0,[z0,z237,z1,z2,z4,z6])],[(0,[z0,z196,z2,z4,z38,z6]),(0,[z0,z1,z2,z4,z859,z6])],[(0,[z64,z0,z96,z2,z4,z5]),(0,[z0,z100,z1,z4,z5,z341]),(0,[z0,z1,z2,z45,z6,z149]),(0,[z0,z1,z2,z860,z5,z6])],[(0,[z0,z47,z258,z1,z4,z6]),(0,[z547,z1,z2,z4,z8,z6]),(1,[z0,z861,z4,z5,z6]),(0,[z0,z1,z2,z10,z163,z6]),(0,[z0,z1,z2,z779,z4,z6])],[(0,[z0,z1,z2,z4,z862,z6]),(0,[z0,z100,z1,z163,z5,z6]),(0,[z0,z1,z2,z26,z688,z6])],[(0,[z0,z9,z2,z4,z45,z6])],[(0,[z863,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z864,z6]),(0,[z0,z142,z2,z26,z11,z6]),(0,[z296,z0,z1,z2,z163,z6])],[(0,[z483,z0,z73,z2,z4,z5]),(0,[z0,z258,z1,z376,z4,z5]),(0,[z0,z1,z449,z4,z15,z6]),(0,[z346,z547,z1,z2,z4,z6])],[(0,[z865,z0,z1,z2,z4,z6]),(0,[z0,z866,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z867,z6]),(0,[z0,z1,z2,z4,z868,z6]),(0,[z0,z1,z89,z4,z88,z117])],[(0,[z0,z1,z869,z2,z4,z6]),(0,[z0,z90,z1,z2,z5,z870])],[(0,[z0,z1,z2,z4,z871,z6]),(0,[z0,z872,z1,z2,z5,z6]),(0,[z0,z9,z110,z4,z38,z6]),(0,[z0,z1,z2,z873,z5,z6]),(0,[z0,z1,z2,z26,z6,z83]),(0,[z427,z0,z1,z463,z4,z6])],[(0,[z0,z156,z258,z1,z5,z6]),(0,[z0,z81,z100,z1,z26,z6]),(0,[z0,z1,z2,z874,z38,z6]),(0,[z0,z1,z4,z5,z6,z875])],[(0,[z0,z1,z2,z10,z5,z341]),(0,[z0,z1,z2,z4,z876,z6]),(0,[z877,z0,z1,z2,z4,z6])],[(0,[z0,z139,z2,z4,z5,z6]),(0,[z0,z1,z2,z878,z4,z6]),(0,[z0,z525,z1,z2,z26,z6]),(0,[z0,z9,z412,z4,z5,z6]),(0,[z0,z1,z2,z60,z5,z6])]],
   [[(0,[z0,z1,z2,z26,z692,z6])],[(0,[z65,z0,z1,z2,z163,z6]),(0,[z0,z237,z1,z2,z37,z6]),(0,[z0,z1,z2,z26,z187,z6])],[(0,[z0,z1,z2,z4,z879,z6]),(0,[z0,z265,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z880]),(0,[z0,z2,z4,z160,z38,z6]),(0,[z0,z1,z89,z4,z164,z6])],[(0,[z20,z0,z1,z2,z329,z6]),(0,[z111,z1,z2,z4,z25,z6]),(0,[z0,z292,z2,z4,z335,z6]),(0,[z0,z1,z2,z4,z881,z6]),(0,[z882,z0,z1,z2,z4,z6]),(0,[z0,z43,z1,z2,z163,z6]),(0,[z0,z1,z301,z67,z5,z6]),(0,[z0,z1,z2,z60,z6,z137])],[(0,[z883,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z26,z884,z6])],[(0,[z0,z219,z1,z4,z38,z6]),(0,[z64,z0,z1,z2,z163,z6]),(0,[z0,z1,z2,z4,z885,z38]),(0,[z0,z1,z2,z886,z38,z6])],[(0,[z0,z1,z887,z4,z5,z6]),(0,[z0,z1,z2,z163,z218,z6])],[(0,[z0,z1,z2,z5,z6,z149]),(0,[z0,z1,z2,z4,z888,z6])],[(0,[z889,z0,z1,z2,z602,z6])],[(0,[z0,z110,z2,z4,z280,z6]),(0,[z0,z732,z2,z4,z164,z6])],[(0,[z0,z223,z2,z4,z15,z6]),(0,[z0,z2,z4,z890,z5,z6])],[(0,[z0,z9,z162,z2,z4,z6]),(0,[z0,z891,z2,z4,z5,z6]),(0,[z0,z1,z4,z15,z799,z6]),(0,[z20,z0,z90,z1,z2,z83]),(0,[z428,z0,z1,z2,z60,z6])],[(0,[z0,z292,z2,z26,z4,z6])],[(0,[z91,z0,z1,z2,z163,z6]),(0,[z585,z120,z2,z4,z5,z6]),(0,[z21,z1,z2,z148,z38,z6]),(0,[z0,z1,z2,z4,z892,z6])],[(0,[z0,z893,z1,z2,z4,z6]),(0,[z129,z1,z63,z4,z38,z6]),(0,[z20,z0,z55,z2,z4,z6]),(0,[z0,z1,z2,z4,z894,z6]),(0,[z0,z1,z2,z4,z895,z6]),(0,[z0,z1,z2,z67,z38,z6]),(0,[z0,z1,z235,z2,z244,z6]),(0,[z0,z1,z2,z26,z6,z93]),(0,[z0,z23,z4,z5,z327,z46])],[(0,[z0,z1,z2,z896,z5,z6]),(0,[z0,z1,z2,z4,z897,z6])]],
   [[(0,[z0,z1,z4,z5,z6,z898]),(0,[z0,z1,z2,z4,z899,z6])],[],[(0,[z133,z0,z1,z463,z4,z6])],[(0,[z0,z1,z2,z4,z900,z6]),(1,[z1,z2,z4,z748,z6]),(0,[z0,z1,z4,z74,z38,z6]),(0,[z1,z2,z4,z5,z6,z901])],[(0,[z0,z96,z2,z4,z38,z6]),(0,[z0,z1,z2,z97,z38,z6]),(0,[z0,z1,z902,z4,z5,z6]),(0,[z0,z1,z2,z4,z903,z6]),(0,[z0,z1,z2,z904,z88,z6])],[(0,[z75,z41,z2,z4,z5,z6]),(0,[z0,z905,z2,z4,z5,z6]),(0,[z84,z295,z1,z2,z140,z6]),(0,[z0,z1,z301,z4,z5,z6]),(0,[z0,z1,z2,z4,z906,z6]),(0,[z0,z1,z2,z4,z907,z6]),(0,[z20,z0,z246,z2,z4,z6])],[],[(0,[z0,z1,z2,z4,z335,z6]),(0,[z20,z0,z1,z425,z4,z6]),(0,[z0,z1,z2,z4,z908,z6]),(0,[z0,z1,z703,z4,z38,z6])],[(0,[z0,z47,z1,z376,z2,z4]),(0,[z0,z1,z2,z163,z140,z6]),(0,[z0,z1,z4,z15,z6,z167]),(0,[z0,z1,z2,z4,z909,z6]),(0,[z0,z910,z2,z4,z5,z6])],[(0,[z0,z1,z911,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z912]),(0,[z0,z1,z2,z4,z5,z341]),(0,[z0,z1,z2,z4,z913,z6]),(0,[z0,z1,z2,z4,z6,z914])],[(0,[z1,z231,z837,z4,z5,z6]),(0,[z0,z81,z1,z630,z5,z6]),(0,[z0,z100,z861,z4,z5,z6]),(0,[z0,z1,z2,z915,z5,z6]),(1,[z0,z1,z2,z163,z6]),(0,[z133,z0,z1,z2,z163,z6])],[(0,[z150,z96,z2,z4,z5,z141]),(0,[z150,z1,z2,z97,z5,z141]),(0,[z0,z1,z2,z4,z916,z6]),(0,[z0,z1,z2,z163,z5,z6]),(0,[z0,z1,z2,z163,z127,z6]),(0,[z0,z1,z801,z26,z4,z6])],[(0,[z483,z0,z258,z1,z4,z5]),(0,[z0,z1,z152,z4,z38,z6])],[(0,[z0,z258,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z917,z6]),(0,[z0,z1,z2,z4,z918,z6])],[(0,[z0,z1,z4,z5,z6,z919]),(0,[z20,z0,z196,z2,z4,z6]),(0,[z0,z73,z4,z5,z6,z167]),(0,[z0,z1,z2,z4,z920,z6]),(0,[z20,z0,z1,z301,z4,z6])],[(0,[z483,z0,z162,z1,z2,z4]),(0,[z129,z1,z837,z4,z5,z6]),(0,[z0,z1,z2,z163,z6,z137]),(0,[z0,z1,z2,z4,z753,z6]),(0,[z0,z2,z921,z4,z5,z6]),(0,[z0,z1,z2,z4,z27,z99])]],
   [[(0,[z0,z1,z2,z4,z922,z6]),(0,[z0,z1,z2,z923,z4,z6]),(0,[z0,z1,z4,z924,z243,z6]),(0,[z0,z1,z2,z15,z6,z925])],[(0,[z0,z1,z2,z4,z926,z6]),(0,[z0,z237,z1,z2,z16,z6]),(0,[z0,z1,z2,z2,z163,z6]),(0,[z0,z1,z927,z2,z4,z6])],[(0,[z0,z1,z2,z26,z4,z341]),(0,[z0,z246,z81,z4,z5,z6]),(0,[z0,z1,z10,z4,z164,z6]),(0,[z0,z1,z2,z26,z4,z912])],[(0,[z0,z1,z2,z4,z928,z6]),(0,[z929,z0,z1,z2,z163,z6]),(0,[z0,z1,z2,z163,z144,z6]),(0,[z0,z1,z200,z37,z4,z6]),(0,[z0,z1,z2,z4,z99,z914])],[(0,[z0,z930,z2,z4,z5,z6]),(0,[z0,z1,z2,z26,z6,z149]),(0,[z0,z1,z2,z4,z5,z527]),(0,[z0,z1,z2,z26,z4,z815])],[(0,[z202,z41,z2,z26,z4,z6]),(0,[z0,z1,z2,z4,z931,z6]),(0,[z0,z1,z4,z5,z6,z167]),(0,[z0,z1,z2,z163,z27,z6])],[(0,[z0,z258,z1,z26,z4,z6]),(0,[z0,z1,z2,z4,z932,z5]),(0,[z64,z0,z2,z4,z5,z634]),(0,[z0,z933,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z914,z137])],[(0,[z0,z934,z2,z4,z5,z6]),(0,[z0,z1,z935,z4,z5,z6]),(0,[z150,z1,z2,z4,z5,z141]),(0,[z0,z1,z301,z4,z6,z173]),(0,[z0,z1,z2,z724,z38,z6]),(0,[z0,z487,z1,z4,z5,z46])],[(0,[z0,z29,z368,z2,z4,z6]),(0,[z0,z1,z2,z26,z185,z6])],[(0,[z0,z136,z2,z28,z15,z6]),(0,[z64,z0,z2,z4,z15,z87]),(0,[z0,z2,z4,z5,z44,z880])],[(0,[z936,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z384,z6]),(0,[z0,z1,z4,z840,z38,z6]),(0,[z0,z1,z2,z4,z937,z6]),(0,[z0,z43,z2,z4,z44,z173]),(0,[z0,z176,z2,z4,z38,z6]),(0,[z0,z1,z200,z4,z15,z6]),(0,[z0,z342,z2,z106,z4,z6])],[],[(0,[z0,z938,z2,z4,z5,z6]),(0,[z21,z1,z2,z148,z15,z6]),(0,[z1,z2,z4,z5,z62,z773])],[(0,[z129,z1,z63,z4,z15,z6]),(0,[z0,z1,z2,z939,z5,z6])],[(0,[z0,z1,z2,z940,z4,z6]),(0,[z941,z1,z2,z4,z5,z6]),(0,[z0,z110,z1,z4,z74,z6]),(0,[z0,z176,z2,z163,z38,z6])],[(0,[z0,z942,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z943,z6]),(0,[z21,z0,z1,z2,z163,z6]),(0,[z428,z0,z1,z2,z4,z188])]],
   [[(0,[z1,z837,z63,z4,z5,z6]),(0,[z0,z1,z2,z4,z944,z6]),(0,[z0,z1,z2,z4,z22,z341])],[(0,[z0,z1,z2,z945,z5,z6]),(0,[z0,z946,z1,z2,z4,z6]),(0,[z0,z1,z2,z5,z674,z83])],[(0,[z0,z9,z1,z290,z38,z6])],[(0,[z0,z96,z2,z4,z15,z6]),(0,[z0,z1,z2,z97,z15,z6]),(0,[z0,z528,z1,z2,z5,z83]),(0,[z0,z1,z2,z32,z244,z6]),(0,[z0,z90,z1,z2,z5,z83])],[(0,[z0,z1,z947,z4,z5,z6]),(0,[z84,z223,z2,z140,z5,z6]),(0,[z0,z1,z2,z4,z948,z6])],[(0,[z581,z1,z2,z148,z5,z6]),(0,[z0,z9,z210,z4,z279,z6]),(0,[z0,z2,z873,z11,z5,z6]),(0,[z0,z1,z2,z67,z26,z6])],[(0,[z0,z1,z2,z949,z5,z6]),(0,[z0,z1,z2,z4,z950,z6]),(0,[z0,z951,z258,z1,z4,z6]),(0,[z0,z1,z2,z952,z5,z6]),(0,[z0,z953,z1,z2,z4,z6]),(0,[z0,z176,z2,z4,z6,z536])],[(0,[z0,z1,z2,z4,z5,z954]),(0,[z0,z1,z2,z4,z955,z6])],[(0,[z0,z956,z1,z2,z5,z6]),(0,[z0,z1,z376,z2,z4,z15]),(0,[z20,z202,z41,z2,z4,z6]),(0,[z0,z41,z1,z2,z163,z6]),(0,[z0,z2,z4,z52,z415,z6]),(0,[z0,z1,z957,z4,z5,z6]),(0,[z0,z1,z2,z26,z591,z6])],[(0,[z0,z830,z1,z2,z4,z6])],[(0,[z0,z55,z2,z4,z15,z6]),(0,[z0,z1,z73,z2,z163,z6])],[(0,[z0,z156,z223,z2,z5,z6]),(0,[z0,z9,z379,z4,z5,z6]),(0,[z427,z0,z1,z2,z26,z6]),(1,[z0,z1,z4,z5,z958])],[(0,[z0,z1,z2,z4,z5,z959]),(0,[z0,z81,z1,z15,z16,z6]),(0,[z0,z1,z2,z37,z163,z6]),(0,[z0,z1,z2,z4,z6,z960])],[(0,[z0,z1,z2,z26,z318,z6]),(0,[z0,z1,z2,z4,z961,z6]),(0,[z0,z1,z572,z4,z38,z6])],[(0,[z0,z100,z1,z4,z38,z6]),(0,[z0,z136,z1,z2,z163,z6]),(0,[z0,z1,z2,z4,z6,z962])],[(0,[z0,z1,z963,z4,z5,z6]),(0,[z0,z100,z1,z2,z163,z6]),(0,[z0,z1,z26,z4,z243,z6]),(0,[z0,z1,z2,z4,z164,z6])]],
   [[(0,[z0,z1,z2,z964,z5,z6]),(0,[z20,z207,z1,z231,z4,z6]),(0,[z0,z965,z1,z4,z5,z6]),(0,[z863,z0,z1,z2,z97,z6]),(0,[z0,z2,z4,z127,z5,z6]),(0,[z0,z1,z2,z4,z966,z6]),(0,[z0,z237,z1,z2,z10,z6])],[(0,[z0,z1,z2,z4,z967,z6]),(0,[z1,z2,z4,z25,z748,z6]),(0,[z0,z1,z2,z4,z968,z6]),(0,[z0,z2,z4,z873,z5,z6]),(0,[z0,z246,z2,z4,z244,z6]),(0,[z0,z1,z2,z4,z969,z6])],[(0,[z202,z807,z2,z4,z5,z6]),(0,[z0,z970,z2,z4,z5,z6]),(0,[z0,z1,z2,z971,z5,z6]),(0,[z84,z1,z2,z26,z140,z6]),(0,[z20,z0,z292,z2,z4,z6]),(0,[z0,z110,z2,z4,z415,z6]),(0,[z0,z9,z397,z4,z5,z6]),(0,[z0,z2,z4,z52,z280,z6]),(0,[z0,z1,z4,z243,z38,z6]),(0,[z0,z110,z1,z2,z163,z6]),(0,[z0,z1,z2,z4,z5,z958])],[(0,[z207,z1,z231,z4,z15,z6]),(0,[z0,z96,z135,z4,z5,z6]),(0,[z0,z1,z135,z97,z5,z6])],[(0,[z0,z1,z2,z4,z972,z6]),(0,[z0,z1,z2,z4,z973,z6]),(0,[z0,z1,z2,z38,z6,z708])],[(0,[z20,z0,z258,z1,z4,z6]),(0,[z0,z1,z2,z974,z5,z6]),(0,[z0,z23,z1,z24,z5,z46])],[(0,[z0,z1,z975,z4,z5,z6]),(0,[z0,z976,z2,z4,z5,z6]),(0,[z0,z283,z1,z4,z977,z6])],[(0,[z0,z1,z2,z4,z978,z6]),(0,[z0,z1,z2,z979,z5,z6]),(0,[z20,z0,z413,z1,z4,z6]),(0,[z0,z1,z4,z6,z167,z962])],[(0,[z0,z980,z1,z2,z4,z5]),(1,[z1,z837,z4,z5,z6]),(0,[z0,z1,z2,z4,z981,z6]),(0,[z0,z982,z1,z4,z5,z6]),(0,[z0,z1,z301,z5,z6,z149]),(0,[z0,z246,z10,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z983]),(0,[z0,z1,z89,z4,z5,z958])],[(0,[z20,z0,z1,z2,z358,z6]),(0,[z0,z176,z2,z4,z15,z6]),(0,[z0,z1,z2,z163,z984,z6])],[(0,[z31,z1,z2,z4,z25,z6]),(0,[z0,z1,z985,z4,z5,z6])],[(0,[z0,z139,z2,z26,z4,z6]),(0,[z0,z43,z2,z5,z44,z149]),(0,[z0,z1,z2,z4,z986,z6]),(0,[z0,z17,z1,z2,z5,z83])],[(0,[z0,z1,z2,z4,z987,z6]),(0,[z0,z1,z988,z4,z5,z6]),(0,[z0,z1,z989,z2,z4,z6]),(0,[z201,z0,z729,z2,z4,z6]),(0,[z0,z1,z2,z60,z27,z6])],[(0,[z0,z1,z2,z27,z99,z362])],[(0,[z1,z2,z767,z140,z5,z6]),(0,[z1,z2,z4,z748,z5,z6]),(0,[z0,z990,z1,z2,z4,z6]),(0,[z0,z782,z2,z4,z38,z6]),(0,[z0,z265,z2,z26,z4,z6])],[(0,[z0,z292,z2,z4,z38,z6]),(0,[z0,z1,z89,z4,z5,z117]),(0,[z0,z1,z2,z26,z304,z6]),(0,[z0,z90,z1,z2,z82,z83])]],
   [[(0,[z0,z991,z156,z1,z2,z6]),(0,[z0,z110,z80,z2,z4,z6]),(0,[z0,z142,z2,z873,z5,z6]),(0,[z0,z23,z1,z76,z5,z46])],[(0,[z483,z0,z78,z1,z2,z5]),(0,[z0,z1,z2,z163,z25,z6]),(0,[z0,z1,z2,z4,z992,z6]),(0,[z0,z1,z2,z784,z38,z6])],[(0,[z0,z100,z139,z4,z5,z6]),(0,[z0,z9,z4,z38,z44,z6]),(0,[z0,z1,z2,z4,z993,z6]),(0,[z0,z994,z2,z4,z5,z6]),(0,[z0,z23,z1,z4,z5,z46]),(0,[z0,z1,z887,z26,z4,z6])],[(0,[z0,z1,z2,z4,z995,z6]),(0,[z0,z1,z985,z26,z4,z6]),(0,[z20,z0,z739,z2,z4,z6])],[(0,[z0,z1,z2,z4,z996,z6])],[(0,[z0,z1,z2,z4,z997,z6]),(0,[z0,z196,z2,z4,z15,z6]),(0,[z0,z1,z4,z45,z6,z167]),(0,[z0,z1,z2,z4,z998,z6])],[(0,[z0,z999,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z1000,z6]),(0,[z150,z292,z2,z4,z5,z141]),(0,[z0,z1,z2,z24,z38,z6]),(0,[z0,z1,z2,z32,z118,z113])],[(0,[z0,z1001,z258,z1,z4,z6]),(0,[z0,z1,z2,z163,z163,z6]),(0,[z0,z1,z2,z4,z1002,z6])],[(0,[z166,z41,z2,z4,z5,z6]),(0,[z84,z0,z1,z2,z163,z6]),(0,[z0,z1,z2,z4,z6,z1003]),(0,[z0,z1,z2,z4,z1004,z6]),(0,[z0,z1,z2,z4,z1005,z6])],[(0,[z0,z1,z2,z4,z1006,z5]),(0,[z129,z1,z63,z4,z248,z6]),(0,[z0,z292,z2,z4,z384,z6]),(0,[z0,z9,z193,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1007,z6]),(0,[z0,z1,z2,z4,z1008,z6])],[(0,[z0,z23,z1,z26,z4,z46])],[(0,[z20,z0,z1,z2,z305,z6]),(0,[z0,z1,z2,z4,z1009,z6]),(0,[z0,z81,z160,z16,z5,z6]),(0,[z0,z1,z2,z463,z4,z6])],[(0,[z0,z861,z210,z4,z5,z6]),(0,[z0,z100,z1,z4,z164,z6]),(0,[z0,z1,z2,z163,z11,z6]),(0,[z0,z176,z2,z163,z4,z6]),(0,[z0,z1,z2,z1010,z15,z6])],[(0,[z0,z1,z2,z163,z118,z6])],[(0,[z20,z0,z1,z2,z4,z1011])]],
   [[(0,[z0,z991,z1,z2,z4,z6]),(0,[z65,z1,z2,z4,z5,z62]),(0,[z0,z1,z26,z4,z6,z167])],[(0,[z21,z1,z2,z148,z147,z6]),(0,[z0,z1,z4,z243,z15,z6]),(0,[z0,z1,z301,z26,z4,z6]),(0,[z0,z905,z2,z4,z38,z6]),(0,[z0,z1,z2,z76,z38,z6])],[(0,[z0,z156,z252,z1,z5,z6]),(0,[z0,z1,z2,z4,z1012,z6]),(0,[z354,z1,z231,z4,z5,z6]),(0,[z0,z1,z1013,z4,z5,z6]),(0,[z0,z413,z1,z4,z279,z6]),(0,[z0,z100,z73,z4,z280,z6]),(0,[z0,z1014,z2,z4,z5,z6]),(0,[z0,z1,z2,z1015,z4,z6])],[(0,[z0,z1,z2,z4,z38,z6]),(0,[z0,z9,z1,z4,z88,z6]),(0,[z0,z1,z2,z119,z779,z6])],[(0,[z0,z1,z2,z4,z1016,z6]),(0,[z0,z96,z2,z602,z5,z6]),(0,[z0,z1,z2,z26,z6,z352]),(0,[z0,z1,z2,z4,z188,z137])],[(0,[z0,z246,z2,z4,z5,z6]),(0,[z0,z142,z9,z4,z38,z6]),(0,[z0,z1,z2,z4,z38,z341]),(0,[z0,z1,z2,z1017,z5,z6])],[(0,[z0,z1,z2,z1018,z4,z6])],[(0,[z0,z1,z2,z4,z5,z1019]),(0,[z0,z1,z2,z1020,z5,z6]),(0,[z7,z179,z1,z2,z4,z6]),(0,[z0,z29,z2,z4,z127,z6]),(0,[z0,z1,z2,z4,z1021,z6]),(0,[z0,z4,z127,z74,z38,z6]),(0,[z0,z1,z2,z163,z38,z6])],[(0,[z20,z0,z1,z376,z2,z4]),(0,[z202,z41,z2,z4,z38,z6]),(0,[z0,z1,z2,z26,z97,z6]),(0,[z20,z0,z1,z2,z6,z362])],[(0,[z378,z1,z63,z4,z5,z6]),(0,[z0,z1,z2,z26,z60,z6]),(0,[z0,z2,z4,z1022,z5,z6])],[(0,[z0,z1,z2,z4,z264,z6]),(0,[z150,z1,z2,z4,z335,z141]),(0,[z150,z1,z2,z4,z5,z773]),(0,[z0,z81,z1,z26,z164,z6]),(0,[z0,z1,z89,z4,z102,z117])],[(0,[z0,z1,z2,z4,z393,z6]),(0,[z0,z1,z2,z32,z38,z118])],[(0,[z1023,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z32,z26,z83])],[(0,[z0,z47,z78,z1,z2,z6]),(0,[z0,z1,z2,z4,z1024,z6]),(0,[z20,z0,z136,z2,z28,z6]),(0,[z0,z1,z2,z4,z1025,z6])],[(0,[z0,z9,z210,z4,z415,z6]),(0,[z0,z1,z2,z28,z163,z6]),(0,[z0,z246,z2,z26,z4,z6]),(0,[z123,z0,z246,z2,z4,z6]),(0,[z0,z1,z235,z2,z163,z6])],[(0,[z0,z1,z2,z4,z1026,z6]),(0,[z1027,z0,z1,z2,z4,z6]),(0,[z0,z2,z4,z5,z44,z105])]],
   [[(0,[z0,z1,z2,z602,z5,z6]),(0,[z0,z1028,z1,z2,z4,z6]),(0,[z0,z1,z2,z67,z15,z6]),(0,[z0,z1,z2,z26,z4,z527]),(0,[z0,z246,z2,z5,z6,z83]),(0,[z0,z1,z68,z4,z799,z6]),(0,[z0,z1,z2,z5,z6,z925])],[(0,[z0,z1,z4,z5,z6,z1029]),(0,[z0,z1,z1030,z4,z5,z6]),(0,[z0,z785,z2,z4,z15,z6]),(0,[z820,z0,z1,z2,z4,z6])],[(0,[z0,z1,z1031,z2,z4,z6]),(0,[z0,z1032,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z776,z6]),(0,[z0,z933,z2,z4,z38,z6]),(0,[z0,z1033,z2,z4,z15,z6])],[(0,[z150,z1,z2,z26,z4,z141]),(0,[z0,z9,z4,z127,z38,z6]),(0,[z0,z1,z2,z163,z6,z536])],[(0,[z0,z1,z2,z1034,z4,z6]),(0,[z0,z9,z4,z5,z6,z327]),(0,[z0,z142,z69,z2,z11,z6]),(0,[z0,z110,z2,z4,z507,z6])],[(0,[z0,z1,z2,z5,z6,z1035]),(0,[z0,z142,z283,z11,z5,z6]),(0,[z0,z1,z331,z4,z5,z117])],[(0,[z0,z1,z2,z4,z884,z6]),(0,[z0,z1,z4,z5,z117,z958])],[(0,[z0,z283,z28,z4,z5,z6]),(0,[z0,z1,z2,z38,z6,z149])],[(0,[z0,z9,z4,z5,z6,z167]),(0,[z0,z1,z2,z1036,z4,z6])],[(0,[z0,z1,z2,z4,z1037,z6]),(0,[z20,z0,z1,z2,z12,z6]),(0,[z0,z1,z235,z10,z26,z6])],[(0,[z20,z0,z78,z1,z2,z6]),(0,[z41,z807,z2,z4,z5,z6]),(0,[z202,z0,z1,z2,z163,z6]),(0,[z0,z1,z2,z4,z1038,z6]),(0,[z0,z1,z1039,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z1040]),(0,[z1041,z0,z1,z2,z4,z6]),(0,[z0,z1,z4,z1042,z5,z6]),(0,[z20,z0,z1,z2,z76,z6]),(0,[z20,z0,z782,z2,z4,z6])],[(0,[z0,z1,z2,z4,z1043,z6]),(0,[z0,z1,z2,z26,z602,z6]),(0,[z0,z1,z2,z37,z4,z6]),(0,[z133,z0,z1,z4,z15,z6]),(0,[z20,z0,z1,z2,z290,z6]),(0,[z0,z219,z2,z4,z507,z6])],[(0,[z0,z1,z2,z26,z35,z6]),(0,[z0,z1,z2,z828,z602,z6]),(0,[z0,z1,z2,z163,z398,z6])],[(0,[z0,z1,z2,z4,z5,z1044]),(0,[z0,z1,z2,z4,z924,z6]),(0,[z0,z1,z2,z903,z6,z149])],[(0,[z0,z1045,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1046,z6]),(0,[z0,z110,z2,z4,z441,z6]),(0,[z0,z1,z2,z4,z22,z527])],[(0,[z84,z196,z2,z140,z5,z6]),(0,[z0,z1,z2,z278,z6,z83])]],
   [[(0,[z0,z1,z4,z5,z303,z46]),(0,[z0,z1,z2,z76,z15,z6]),(0,[z0,z2,z4,z15,z6,z327])],[(0,[z483,z0,z252,z1,z4,z5]),(0,[z1047,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z1048,z6]),(0,[z0,z9,z1,z4,z181,z6]),(0,[z0,z142,z2,z11,z38,z6]),(0,[z0,z1,z2,z4,z1049,z6]),(0,[z0,z1,z2,z1050,z5,z6])],[(0,[z0,z1,z2,z4,z15,z6]),(0,[z1,z2,z4,z5,z6,z773]),(0,[z0,z1051,z1,z2,z163,z6]),(0,[z0,z1,z2,z4,z1052,z6])],[(0,[z1053,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z1054,z5,z6]),(0,[z0,z1,z2,z1055,z4,z6]),(0,[z20,z0,z223,z2,z4,z6]),(0,[z523,z0,z176,z2,z4,z6]),(0,[z0,z1,z134,z2,z4,z453])],[(0,[z0,z1,z2,z4,z1056,z6]),(0,[z0,z156,z47,z1,z2,z6]),(0,[z0,z1,z626,z2,z4,z137]),(0,[z0,z1,z4,z5,z6,z958])],[(0,[z0,z100,z1,z163,z38,z6]),(0,[z0,z1,z2,z4,z1057,z6]),(0,[z0,z813,z2,z4,z15,z6])],[(0,[z7,z1,z2,z4,z115,z6]),(0,[z150,z0,z1,z2,z163,z6]),(0,[z0,z1,z2,z163,z164,z6]),(0,[z0,z176,z2,z290,z5,z6])],[(0,[z165,z658,z1,z2,z4,z6]),(0,[z0,z1,z2,z1058,z5,z6]),(0,[z0,z1,z2,z4,z1059,z6])],[(0,[z20,z0,z1,z2,z24,z6]),(0,[z0,z1,z2,z76,z26,z6])],[(0,[z0,z100,z1,z4,z248,z6])],[(0,[z0,z1,z2,z1060,z4,z6]),(0,[z0,z615,z1,z4,z38,z6]),(0,[z20,z0,z1,z4,z74,z6]),(0,[z0,z1,z2,z1018,z67,z6]),(0,[z0,z1,z2,z32,z15,z118])],[(0,[z483,z0,z43,z2,z4,z5])],[(0,[z0,z43,z2,z4,z45,z44]),(0,[z0,z1,z2,z163,z44,z6]),(0,[z0,z1,z2,z4,z389,z421]),(0,[z20,z0,z1,z2,z435,z6])],[(0,[z0,z1,z2,z4,z1061,z6]),(0,[z0,z1,z2,z4,z1062,z6]),(0,[z0,z1,z2,z60,z27,z99])],[(0,[z0,z139,z2,z4,z38,z6]),(0,[z0,z369,z1,z2,z5,z83]),(0,[z0,z1,z2,z119,z181,z6]),(0,[z0,z1,z666,z2,z26,z6]),(0,[z0,z1,z2,z60,z38,z6]),(0,[z0,z1,z2,z4,z1063,z6])],[(0,[z0,z1,z624,z2,z26,z6]),(0,[z0,z1,z2,z1064,z5,z6]),(0,[z0,z1,z2,z4,z1065,z6]),(0,[z0,z1,z2,z4,z1066,z6]),(0,[z523,z0,z1,z2,z163,z6]),(0,[z1067,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z1068,z6]),(0,[z0,z1,z2,z4,z1069,z6]),(0,[z0,z1,z2,z1070,z4,z6]),(0,[z0,z1,z134,z2,z4,z914])],[(0,[z0,z1,z2,z4,z1071,z6]),(0,[z0,z265,z2,z4,z38,z6]),(0,[z0,z1,z4,z15,z586,z6])],[(0,[z91,z120,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1072,z6]),(0,[z0,z1,z135,z4,z5,z6]),(0,[z0,z1,z587,z4,z38,z6]),(0,[z0,z1,z1073,z2,z4,z6]),(0,[z1074,z1,z2,z4,z5,z6]),(0,[z20,z0,z176,z2,z4,z6]),(0,[z0,z1,z2,z32,z26,z118]),(0,[z0,z1,z134,z2,z4,z137])],[(0,[z0,z1,z134,z2,z4,z510]),(0,[z0,z1,z2,z4,z6,z1075]),(0,[z0,z660,z1,z2,z26,z6]),(0,[z0,z1,z2,z32,z163,z6])],[(0,[z0,z1,z2,z1076,z5,z6]),(0,[z0,z1,z4,z5,z6,z1077]),(0,[z0,z1,z2,z4,z6,z1078]),(0,[z0,z1079,z2,z4,z5,z6]),(0,[z0,z2,z4,z1080,z5,z6])],[(0,[z0,z156,z1,z2,z5,z6])],[(0,[z207,z0,z1,z2,z163,z6]),(0,[z0,z1,z2,z163,z4,z6]),(1,[z0,z1,z2,z26,z341]),(0,[z0,z176,z2,z4,z101,z6])],[(0,[z0,z136,z2,z390,z5,z6]),(0,[z0,z1,z381,z2,z4,z6]),(0,[z0,z69,z1,z2,z4,z6])],[(0,[z150,z539,z1,z2,z4,z5]),(0,[z0,z1,z2,z163,z6,z141]),(0,[z0,z1,z988,z26,z4,z6])],[],[(0,[z0,z1,z2,z4,z5,z1081]),(0,[z0,z1,z2,z1082,z5,z6]),(0,[z0,z1,z2,z4,z185,z6]),(0,[z0,z1,z2,z37,z6,z83])],[(0,[z91,z120,z2,z26,z4,z6]),(0,[z207,z1,z231,z4,z348,z6]),(0,[z0,z1,z135,z26,z4,z6]),(0,[z0,z1,z89,z26,z4,z117])],[(0,[z1083,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z1084,z5,z6]),(0,[z0,z142,z243,z11,z5,z6]),(0,[z0,z1,z235,z2,z164,z6]),(0,[z20,z0,z1,z2,z4,z714])],[(0,[z1041,z0,z1,z2,z67,z6]),(0,[z0,z500,z1,z2,z26,z6]),(0,[z0,z1,z2,z4,z1085,z6]),(0,[z20,z0,z1,z2,z163,z6]),(0,[z0,z1,z2,z119,z82,z6])],[(0,[z0,z258,z78,z1,z5,z6]),(0,[z0,z29,z549,z2,z4,z6]),(0,[z0,z292,z2,z602,z5,z6]),(0,[z0,z1,z2,z26,z6,z341]),(0,[z0,z1,z2,z1086,z5,z6]),(0,[z0,z1,z2,z37,z187,z6]),(0,[z0,z1,z2,z482,z26,z6])]],
   [[(0,[z0,z78,z1,z2,z5,z6]),(0,[z0,z1,z2,z1087,z4,z6]),(0,[z0,z1,z1088,z2,z4,z6]),(0,[z0,z1,z2,z4,z1089,z6]),(0,[z0,z1,z1090,z4,z5,z6]),(0,[z0,z142,z2,z11,z15,z6])],[(0,[z0,z1091,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z1092,z6]),(0,[z0,z1,z4,z5,z6,z1093]),(0,[z0,z1,z2,z198,z26,z6]),(0,[z0,z1,z2,z1042,z5,z6]),(0,[z0,z81,z1,z2,z244,z6]),(0,[z20,z0,z81,z1,z16,z6]),(0,[z0,z756,z2,z4,z15,z6])],[(0,[z1094,z1,z2,z4,z5,z6]),(0,[z0,z1095,z1,z2,z4,z6])],[(0,[z0,z1096,z2,z4,z5,z6]),(0,[z0,z1,z2,z1097,z5,z6]),(0,[z0,z1098,z1,z2,z5,z6]),(0,[z0,z1,z1099,z2,z4,z38])],[(0,[z483,z0,z156,z1,z2,z5]),(0,[z0,z1,z2,z4,z1100,z6]),(0,[z0,z1,z2,z4,z1101,z6]),(0,[z0,z136,z2,z28,z432,z6]),(0,[z0,z1,z301,z4,z38,z6]),(0,[z0,z1,z2,z4,z778,z6]),(0,[z0,z1,z2,z4,z6,z1102])],[(0,[z0,z1,z235,z2,z26,z6])],[(0,[z84,z406,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z1103,z6])],[(0,[z0,z1,z2,z4,z5,z1104]),(0,[z1105,z0,z1,z2,z163,z6]),(0,[z0,z1,z2,z4,z1106,z6])],[(0,[z0,z1,z2,z4,z1107,z6]),(0,[z21,z1,z2,z26,z148,z6]),(0,[z1108,z0,z1,z2,z4,z6]),(0,[z0,z2,z4,z5,z6,z1109]),(0,[z0,z1,z2,z76,z226,z6])],[(0,[z0,z1,z2,z4,z5,z1110]),(0,[z0,z1,z2,z4,z1111,z6]),(0,[z0,z1,z2,z4,z1112,z6]),(0,[z0,z2,z4,z1113,z5,z6]),(0,[z0,z81,z1,z26,z16,z6]),(0,[z0,z448,z1,z4,z15,z6])],[(0,[z0,z43,z2,z67,z5,z44]),(0,[z0,z1,z2,z4,z226,z6])],[(0,[z0,z1,z2,z1114,z5,z6]),(0,[z0,z142,z283,z4,z5,z6]),(0,[z1115,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z766])],[(0,[z0,z258,z1,z4,z38,z6]),(0,[z84,z1,z2,z140,z5,z6]),(0,[z0,z1,z496,z4,z38,z6]),(0,[z0,z1,z2,z1116,z4,z6]),(0,[z65,z1,z2,z4,z38,z62]),(0,[z0,z43,z4,z5,z44,z167]),(0,[z0,z1,z2,z904,z5,z6])],[(0,[z0,z1,z68,z290,z38,z6])],[(0,[z0,z1,z2,z4,z248,z6]),(0,[z0,z1,z2,z4,z1117,z6]),(0,[z0,z1,z1118,z4,z5,z6]),(0,[z0,z1,z135,z4,z852,z6]),(0,[z0,z283,z1,z4,z5,z6]),(0,[z0,z110,z2,z4,z30,z6]),(0,[z0,z1,z2,z665,z26,z6]),(0,[z0,z1,z503,z4,z38,z6]),(0,[z0,z1119,z2,z4,z5,z6]),(0,[z0,z128,z1,z2,z4,z453])],[(0,[z0,z1,z2,z4,z1120,z6]),(0,[z1,z2,z4,z5,z6,z1121]),(0,[z0,z1,z2,z5,z118,z870])]],
   [[(0,[z0,z1,z2,z917,z24,z6]),(0,[z0,z1,z2,z26,z4,z1104])],[(0,[z0,z1122,z223,z4,z5,z6]),(0,[z0,z292,z2,z4,z15,z6]),(0,[z0,z1,z2,z4,z1123,z6])],[(0,[z0,z252,z162,z1,z4,z6]),(0,[z0,z1,z2,z26,z537,z6]),(0,[z0,z1,z2,z1124,z5,z6]),(0,[z0,z1,z2,z4,z1125,z6]),(0,[z20,z0,z23,z1,z4,z46])],[(0,[z0,z142,z223,z2,z5,z6]),(0,[z0,z1,z2,z602,z335,z6]),(0,[z0,z176,z2,z4,z52,z6]),(0,[z0,z1,z2,z4,z38,z527]),(0,[z0,z1,z2,z4,z27,z316]),(0,[z0,z1126,z2,z4,z5,z6])],[(0,[z483,z0,z1,z2,z4,z5]),(0,[z0,z1,z1127,z2,z4,z6]),(0,[z1128,z0,z1,z2,z4,z6]),(0,[z0,z100,z1,z163,z4,z6]),(0,[z0,z1129,z2,z4,z5,z6]),(0,[z0,z1,z235,z10,z15,z6]),(0,[z0,z1,z2,z4,z27,z421])],[(0,[z0,z1,z2,z4,z1130,z6]),(0,[z133,z0,z1,z4,z279,z6]),(0,[z0,z1,z2,z163,z6,z83])],[(0,[z0,z1,z2,z4,z1131,z6]),(0,[z0,z1,z2,z1132,z5,z6]),(0,[z150,z1,z2,z4,z38,z141]),(0,[z0,z1,z2,z76,z272,z6])],[(0,[z0,z1,z4,z1133,z5,z6]),(0,[z0,z1134,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z147,z6]),(0,[z0,z283,z1,z26,z4,z6])],[(0,[z0,z1,z2,z4,z272,z6]),(0,[z0,z1,z2,z24,z15,z6]),(0,[z0,z1,z2,z4,z1135,z6])],[(0,[z0,z1,z1136,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1137])],[(0,[z0,z4,z15,z127,z38,z6])],[(0,[z0,z1,z2,z4,z885,z5]),(0,[z0,z1,z2,z4,z1138,z6]),(0,[z0,z1,z4,z5,z6,z1139]),(0,[z0,z1,z2,z4,z1140,z6]),(0,[z0,z1,z544,z4,z38,z6])],[(0,[z0,z1,z2,z4,z1141,z6]),(0,[z0,z1,z2,z4,z776,z6]),(0,[z0,z43,z2,z4,z5,z44]),(0,[z0,z1,z235,z2,z37,z6]),(0,[z0,z176,z1,z2,z163,z6]),(0,[z0,z1,z2,z4,z6,z1142])],[(0,[z0,z2,z4,z5,z6,z1143]),(0,[z7,z1,z2,z4,z39,z6]),(0,[z150,z1,z2,z4,z264,z141])],[(0,[z0,z1,z2,z1144,z4,z6]),(0,[z1,z837,z2,z4,z5,z6]),(0,[z0,z81,z1,z2,z163,z6])],[(0,[z7,z0,z1,z2,z60,z6]),(0,[z0,z9,z680,z4,z5,z6]),(0,[z0,z1,z2,z290,z5,z6])]],
   [[(0,[z0,z1,z2,z1145,z5,z6]),(0,[z0,z258,z139,z4,z5,z6]),(0,[z150,z1,z2,z4,z384,z141])],[(0,[z326,z41,z2,z4,z5,z6]),(0,[z0,z292,z135,z4,z5,z6]),(0,[z0,z1,z2,z4,z1146,z6])],[(0,[z0,z1,z627,z4,z38,z6]),(0,[z20,z64,z0,z2,z4,z87]),(0,[z0,z1,z301,z4,z1049,z6]),(0,[z0,z90,z1,z2,z38,z83]),(0,[z0,z1,z2,z24,z5,z117]),(0,[z0,z1,z2,z32,z164,z6])],[(0,[z0,z1,z3,z4,z38,z6]),(0,[z0,z2,z4,z5,z880,z87]),(0,[z0,z1,z2,z163,z1147,z6]),(0,[z20,z0,z2,z4,z6,z327])],[(0,[z0,z495,z2,z4,z30,z6]),(0,[z0,z1148,z1,z2,z163,z6])],[(0,[z0,z43,z2,z26,z4,z44]),(0,[z0,z1,z2,z163,z16,z6]),(0,[z0,z1,z2,z4,z1149,z6]),(0,[z0,z1,z2,z952,z38,z6]),(0,[z0,z1,z145,z4,z38,z6])],[(0,[z0,z283,z41,z4,z5,z6]),(0,[z1,z2,z4,z38,z6,z901]),(0,[z0,z1,z2,z26,z4,z1040])],[(0,[z0,z1,z2,z4,z15,z341]),(0,[z133,z0,z1,z4,z799,z6]),(0,[z0,z1,z2,z112,z4,z316])],[(0,[z0,z2,z26,z4,z6,z327])],[(0,[z0,z73,z861,z4,z5,z6]),(0,[z0,z1,z2,z163,z15,z6]),(0,[z0,z1,z2,z163,z6,z46])],[(0,[z202,z41,z2,z4,z15,z6]),(0,[z0,z1150,z2,z4,z5,z6]),(0,[z0,z1,z2,z197,z6,z83]),(0,[z165,z0,z176,z2,z4,z6]),(0,[z0,z490,z1,z4,z38,z6]),(0,[z0,z237,z1,z2,z119,z6]),(0,[z0,z1,z2,z32,z26,z6]),(0,[z0,z1,z4,z1151,z5,z6])],[(0,[z0,z258,z1,z4,z15,z6]),(0,[z0,z1,z2,z26,z49,z6]),(0,[z0,z236,z1,z2,z163,z6]),(0,[z0,z1,z430,z2,z26,z6]),(0,[z0,z1,z2,z4,z6,z113])],[(0,[z0,z1,z4,z58,z38,z6]),(0,[z0,z1,z2,z469,z26,z6])],[(0,[z20,z0,z156,z1,z2,z6]),(0,[z0,z1152,z223,z4,z5,z6]),(0,[z0,z1,z2,z1050,z38,z6])],[(0,[z0,z951,z1,z2,z4,z6]),(0,[z0,z1,z2,z1153,z5,z6]),(0,[z0,z1154,z1,z2,z4,z6]),(0,[z201,z0,z2,z4,z127,z6])],[(0,[z0,z1,z2,z5,z6,z1155]),(0,[z165,z1,z2,z4,z748,z6]),(0,[z0,z1,z2,z4,z1156,z6]),(0,[z0,z2,z4,z127,z38,z6])]],
   [[(0,[z0,z47,z1,z2,z4,z6]),(0,[z0,z1,z861,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z327]),(0,[z0,z413,z29,z4,z52,z6])],[(0,[z1157,z0,z1,z2,z4,z6]),(0,[z20,z0,z43,z2,z4,z44])],[(0,[z0,z252,z1,z376,z4,z5]),(0,[z0,z142,z2,z195,z11,z6])],[(0,[z0,z1158,z2,z4,z5,z6]),(0,[z1159,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z1160,z6])],[(0,[z0,z1,z1161,z4,z5,z6]),(0,[z0,z176,z100,z4,z38,z6]),(0,[z0,z1,z2,z4,z468,z137]),(0,[z0,z1,z2,z4,z1162,z6]),(0,[z0,z1,z235,z2,z884,z6]),(0,[z0,z2,z4,z1022,z164,z6])],[(0,[z0,z1,z135,z4,z335,z6]),(0,[z0,z1,z89,z4,z5,z158]),(0,[z0,z1,z89,z2,z904,z6]),(0,[z20,z0,z1,z2,z26,z6])],[(0,[z0,z1,z2,z4,z1163,z6]),(0,[z165,z0,z1,z2,z163,z6]),(0,[z0,z1,z4,z38,z6,z513])],[(0,[z0,z1,z2,z4,z1164,z6]),(0,[z0,z1,z2,z1165,z5,z6]),(0,[z0,z1,z2,z4,z1166,z6])],[(0,[z0,z1,z2,z4,z1167,z6]),(0,[z644,z0,z1,z2,z26,z6]),(0,[z0,z1,z2,z4,z1168,z6]),(0,[z0,z1,z4,z38,z6,z167]),(0,[z0,z1,z2,z5,z6,z1169])],[(0,[z0,z1,z2,z4,z1170,z6]),(0,[z523,z1,z2,z4,z218,z6])],[(0,[z0,z1,z1171,z4,z5,z6]),(0,[z0,z1,z2,z4,z348,z6]),(0,[z0,z100,z1,z4,z280,z6]),(0,[z1172,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z1173,z6]),(0,[z0,z1174,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z686,z6]),(0,[z0,z1,z2,z4,z1175,z6]),(0,[z1067,z1,z2,z4,z38,z6])],[(0,[z0,z1,z2,z4,z5,z1176]),(0,[z0,z81,z1,z4,z164,z6])],[(0,[z20,z0,z1,z2,z4,z6]),(0,[z91,z162,z120,z2,z4,z6]),(0,[z0,z1,z2,z4,z1177,z6]),(0,[z0,z1,z2,z4,z1178,z6]),(0,[z165,z1,z2,z4,z218,z6]),(0,[z0,z136,z2,z28,z570,z6]),(0,[z0,z1,z2,z4,z1179,z6]),(0,[z0,z1,z2,z4,z1180,z6]),(0,[z0,z4,z5,z6,z327,z167]),(0,[z0,z1,z477,z4,z15,z6])],[(0,[z0,z1,z89,z4,z38,z117]),(0,[z0,z1,z555,z4,z15,z6]),(0,[z1181,z0,z1,z2,z4,z6]),(0,[z0,z1,z1182,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z914])],[(1,[z0,z100,z1,z163,z6]),(0,[z0,z81,z1,z16,z181,z6])]],
   [[(0,[z0,z1,z2,z24,z226,z6])],[(0,[z0,z1183,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z1184,z6]),(0,[z0,z176,z4,z15,z38,z6]),(0,[z0,z23,z1,z4,z38,z46]),(0,[z0,z2,z4,z909,z6,z327])],[(0,[z807,z120,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1185,z6]),(0,[z0,z1,z2,z4,z6,z1186]),(0,[z0,z1,z1042,z16,z5,z6])],[(0,[z0,z1,z2,z4,z1187,z6]),(0,[z0,z1,z2,z4,z1188,z6]),(0,[z0,z1,z2,z4,z1189,z6]),(0,[z0,z1,z2,z4,z1190,z6])],[(0,[z0,z2,z4,z5,z722,z6])],[(0,[z0,z1,z2,z4,z6,z1191]),(0,[z0,z1,z2,z4,z195,z6]),(0,[z0,z1,z2,z629,z26,z6]),(0,[z0,z1,z2,z26,z4,z1176])],[(0,[z84,z20,z1,z2,z140,z6]),(0,[z0,z1,z2,z4,z197,z6]),(0,[z0,z1,z37,z4,z164,z6])],[(0,[z0,z1192,z2,z4,z5,z6]),(0,[z0,z1193,z2,z4,z5,z6]),(0,[z0,z1,z2,z163,z6,z1194]),(0,[z0,z1,z186,z2,z4,z137]),(0,[z0,z1,z2,z1195,z76,z6]),(0,[z0,z1,z1182,z26,z4,z6]),(0,[z0,z1,z2,z5,z870,z83])],[(0,[z0,z1196,z1,z2,z4,z6]),(0,[z0,z1,z135,z4,z384,z6]),(0,[z0,z1,z2,z26,z181,z6]),(0,[z0,z246,z2,z32,z5,z6])],[(0,[z0,z1,z4,z1197,z5,z6]),(0,[z0,z1,z2,z1198,z5,z6]),(0,[z0,z23,z1,z2,z163,z6]),(0,[z0,z1,z2,z163,z214,z6]),(0,[z0,z90,z1,z2,z26,z83]),(0,[z0,z1,z2,z32,z5,z316])],[(0,[z0,z1,z2,z163,z148,z6]),(0,[z150,z1,z381,z2,z4,z141]),(0,[z0,z1,z2,z4,z1199,z6]),(0,[z0,z1,z2,z244,z6,z83]),(0,[z599,z0,z368,z2,z4,z6])],[(0,[z91,z376,z120,z2,z4,z5]),(0,[z0,z1,z2,z26,z517,z6]),(0,[z0,z1,z2,z1200,z5,z6])],[(0,[z0,z1,z2,z4,z769,z6]),(0,[z1201,z0,z1,z2,z4,z6])],[(0,[z20,z0,z252,z1,z4,z6]),(0,[z0,z1,z2,z4,z1202,z6]),(0,[z0,z1203,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z1204,z6]),(0,[z7,z1,z418,z2,z4,z6]),(0,[z0,z96,z425,z4,z5,z6]),(0,[z0,z1,z425,z97,z5,z6]),(0,[z0,z1,z2,z1205,z4,z6]),(0,[z0,z81,z1,z2,z164,z6]),(0,[z0,z1206,z1,z2,z4,z6])],[(0,[z0,z1,z2,z26,z395,z6]),(0,[z0,z1,z2,z24,z272,z6]),(0,[z20,z0,z1,z2,z6,z217])],[(0,[z0,z1001,z1,z2,z4,z6]),(0,[z0,z1,z2,z616,z26,z6])]],
   [[(0,[z0,z139,z2,z4,z15,z6]),(0,[z0,z100,z4,z199,z5,z6]),(0,[z0,z1,z2,z163,z52,z6]),(0,[z0,z1,z2,z60,z15,z6])],[(0,[z0,z1,z2,z4,z5,z1207]),(0,[z0,z1208,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1209,z6]),(0,[z0,z1014,z2,z4,z38,z6])],[],[(0,[z201,z0,z100,z1,z4,z6]),(0,[z0,z73,z4,z420,z5,z6]),(0,[z0,z2,z4,z5,z6,z880]),(0,[z0,z265,z2,z4,z15,z6])],[(0,[z483,z0,z47,z1,z2,z4]),(0,[z0,z1,z2,z4,z6,z1210]),(0,[z0,z246,z2,z4,z38,z6])],[(0,[z0,z1,z2,z4,z5,z1211]),(0,[z0,z1,z2,z4,z1212,z6]),(0,[z0,z713,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z1213,z6])],[(0,[z0,z252,z1,z4,z5,z6]),(0,[z483,z0,z2,z4,z5,z87])],[(0,[z0,z1,z1214,z4,z5,z6])],[(0,[z0,z1,z2,z26,z556,z6])],[(0,[z0,z1,z2,z63,z163,z6]),(0,[z0,z81,z1,z463,z4,z6]),(0,[z0,z1,z2,z4,z1215,z6])],[(0,[z0,z1,z2,z4,z1216,z6]),(0,[z123,z0,z81,z1,z16,z6])],[(0,[z0,z1,z2,z1217,z4,z6]),(0,[z0,z1,z2,z1218,z5,z6]),(0,[z0,z498,z1,z4,z38,z6]),(0,[z0,z1,z2,z290,z163,z6]),(0,[z0,z238,z2,z4,z293,z6]),(0,[z0,z1,z2,z15,z6,z362]),(0,[z0,z1,z2,z4,z5,z870])],[(0,[z0,z1,z2,z1219,z5,z6]),(0,[z0,z1,z2,z767,z5,z6]),(0,[z0,z2,z4,z5,z6,z1220]),(0,[z0,z9,z176,z4,z38,z6]),(0,[z0,z1,z2,z1221,z5,z6]),(0,[z0,z1,z2,z4,z276,z6])],[(0,[z0,z9,z1,z4,z5,z341]),(0,[z0,z100,z73,z4,z183,z6]),(0,[z0,z43,z301,z4,z5,z44]),(0,[z0,z1,z2,z1222,z163,z6]),(0,[z0,z1,z145,z2,z26,z6])],[],[(0,[z0,z252,z1,z26,z4,z6]),(0,[z0,z1,z2,z1223,z5,z6]),(0,[z0,z1224,z1,z4,z5,z6]),(0,[z0,z9,z662,z4,z5,z6]),(0,[z20,z129,z1,z63,z4,z6]),(0,[z0,z1,z2,z4,z1225,z6]),(0,[z0,z1,z2,z602,z38,z6]),(0,[z0,z1,z2,z4,z279,z6]),(0,[z0,z1,z2,z4,z280,z6]),(0,[z0,z176,z2,z4,z415,z6]),(0,[z0,z9,z1,z163,z5,z6]),(0,[z0,z1,z2,z4,z1226,z6]),(0,[z0,z1,z2,z26,z6,z18])]],
   [[(0,[z483,z0,z1,z2,z4,z15]),(0,[z0,z1,z2,z163,z62,z6]),(0,[z0,z23,z1,z4,z15,z46])],[(0,[z0,z1,z2,z4,z6,z1227]),(0,[z0,z1,z4,z279,z38,z6]),(0,[z0,z1,z2,z16,z5,z341]),(0,[z1,z2,z4,z5,z6,z1228]),(0,[z0,z1,z2,z119,z163,z6]),(0,[z0,z1,z2,z4,z1229,z6])],[(0,[z1230,z0,z1,z2,z4,z6]),(0,[z20,z0,z1,z135,z4,z6]),(0,[z0,z2,z4,z5,z6,z1231]),(0,[z0,z1,z2,z544,z5,z83])],[(0,[z0,z136,z444,z2,z5,z6]),(0,[z20,z0,z100,z73,z4,z6])],[(0,[z0,z1,z231,z2,z163,z6]),(0,[z0,z1,z2,z26,z524,z6]),(0,[z0,z2,z163,z127,z5,z6])],[(0,[z0,z1,z2,z4,z1232,z6]),(0,[z0,z1,z2,z570,z6,z83]),(0,[z0,z2,z28,z873,z5,z6]),(0,[z0,z1,z2,z163,z117,z6]),(0,[z0,z1233,z1,z2,z163,z6]),(1,[z0,z1,z2,z5,z870])],[(0,[z150,z1,z2,z602,z5,z141]),(0,[z0,z1,z2,z4,z1234,z6]),(0,[z0,z1,z301,z4,z15,z6])],[(0,[z207,z1,z837,z4,z5,z6]),(0,[z0,z1,z4,z15,z74,z6]),(0,[z0,z1,z26,z4,z853,z6])],[(0,[z0,z43,z2,z4,z38,z44])],[(0,[z0,z1235,z2,z4,z5,z6]),(0,[z0,z1,z2,z602,z384,z6]),(0,[z0,z1,z2,z4,z1236,z6])],[(0,[z207,z55,z231,z4,z5,z6]),(0,[z0,z9,z210,z4,z5,z6]),(0,[z0,z1,z2,z119,z5,z341]),(0,[z0,z246,z81,z16,z5,z6]),(1,[z0,z1,z4,z799,z6]),(0,[z0,z23,z1,z4,z5,z958])],[(0,[z0,z1,z2,z4,z1237,z6]),(0,[z0,z1122,z1,z4,z5,z6]),(0,[z0,z283,z69,z1,z4,z6]),(0,[z0,z1,z2,z4,z6,z1238]),(1,[z0,z1,z2,z904,z6])],[(0,[z0,z29,z2,z4,z776,z6]),(0,[z0,z1,z2,z753,z6,z83])],[(0,[z0,z1,z2,z4,z1239,z6]),(0,[z0,z729,z2,z4,z5,z6])],[(0,[z65,z1,z2,z4,z15,z62]),(0,[z0,z9,z1,z4,z840,z6]),(0,[z0,z1,z2,z1240,z4,z6])],[(0,[z21,z308,z1,z2,z5,z6]),(0,[z0,z1,z2,z26,z255,z6])]],
   [[(0,[z84,z1,z2,z197,z140,z6]),(0,[z0,z9,z28,z4,z38,z6]),(0,[z0,z1241,z1,z2,z4,z6]),(0,[z0,z43,z2,z4,z5,z880]),(0,[z0,z90,z1,z2,z163,z6]),(0,[z0,z2,z290,z127,z5,z6]),(0,[z0,z237,z1,z486,z2,z6])],[(0,[z0,z1,z2,z4,z799,z6]),(0,[z0,z1,z2,z4,z1242,z6])],[(0,[z64,z0,z2,z4,z5,z880]),(0,[z0,z1,z2,z1054,z38,z6]),(0,[z271,z0,z1,z2,z163,z6]),(0,[z0,z1,z4,z38,z6,z656])],[(0,[z0,z1,z2,z4,z5,z1011]),(0,[z568,z0,z1,z4,z15,z6]),(0,[z0,z9,z210,z26,z4,z6]),(0,[z0,z246,z2,z4,z15,z6])],[(0,[z0,z9,z81,z1,z26,z6])],[(0,[z0,z43,z2,z4,z5,z479]),(0,[z0,z1,z425,z4,z751,z6]),(0,[z0,z342,z2,z4,z52,z6]),(0,[z0,z1,z2,z4,z15,z527]),(0,[z0,z176,z2,z290,z38,z6])],[(0,[z0,z156,z136,z2,z5,z6]),(0,[z20,z0,z142,z2,z11,z6]),(0,[z0,z1,z2,z163,z101,z6]),(0,[z0,z1,z2,z1058,z38,z6]),(0,[z0,z1,z4,z94,z38,z6])],[(0,[z0,z1,z2,z4,z832,z6]),(0,[z0,z1,z2,z1243,z5,z6]),(0,[z0,z1,z2,z4,z6,z1244]),(0,[z150,z20,z1,z2,z4,z141]),(0,[z1245,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z161,z398]),(0,[z0,z1,z2,z4,z1246,z6])],[(0,[z0,z252,z1,z4,z862,z6]),(0,[z150,z1,z2,z4,z15,z141]),(0,[z0,z1,z2,z82,z6,z362])],[(0,[z0,z1,z2,z693,z26,z6]),(0,[z0,z1,z2,z4,z1247,z6]),(0,[z529,z0,z1,z2,z5,z83])],[(0,[z0,z1,z680,z4,z15,z6]),(0,[z0,z1,z4,z15,z38,z6]),(0,[z0,z394,z1,z4,z15,z6])],[],[(0,[z0,z1,z2,z4,z1248,z6]),(0,[z0,z17,z1,z2,z26,z6])],[(0,[z0,z1,z2,z1249,z4,z6]),(0,[z0,z1,z2,z1250,z5,z6]),(0,[z0,z1251,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z1252,z6]),(0,[z0,z81,z1,z235,z26,z6]),(0,[z0,z1,z343,z4,z38,z6])],[(0,[z0,z1253,z1,z2,z4,z6]),(0,[z0,z100,z4,z127,z5,z6]),(0,[z0,z1,z2,z4,z1254,z6]),(0,[z0,z1,z2,z4,z1255,z6]),(0,[z0,z1,z2,z4,z1256,z6])],[(0,[z0,z1,z2,z4,z5,z1257])]],
   [[(0,[z0,z2,z163,z4,z127,z6])],[(0,[z0,z1,z2,z4,z1258,z6]),(0,[z91,z120,z2,z4,z38,z6]),(0,[z0,z1,z135,z4,z38,z6]),(0,[z64,z0,z9,z4,z38,z6]),(0,[z0,z1,z2,z4,z1259,z6]),(1,[z0,z2,z873,z5,z6]),(0,[z0,z110,z2,z4,z127,z6]),(0,[z20,z0,z1,z2,z125,z6]),(0,[z0,z1,z2,z1260,z163,z6])],[(0,[z91,z483,z120,z2,z4,z5]),(0,[z0,z1,z4,z5,z6,z1261]),(0,[z0,z1,z2,z1262,z4,z6]),(0,[z0,z1,z231,z4,z164,z6]),(0,[z21,z1,z2,z148,z456,z6]),(0,[z20,z0,z1,z2,z4,z341])],[(0,[z0,z43,z349,z2,z4,z5]),(0,[z0,z9,z861,z4,z5,z6]),(0,[z0,z9,z1,z4,z164,z6]),(0,[z0,z1,z2,z4,z1263,z6])],[(0,[z0,z252,z1,z4,z879,z6]),(0,[z0,z156,z1,z2,z38,z6]),(0,[z20,z0,z1,z2,z6,z149]),(0,[z0,z90,z1,z2,z15,z83])],[(0,[z0,z1,z2,z765,z5,z6]),(0,[z0,z1264,z2,z4,z5,z6])],[(0,[z0,z162,z73,z2,z4,z6]),(0,[z0,z1,z2,z4,z1265,z6]),(0,[z0,z1,z2,z4,z6,z1266])],[(0,[z0,z1,z2,z1267,z5,z6]),(0,[z129,z1,z63,z4,z484,z6]),(0,[z0,z1152,z1,z4,z5,z6]),(1,[z0,z2,z4,z5,z880]),(0,[z0,z1,z2,z904,z4,z6])],[(0,[z165,z1,z2,z4,z25,z6]),(0,[z0,z292,z425,z4,z5,z6]),(0,[z150,z1,z135,z4,z5,z141]),(0,[z0,z23,z1,z4,z226,z46])],[(0,[z0,z162,z1,z376,z2,z4]),(0,[z0,z545,z1,z4,z5,z46]),(0,[z431,z1,z2,z4,z8,z6]),(0,[z0,z2,z4,z1268,z5,z6]),(0,[z0,z1,z2,z4,z1269,z6]),(0,[z33,z565,z1,z2,z4,z6])],[(0,[z0,z1,z2,z26,z583,z6]),(0,[z0,z1,z2,z5,z194,z83])],[(0,[z0,z1,z4,z38,z6,z19]),(0,[z0,z1,z2,z4,z27,z914])],[(0,[z0,z1045,z2,z4,z15,z6])],[],[(0,[z0,z1,z2,z1270,z5,z6]),(0,[z0,z1,z67,z5,z6,z167])],[(0,[z0,z78,z1,z2,z38,z6]),(0,[z0,z1,z2,z4,z1271,z6]),(0,[z0,z1,z1272,z4,z5,z6]),(0,[z0,z1,z2,z4,z1273,z6])]],
   [[(0,[z0,z2,z4,z1274,z5,z6]),(0,[z0,z1,z134,z2,z4,z285])],[(0,[z0,z1,z2,z4,z5,z1275]),(0,[z0,z1,z2,z4,z1276,z6]),(0,[z0,z1,z2,z4,z1277,z6])],[],[],[(0,[z0,z69,z1,z4,z243,z6]),(0,[z0,z29,z4,z52,z74,z6])],[(0,[z0,z1,z2,z4,z456,z6]),(0,[z0,z1278,z2,z4,z5,z6]),(0,[z0,z238,z2,z4,z52,z6])],[(0,[z0,z1,z376,z2,z4,z38]),(0,[z0,z1,z376,z2,z26,z4]),(0,[z0,z1,z1279,z4,z5,z6]),(0,[z0,z1,z2,z1280,z4,z6]),(0,[z0,z1,z242,z4,z15,z6]),(0,[z0,z96,z2,z97,z5,z6]),(0,[z0,z1,z2,z1281,z4,z6]),(0,[z123,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z1282,z6]),(0,[z0,z23,z1,z4,z272,z46])],[(0,[z0,z1,z2,z1283,z5,z6]),(0,[z0,z1,z2,z1116,z97,z6]),(0,[z0,z100,z73,z4,z5,z6]),(0,[z0,z1,z2,z1284,z4,z6]),(0,[z0,z413,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z1285]),(0,[z0,z1,z2,z779,z5,z6])],[(0,[z0,z1,z1286,z4,z5,z6]),(0,[z0,z1,z2,z4,z415,z6]),(0,[z0,z1,z2,z4,z1287,z6]),(0,[z0,z136,z2,z28,z5,z6]),(0,[z0,z1,z2,z4,z1288,z6]),(0,[z0,z81,z1,z2,z26,z6]),(0,[z0,z2,z4,z1113,z38,z6]),(0,[z0,z487,z1,z2,z26,z6])],[(0,[z0,z1289,z2,z4,z5,z6]),(0,[z20,z21,z1,z2,z148,z6]),(0,[z0,z1290,z1,z4,z5,z6]),(0,[z0,z1,z4,z15,z164,z6]),(1,[z0,z1,z2,z779,z6])],[(0,[z0,z1,z1291,z4,z5,z6])],[(0,[z84,z1,z2,z140,z38,z6]),(0,[z0,z1,z2,z26,z82,z6])],[(0,[z0,z1,z425,z4,z5,z6]),(0,[z0,z1,z4,z224,z38,z6]),(0,[z0,z1,z2,z1292,z4,z6]),(0,[z0,z29,z2,z4,z52,z6]),(0,[z0,z1,z2,z4,z88,z6])],[(0,[z0,z720,z223,z2,z4,z6]),(0,[z0,z283,z1,z4,z38,z6])],[(0,[z0,z1293,z1,z4,z5,z6]),(0,[z0,z1,z4,z195,z243,z6]),(0,[z0,z81,z1,z1042,z5,z6]),(0,[z0,z1,z4,z799,z5,z6]),(0,[z0,z1278,z2,z26,z4,z6]),(0,[z20,z0,z729,z2,z4,z6])],[(0,[z0,z1,z2,z779,z144,z6]),(0,[z20,z0,z827,z1,z4,z6])]],
   [[(0,[z91,z120,z2,z4,z15,z6]),(0,[z0,z1,z135,z4,z15,z6]),(0,[z0,z100,z73,z26,z4,z6]),(0,[z0,z1,z2,z4,z432,z6]),(0,[z0,z413,z1,z26,z4,z6]),(0,[z0,z1,z2,z4,z6,z1294]),(1,[z0,z2,z163,z127,z6]),(0,[z0,z1,z89,z4,z15,z117]),(0,[z20,z0,z1,z2,z4,z954])],[(0,[z1295,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z1296,z5,z6])],[(0,[z0,z252,z1,z4,z38,z6]),(0,[z0,z1,z2,z4,z5,z1297]),(0,[z0,z1298,z2,z4,z5,z6])],[(0,[z0,z156,z1,z2,z15,z6]),(0,[z0,z1,z2,z4,z798,z6]),(0,[z0,z1299,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z1300,z6]),(0,[z0,z1,z2,z4,z1301,z6]),(0,[z20,z0,z1,z2,z67,z6]),(0,[z0,z1,z1302,z2,z4,z6])],[(0,[z0,z1,z2,z4,z1303,z6]),(0,[z0,z1,z425,z26,z4,z6]),(0,[z0,z1,z2,z4,z6,z1304]),(0,[z0,z136,z2,z873,z5,z6]),(0,[z0,z29,z1,z2,z163,z6])],[(0,[z0,z1,z2,z4,z1305,z6]),(0,[z0,z1306,z1,z2,z4,z6]),(0,[z0,z1,z2,z26,z170,z6])],[(0,[z0,z1,z2,z4,z1307,z6]),(0,[z1,z2,z4,z5,z773,z141]),(0,[z0,z9,z1,z4,z38,z6]),(0,[z0,z1,z134,z2,z163,z6])],[(0,[z0,z846,z1,z2,z4,z6]),(0,[z0,z1,z2,z1308,z4,z6]),(0,[z0,z9,z1,z2,z163,z6])],[(0,[z0,z55,z2,z4,z5,z6]),(0,[z0,z162,z258,z1,z4,z6]),(0,[z0,z142,z1,z2,z163,z6]),(0,[z0,z2,z4,z15,z160,z6]),(0,[z0,z816,z2,z4,z5,z6])],[(0,[z207,z1,z231,z4,z130,z6]),(0,[z0,z9,z4,z52,z38,z6]),(0,[z0,z1,z2,z1195,z4,z6])],[(0,[z0,z156,z1,z2,z26,z6]),(0,[z1309,z0,z1,z2,z4,z6]),(0,[z0,z9,z574,z4,z5,z6]),(0,[z0,z1,z2,z26,z4,z1297]),(0,[z0,z1,z2,z5,z6,z362])],[(0,[z111,z1,z2,z4,z298,z6]),(0,[z0,z1,z2,z1310,z4,z6])],[(0,[z0,z1,z2,z4,z1311,z6])],[(0,[z0,z1312,z2,z4,z5,z6]),(0,[z0,z1,z2,z290,z38,z6]),(0,[z0,z1,z4,z5,z958,z46])],[(0,[z0,z1,z26,z4,z74,z6]),(0,[z0,z81,z1,z2,z37,z6])]],
   [[(0,[z1313,z0,z1,z2,z4,z6]),(0,[z0,z176,z2,z4,z161,z6])],[(0,[z0,z1,z2,z26,z400,z6])],[(0,[z165,z1,z2,z4,z575,z6]),(0,[z0,z1,z2,z4,z1314,z6])],[(0,[z0,z1,z89,z4,z5,z577]),(0,[z0,z1,z2,z4,z1315,z6])],[(0,[z639,z0,z1,z2,z4,z18])],[(0,[z0,z283,z120,z4,z5,z6]),(0,[z0,z1,z2,z4,z1316,z6]),(0,[z0,z1,z2,z4,z1317,z6]),(0,[z0,z1,z343,z2,z26,z6])],[(0,[z0,z78,z1,z2,z26,z6])],[(0,[z0,z1,z2,z4,z6,z1318]),(0,[z1,z2,z148,z767,z5,z6]),(0,[z0,z1,z1319,z4,z5,z6]),(0,[z20,z0,z1,z2,z459,z6])],[],[(0,[z116,z120,z2,z4,z5,z6]),(0,[z0,z1,z1099,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z773]),(0,[z0,z81,z1,z16,z5,z6]),(0,[z0,z487,z1,z16,z5,z6]),(0,[z0,z470,z1,z2,z26,z6]),(0,[z0,z1320,z2,z4,z5,z6])],[(0,[z0,z843,z2,z4,z5,z6]),(0,[z84,z1,z2,z140,z15,z6]),(0,[z0,z100,z1,z4,z88,z6]),(0,[z0,z73,z2,z4,z45,z6])],[(0,[z0,z9,z139,z4,z5,z6]),(0,[z0,z1,z2,z1321,z4,z6]),(0,[z0,z2,z4,z38,z6,z1109]),(0,[z0,z90,z1,z2,z276,z83])],[(0,[z91,z258,z120,z4,z5,z6]),(0,[z0,z223,z2,z4,z5,z6]),(0,[z0,z283,z1,z4,z15,z6]),(0,[z0,z2,z290,z127,z38,z6]),(0,[z0,z1,z463,z4,z38,z6]),(0,[z0,z1,z2,z860,z88,z6])],[(0,[z0,z1322,z2,z4,z5,z6]),(0,[z0,z81,z1,z164,z5,z6])],[(0,[z20,z91,z120,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z1323]),(0,[z0,z1324,z2,z4,z5,z6]),(1,[z1,z2,z767,z5,z6]),(0,[z295,z0,z1,z2,z4,z6])],[(0,[z0,z9,z41,z4,z38,z6]),(0,[z1325,z0,z1,z2,z4,z6]),(0,[z0,z283,z1,z4,z1057,z6]),(0,[z0,z1,z2,z1326,z4,z6]),(0,[z284,z0,z1,z2,z26,z6]),(0,[z0,z1,z2,z4,z6,z1327])]],
   [[(0,[z0,z9,z100,z4,z38,z6]),(0,[z0,z1,z4,z472,z38,z6]),(0,[z0,z1,z2,z163,z99,z6])],[(0,[z0,z1,z2,z602,z15,z6]),(0,[z0,z1,z5,z6,z167,z149])],[(0,[z0,z258,z73,z4,z5,z6]),(0,[z0,z1,z2,z4,z1328,z6]),(0,[z0,z1329,z2,z4,z5,z6]),(0,[z20,z0,z265,z2,z4,z6]),(0,[z0,z1,z2,z4,z278,z6])],[(0,[z0,z1,z476,z4,z38,z6]),(1,[z0,z1,z2,z4,z914])],[(0,[z0,z1,z1330,z4,z5,z6]),(0,[z0,z1,z2,z5,z6,z870])],[(0,[z0,z136,z223,z2,z5,z6]),(0,[z0,z223,z2,z26,z4,z6]),(0,[z0,z1,z2,z5,z6,z1331]),(0,[z0,z1,z2,z4,z1332,z6]),(0,[z0,z1333,z1,z2,z4,z6])],[(0,[z0,z29,z2,z4,z6,z499]),(0,[z0,z1,z2,z1165,z38,z6])],[(0,[z0,z1,z2,z4,z1334,z6]),(0,[z0,z1,z2,z4,z1335,z6])],[(0,[z20,z0,z1,z2,z97,z6]),(0,[z0,z2,z4,z5,z6,z1336]),(0,[z0,z1,z2,z26,z6,z362])],[(0,[z0,z1,z2,z4,z1337,z6]),(0,[z0,z1,z2,z32,z197,z6]),(0,[z20,z0,z1,z2,z60,z6])],[(0,[z889,z0,z1,z2,z4,z6]),(0,[z0,z100,z4,z127,z38,z6]),(0,[z0,z43,z2,z4,z15,z44]),(0,[z0,z1,z2,z26,z144,z6]),(0,[z0,z1,z2,z32,z278,z118])],[(0,[z0,z1,z2,z4,z1338,z6]),(0,[z0,z100,z4,z5,z6,z327]),(0,[z0,z1,z2,z1339,z4,z6]),(0,[z0,z2,z4,z127,z280,z6]),(0,[z0,z176,z2,z4,z30,z6]),(0,[z0,z1340,z1,z4,z5,z6])],[(0,[z0,z156,z162,z1,z2,z6]),(0,[z0,z100,z1,z290,z38,z6]),(0,[z0,z1,z2,z4,z977,z6]),(0,[z0,z1,z2,z1010,z5,z6])],[(0,[z299,z1,z2,z4,z25,z6])],[(0,[z0,z1,z1341,z4,z5,z6]),(0,[z0,z1,z135,z4,z1024,z6]),(0,[z0,z1,z2,z874,z5,z6])],[(0,[z0,z156,z9,z2,z5,z6]),(0,[z483,z0,z96,z2,z4,z5])]],
   [[(0,[z0,z1342,z2,z4,z5,z6]),(0,[z0,z81,z1,z16,z22,z6]),(0,[z20,z0,z1,z2,z4,z527]),(0,[z0,z1,z463,z10,z4,z6]),(0,[z296,z1,z2,z4,z383,z6])],[(0,[z621,z120,z2,z4,z5,z6]),(0,[z0,z1,z135,z602,z5,z6]),(0,[z0,z1,z2,z4,z1343,z6]),(0,[z20,z0,z976,z2,z4,z6])],[(0,[z1344,z0,z156,z1,z2,z6]),(0,[z0,z1,z2,z4,z1345,z6]),(0,[z0,z1,z2,z5,z6,z1346]),(0,[z0,z1,z2,z4,z1347,z6])],[(0,[z0,z1,z2,z4,z1348,z6]),(0,[z0,z1,z2,z4,z1349,z6]),(0,[z0,z1350,z1,z4,z5,z6]),(0,[z20,z0,z9,z210,z4,z6]),(0,[z0,z1,z2,z4,z764,z6])],[(0,[z0,z9,z258,z4,z5,z6]),(0,[z7,z1,z2,z4,z8,z6]),(0,[z0,z1,z2,z5,z6,z1351]),(0,[z0,z29,z1,z4,z74,z6])],[(0,[z1,z807,z2,z4,z5,z6]),(0,[z0,z1,z2,z290,z26,z6]),(0,[z201,z0,z1,z145,z4,z6])],[(0,[z0,z1,z2,z1352,z5,z6]),(0,[z0,z1,z2,z886,z5,z6]),(0,[z0,z412,z1,z2,z26,z6])],[(0,[z0,z1,z2,z4,z5,z1353]),(0,[z0,z1,z2,z163,z383,z6]),(0,[z428,z0,z1,z2,z26,z6])],[(0,[z0,z252,z78,z1,z5,z6]),(0,[z0,z100,z1,z4,z181,z6]),(0,[z0,z73,z2,z67,z5,z6]),(0,[z0,z1,z1354,z4,z5,z6])],[(0,[z0,z1,z2,z4,z570,z6]),(0,[z0,z1,z2,z4,z1355,z6])],[(0,[z0,z156,z2,z11,z5,z6]),(0,[z0,z1,z2,z4,z6,z1356]),(0,[z20,z0,z1,z4,z243,z6])],[(0,[z20,z0,z1,z2,z602,z6]),(0,[z0,z1,z2,z4,z1357,z6]),(0,[z0,z1,z2,z4,z5,z1358]),(0,[z20,z0,z283,z1,z4,z6]),(0,[z64,z0,z2,z4,z5,z87])],[(0,[z0,z1,z2,z4,z484,z6]),(0,[z0,z1,z2,z4,z1359,z6]),(0,[z0,z1,z2,z5,z6,z1360]),(0,[z20,z0,z1,z2,z451,z6]),(0,[z0,z1,z2,z1361,z5,z6]),(0,[z0,z1,z4,z1362,z5,z6])],[(0,[z0,z1,z2,z4,z1363,z6]),(0,[z0,z73,z4,z74,z5,z6]),(0,[z0,z81,z1,z2,z26,z341]),(0,[z0,z2,z4,z15,z127,z6]),(0,[z20,z0,z2,z4,z127,z6]),(0,[z0,z1,z2,z24,z5,z46]),(0,[z0,z2,z26,z4,z1022,z6])],[(0,[z0,z162,z78,z1,z2,z6]),(0,[z21,z1,z2,z148,z5,z6]),(0,[z0,z1,z2,z4,z1364,z6]),(0,[z0,z1,z186,z2,z4,z536]),(0,[z0,z1,z2,z32,z5,z870])],[(0,[z0,z1365,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z1366,z6]),(0,[z129,z1,z63,z4,z5,z6]),(0,[z0,z1,z425,z4,z908,z6]),(0,[z0,z1,z425,z4,z335,z6]),(0,[z0,z2,z861,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z774])]],
   [[(0,[z0,z807,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1367,z6]),(0,[z20,z0,z139,z2,z4,z6]),(0,[z0,z1,z2,z4,z1368,z6]),(0,[z0,z1,z68,z2,z163,z6]),(0,[z0,z238,z1,z4,z38,z6]),(0,[z0,z1,z2,z4,z1369,z6])],[(0,[z0,z1033,z2,z4,z5,z6])],[(0,[z1344,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z32,z5,z333]),(0,[z0,z1,z2,z4,z1370,z6])],[(0,[z0,z1,z2,z1371,z4,z5]),(0,[z0,z2,z4,z38,z6,z327])],[(0,[z0,z1372,z1,z4,z5,z6]),(0,[z64,z0,z2,z26,z4,z87]),(0,[z0,z1,z2,z4,z1373,z6])],[(0,[z0,z96,z2,z4,z5,z6]),(0,[z0,z1,z2,z97,z5,z6]),(0,[z0,z1,z2,z290,z185,z6]),(0,[z0,z2,z4,z1080,z15,z6]),(0,[z0,z1,z2,z4,z1374,z6])],[(0,[z0,z1,z190,z4,z38,z6]),(0,[z0,z1375,z1,z2,z4,z6]),(0,[z0,z1376,z1,z2,z4,z6])],[(0,[z845,z0,z1,z2,z76,z6])],[(0,[z0,z1,z2,z1377,z5,z6]),(0,[z129,z1,z63,z26,z4,z6]),(0,[z0,z1378,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1379,z6]),(0,[z0,z81,z1,z2,z26,z527]),(0,[z201,z0,z782,z2,z4,z6]),(0,[z0,z1,z2,z26,z24,z6])],[(0,[z0,z1,z2,z4,z130,z6]),(0,[z0,z1,z4,z420,z38,z6]),(0,[z0,z176,z68,z4,z38,z6])],[(0,[z0,z1380,z2,z4,z5,z6]),(0,[z0,z1,z4,z1381,z5,z6]),(0,[z0,z1,z4,z164,z6,z46])],[(0,[z0,z1,z2,z1382,z5,z6]),(0,[z0,z1196,z139,z2,z4,z6]),(0,[z0,z1,z2,z1383,z4,z6]),(0,[z0,z1,z2,z26,z309,z6]),(0,[z0,z1,z2,z119,z185,z6]),(0,[z0,z1,z2,z4,z1384,z6]),(0,[z0,z1,z2,z38,z6,z1169]),(0,[z0,z1,z416,z2,z4,z285])],[(0,[z0,z156,z1,z376,z2,z5]),(0,[z0,z1,z2,z4,z1385,z6]),(0,[z0,z716,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1386,z6]),(0,[z20,z0,z2,z4,z160,z6]),(0,[z0,z1,z2,z32,z5,z294]),(0,[z0,z1,z2,z26,z46,z83]),(0,[z0,z1,z2,z4,z1387,z6]),(0,[z0,z1388,z2,z4,z5,z6])],[(0,[z0,z9,z491,z4,z5,z6]),(0,[z0,z2,z4,z818,z5,z6]),(0,[z0,z1,z2,z163,z1389,z6]),(0,[z31,z1,z2,z174,z4,z6])],[(0,[z483,z0,z9,z2,z4,z5]),(0,[z0,z96,z2,z26,z4,z6]),(0,[z0,z1,z2,z4,z1390,z6]),(0,[z0,z9,z1,z163,z38,z6]),(0,[z0,z1,z353,z4,z38,z6]),(0,[z1391,z0,z1,z2,z4,z6])],[(0,[z150,z1,z425,z4,z5,z141]),(0,[z0,z9,z580,z4,z5,z6]),(0,[z0,z1,z2,z4,z1392,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 504) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 504).take 487) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 991).take 433) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1424)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [504, 487, 433] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 112).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 112).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 218).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 318).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 424).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [112, 106, 100, 106, 88] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_38165

theorem PEqualNP.Outside.L_meta_38165 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241824 * 2 ^ 32 + 4008222880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241824 * 2 ^ 32 + 4008222880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38165.solve