import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37577

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

theorem tierB {S : ℕ × List W → Bool} {J d K : ℕ} (hK : J + d = K) {L : List (ℕ × List W)} {sizes : List ℕ}
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false)
    (hw : windowsG (chunkB S d) L 0 sizes = true) : FalseAt K L := by
  subst hK
  have hP := windowsG_sound (P := fun c => optB S d c.1 c.2 = false)
    (fun X hX c hc => by have := List.all_eq_true.mp hX c hc; simpa using this) sizes 0 hw
  intro c hc
  exact optB_sound S J hS d c.1 c.2 (hP c (by simpa using hc))

theorem memS {g nb J : ℕ} {bk : List (List (List (ℕ × List W)))} (h : FalseAt J bk.flatten.flatten) :
    ∀ c, (!inB2 g nb bk c) = false → optimized J c.1 c.2 = false := by
  intro c hc
  have hin : inB2 g nb bk c = true := by simpa using hc
  exact h c (inB2_mem hin)

theorem finalF {J : ℕ} {bk : List (List (List (ℕ × List W)))} {sizes : List ℕ}
    (h : windowsF J bk.flatten 0 sizes = true) : FalseAt J bk.flatten.flatten := by
  have := falseAt_of_windowsF sizes 0 h
  simpa using this

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4276791464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def rows : List W :=
  [(mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07fffffff 0xfff04e463c063fff),
   (mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f1b5b9d239d273),
   (mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e39c1e3c1e39c),
   (mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000fc1fe03fe03e0),
   (mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000ffe0003fffc00),
   (mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000ffffffc000000)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

def z0 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f1b5b9d239d273

def z1 : W := mkw 0x1802081040400000 0x0006da0000000000 0x0000000000000000 0x000e4a0000000000

def z2 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000ffffffc000000

def z3 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07fffffff 0xfff04e463c063fff

def z4 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000fc1fe03fe03e0

def z5 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000ffe0003fffc00

def z6 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e39c1e3c1e39c

def z7 : W := mkw 0x0000010008800111 0x000000000800080a 0x000000e07ffe000f 0xfff00e003c003c1f

def z8 : W := mkw 0x2004000000044000 0x1040000400040140 0xe03c0f000001fff0 0x00004046000603e0

def z9 : W := mkw 0x011850628108a8aa 0x09a0012102319231 0x003ff0ff8781e0ff 0x03f181b80239d273

def z10 : W := mkw 0x2404010008845111 0x924800defc04094a 0x000000000001ffff 0xfff001fffc0003ff

def z11 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x00004a462c000000

def z12 : W := mkw 0x0001000804000000 0x0201241090000000 0x0000000000000000 0x0001b5b9d0000000

def z13 : W := mkw 0xdd4348bb54513a8c 0xea2fffdbf7816294 0xffc000fff801ff0f 0xfc0fffffffc1e39c

def z14 : W := mkw 0x0108400200008888 0x0080012002200220 0x003ff0000001e0f0 0x000181b802380260

def z15 : W := mkw 0x75bf7a6a852dfcea 0x3bebe5ff937f93f1 0xffffffff8781ffff 0x03fff5ffd3ffd3f3

def z16 : W := mkw 0x0400000000001000 0x800800ca64000000 0x0000000000000000 0x000000462c000000

def z17 : W := mkw 0x0400000000001000 0x820800daf4000000 0x0000000000000000 0x000001fffc000000

def z18 : W := mkw 0x1d03483a44403888 0x8a2fffdbf6010210 0x000000ff8001e00f 0x000ffffffe01c210

def z19 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0f007ffe1ff0 0xfff04e463c063def

def z20 : W := mkw 0x4540402310013a8c 0xaa2801dbf7010294 0x000000000001ff0f 0xfc0001fffc00039c

def z21 : W := mkw 0x1c02081040401000 0x800edaca64000000 0x0000000000000000 0x000e4a462c000000

def z22 : W := mkw 0x4508400200019888 0x208801e0032002a0 0xfffff0000001fff0 0x000f81f803f803e0

def z23 : W := mkw 0x9b3bccde66788888 0x4187ff2002faf620 0xffffffffffffe0f0 0x000fffb803fffe60

def z24 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000007801ff0f 0xfc0e09c1e1c0239c

def z25 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e00780000f 0x03f0040010001013

def z26 : W := mkw 0x0100402200002888 0x0820010102010210 0x000000ff8001e00f 0x00003181c201c210

def z27 : W := mkw 0xcd5950fbd519baae 0xebad3df1f3b1f2b5 0xfffff0ffff81ffff 0xffffbdf9f3f9f3ff

def z28 : W := mkw 0x884000b150102204 0xc824180160816014 0x000000fff800000f 0xfc003801e001e01c

def z29 : W := mkw 0x61ac630208a5cdd9 0x30c001240b6e0bea 0xffffffe07fffffff 0xfff04e463ffe3fff

def z30 : W := mkw 0x0000000000000000 0x82000010f4000000 0x0000000000000000 0x00000001fc000000

def z31 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fb1b9c0000000

def z32 : W := mkw 0x0019104885088022 0x0381243090309021 0x003ff0e00781e0ff 0x03f1843810381273

def z33 : W := mkw 0x8a1194fce7582022 0x4b253e119091f411 0x000000fffffe000f 0x03f03e01d001fc13

def z34 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000ffe463ffffc00

def z35 : W := mkw 0xdd4348bb54513a8c 0xea2fffdbf7816294 0x1fc0001f80000000 0x000fffffffc1c000

def z36 : W := mkw 0x1022080000200000 0x0002c000004a0000 0xffffff0000000000 0x000fc00003fe0000

def z37 : W := mkw 0xffbfeede667ddcc8 0x71cfffee03fef7e0 0xfffffffffffffff0 0x000ffffe03ffffe0

def z38 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffff1f80000000 0x000ff00003ffc000

def z39 : W := mkw 0x9a338ddc6ef80111 0x4107fe0008dafc0a 0xfffffffffffe000f 0xfffffe003ffffc1f

def z40 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe07fffffff 0xffffcffe3ffe3fff

def z41 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xfffc00ffff81ffff 0xfffe3dc1f3c1f3ff

def z42 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x000181b800000000

def z43 : W := mkw 0x7daf6a1a4465dcc8 0xb2cffffef76e03e0 0xffffff000001fff0 0x000ffffffffe03e0

def z44 : W := mkw 0x211c5162898ce9bb 0x19e001250a359b7b 0xe03fffffffffffff 0xfff00000023fffff

def z45 : W := mkw 0x211d516a8d8ce9bb 0x1be125359a359b7b 0xe03fffffffffffff 0xfff1fffffe3fffff

def z46 : W := mkw 0x75ee6a231025fecc 0xb8eac1ef636f03f4 0xffffff000001ffff 0xfc0fc1ffe3fe03fc

def z47 : W := mkw 0x0011004804080000 0x0101240000109000 0x003ff0ff87800000 0x0001b4000239d000

def z48 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0xfffffffffffe0000 0x000ffffffffffc00

def z49 : W := mkw 0x0100402200002888 0x0820010102010210 0x003c00ff8781e0ff 0x03f03581d201d273

def z50 : W := mkw 0x011850628108a8aa 0x09a0012102319231 0x003ff0ff8781e0ff 0x03f000000239d273

def z51 : W := mkw 0x2004010008844111 0x104000040804094a 0x003c0fe007ffe0ff 0x03f046061c061e73

def z52 : W := mkw 0x0101402a04002888 0x0a21251192010210 0x000000ff8001e00f 0x0001b5b9d201c210

def z53 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x0003f01f80000000 0x0001b1b9c239c000

def z54 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1fc3f00000000000 0x000f81b803f80000

def z55 : W := mkw 0x61ac62020025ccc8 0x30c00124036e03e0 0xffffff000001fff0 0x0000000003fe03e0

def z56 : W := mkw 0x133bdc6ea768a8aa 0x0ba3e731927b9631 0x003fffff87ffe0ff 0x03f1f7b9d23fde73

def z57 : W := mkw 0x4540402310013a8c 0xa82801c163010294 0x000000000001ff0f 0xfc0001c1e000039c

def z58 : W := mkw 0xed4441b358957b9d 0xf86c19c56b856bde 0xfffc0fffffffffff 0xfffe7fc7ffc7ffff

def z59 : W := mkw 0xcc40009150111204 0xe00c18c061806084 0xffc0000078001f00 0xfc0e084021c0218c

def z60 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0x1fc0001f80000000 0x000e3181c3c1c000

def z61 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e7fc7ffc1e39c

def z62 : W := mkw 0xfdee6ab35035fecc 0xf8eed9ef63ef63f4 0xfffffffff801ffff 0xfc0ff9ffe3ffe3fc

def z63 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000ff80000000 0x000030000201c000

def z64 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff87800000 0x0001b5b9c239d000

def z65 : W := mkw 0x0400000000001000 0x000800c000000000 0x0000000000000000 0x000e01c000000000

def z66 : W := mkw 0x1d1b587ac548b8aa 0x8baffffbf6319231 0x003ff0ff8781e0ff 0x03fffffffe39d273

def z67 : W := mkw 0x1022080000200000 0x0002c000004a0000 0x003fff0000000000 0x0001c000003e0000

def z68 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0xe03c0fe07ffe0000 0x000ffffffc063c00

def z69 : W := mkw 0x0801001844400000 0x82053e10f4000000 0x0000000000000000 0x00003e01fc000000

def z70 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x003c00e00781e0ff 0x03fffffffc001273

def z71 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0x1fc3f01f80000000 0x000fb00003f9c000

def z72 : W := mkw 0xdf73ccff76793a8c 0xe92fffc163dbf694 0xffffffffffffff0f 0xfc0fffc1e3ffff9c

def z73 : W := mkw 0x1402080000001000 0x000ac0ca00000000 0x0000000000000000 0x000fc1fe00000000

def z74 : W := mkw 0x8c4000b150103204 0xc82c18c160816014 0x000000fff800000f 0xfc0e39c1e001e01c

def z75 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0x1fc3f01f80000000 0x000ffffffff9c000

def z76 : W := mkw 0x1803081844400000 0x0007fe0000000000 0xe03c0fe07ffe0000 0x000ffe0000063c00

def z77 : W := mkw 0xa84401b158946315 0xd86418056885695e 0xe03c0fffffffffff 0xfff07e47fc07ffff

def z78 : W := mkw 0x0000000000000000 0x0000000000000000 0xe03c00e07f81ffff 0xfff00c40300033ff

def z79 : W := mkw 0x211c5162898ce9bb 0x19e001250a359b7b 0xe03fffffffffffff 0xfff04e463e3fffff

def z80 : W := mkw 0x8b19d4fee758a8aa 0x4ba53f3192b1f631 0x003ff0ffffffe0ff 0x03f1bfb9d239fe73

def z81 : W := mkw 0x7dbf7a7ac56dfcea 0xbbeffffff77f93f1 0xffffffff8781ffff 0x03ffffffffffd3f3

def z82 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x00004e463c000000

def z83 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000fb00003fffc00

def z84 : W := mkw 0x74a62b0008a55551 0x304ac0ce094e09ca 0xffc00f00787e1f00 0xfc0e4a462dc62d8c

def z85 : W := mkw 0xedec62b35035fecc 0xf8ec19e563ef63f4 0xfffffffff801ffff 0xfc0e39c1e3ffe3fc

def z86 : W := mkw 0xbe378ddc6efc5111 0xd34ffedefcdefd4a 0xffffffffffffffff 0xffffffffffffffff

def z87 : W := mkw 0x30ae2a000024c440 0x10c2c02e006e0160 0xe03fff000001fff0 0x0001c07e003e03e0

def z88 : W := mkw 0x380709184cc44111 0x1047fe040804094a 0xe03c0fe07fffffff 0xfffffe463c063fff

def z89 : W := mkw 0x12338c4c26680000 0x0103e600005a9400 0x003fff0007fe0000 0x0001c600003e1c00

def z90 : W := mkw 0x1803081844400000 0x0007fe0000000000 0x0000000000000000 0x000ffe0000000000

def z91 : W := mkw 0x8a1185dc6ed80111 0x41053e000890fc0a 0x000000fffffe000f 0xfff03e003c01fc1f

def z92 : W := mkw 0x0108400200008888 0x0080012002200220 0x003ff0000001e0f0 0x0000000002380260

def z93 : W := mkw 0x32bfae4c266cc440 0x11c3e62e007e9560 0x003fff0007fe00f0 0x0001c63e003e1c60

def z94 : W := mkw 0x1a338c5c66680000 0x0107fe00005a9400 0x003fff0007fe0000 0x000ffe00003e1c00

def z95 : W := mkw 0x30ae2a000024c440 0x10c2c02e006e0160 0x003fff00000000f0 0x0001c03e003e0060

def z96 : W := mkw 0xcd5950fbd519baae 0xebad3df1f3b1f2b5 0xffc3f0fff801ff0f 0xfc0fb9f9e3f9e39c

def z97 : W := mkw 0x9b3bdcfee778a8aa 0x4ba7ff3192fbf631 0xffffffffffffe0ff 0x03ffffb9d3fffe73

def z98 : W := mkw 0x0000000000000000 0x0000000000000000 0x003c00e00781e0ff 0x03f0040010001273

def z99 : W := mkw 0x0011106885082022 0x0b21241190119011 0x000000ff8780000f 0x03f03401d001d013

def z100 : W := mkw 0x8a00849462500000 0x40041a0000806400 0x00000000787e0000 0x00000a0000002c00

def z101 : W := mkw 0xba378ddc6efc4111 0x5147fe0408defd4a 0xffffffffffffffff 0xfffffe463fffffff

def z102 : W := mkw 0x7ca62a1040655440 0xb04edace654e01c0 0xffc00f0000001f00 0x000e4a462dc60180

def z103 : W := mkw 0x885110f9d5182226 0xcb253c11f091f015 0x000000ffff80000f 0xfff03c01f001f01f

def z104 : W := mkw 0xdd4348bb54513a8c 0xea2fffdbf7816294 0x1fc0001f80000000 0x000fb1b9c3c1c000

def z105 : W := mkw 0x0c00001040001000 0x800c18c060000000 0x0000000000000000 0x000e3181c0000000

def z106 : W := mkw 0x3026090008a44111 0x1042c004084e094a 0xffffffe07fffffff 0xffffce463ffe3fff

def z107 : W := mkw 0xc14040a310112a8c 0x6820010103816294 0xffc000fff801ff0f 0xfc00000003c1e39c

def z108 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x0003f01f8001e0ff 0x03f1b1b9d239c273

def z109 : W := mkw 0x0108400200008888 0x0080012002200220 0x000000000001e0f0 0x000001b800000260

def z110 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07fffffff 0xfff0000000063fff

def z111 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe07fffffff 0xffffc1fe03fe3fff

def z112 : W := mkw 0xddea6ab35031becc 0xe8aed9eb63eb62b4 0xffc3f0fff801ff0f 0xfc0fb9f9e3f9e39c

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x00000e003c000000

def z114 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f1b1b9c239d273

def z115 : W := mkw 0x0000000000000000 0x0000000000000000 0xe03c0fe07ffe0000 0x00004e0000063c00

def z116 : W := mkw 0x0111506a850828aa 0x0b21251192119211 0x000000ff8781e00f 0x03f03581d201d213

def z117 : W := mkw 0x74a62a0000255440 0x304ac0ce014e01c0 0xffc00f0000001f00 0x000e404601c60180

def z118 : W := mkw 0x010850228100a8aa 0x0aa0013192210231 0x000000000001e0ff 0x03f001b9d0000273

def z119 : W := mkw 0x1003080804400000 0x0203e61a94000000 0x0000000000000000 0x0001c63e1c000000

def z120 : W := mkw 0x1033084804280000 0x0103e400005a9000 0xffffffff87800000 0x000ff40003ffd000

def z121 : W := mkw 0x12338c4c26680000 0x0103e600005a9400 0xe03fffe07ffe0000 0x0001ce00003e3c00

def z122 : W := mkw 0x1403080804001000 0x020be4da90000000 0x0000000000000000 0x000ff5ffd0000000

def z123 : W := mkw 0x92328cc422380000 0x4102c00000daf400 0xfffffffffffe0000 0x000fc00003fffc00

def z124 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00000e07801ff0f 0xfc0008402000239c

def z125 : W := mkw 0x0019104885088022 0x0381243090309021 0x003ff000078000f0 0x03f1843810381063

def z126 : W := mkw 0xfce62a9150355644 0xf04ed8ce61ce61c4 0xffc00f0078001f00 0xfc0e484621c6218c

def z127 : W := mkw 0x0801001844400000 0x82053e10f4000000 0x0000000000000000 0x00007e47fc000000

def z128 : W := mkw 0x4540402310013a8c 0xa82801c163010294 0x0000000000000000 0x00000181c0000000

def z129 : W := mkw 0x74a62a0000255440 0x304ac0ce014e01c0 0xffffff0000001f00 0x000fc04603fe0180

def z130 : W := mkw 0x75bf7a6a852dfcea 0x3bebe5ff937f93f1 0xffffff1f8001fff0 0x000ff1ffc3ffc3e0

def z131 : W := mkw 0x0400000000001000 0x000800ca00000000 0x0000000000000000 0x000001fe00000000

def z132 : W := mkw 0x2004010008844111 0x104000040804094a 0x0000000000001f00 0xfc0000462c00018c

def z133 : W := mkw 0x3c0709184cc45111 0x924ffedefc04094a 0xe0000f00787e1f00 0xfc0ffffffc062d8c

def z134 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0x003fff000001fff0 0x0001c1fe003e03e0

def z135 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xfffc0fffffffff0f 0xfc0e7fc1e3c7ff9c

def z136 : W := mkw 0x7dae6a124065dcc8 0xb0cedbee676e03e0 0xffffff000001fff0 0x000fcbfe2ffe03e0

def z137 : W := mkw 0x884000b150102204 0xc824180160816014 0x0000001f80000000 0x00003001c001c000

def z138 : W := mkw 0x895950fbd518aaae 0xcba53d31f2b1f235 0x003ff0ffff81e0ff 0xfff1bdb9f239f27f

def z139 : W := mkw 0x0c00001040001000 0x820c18daf4000000 0x0000000000000000 0x000e39fffc000000

def z140 : W := mkw 0x2004010008844111 0x104000040804094a 0xe0000fe07ffe1f0f 0xfff04e463c063d9f

def z141 : W := mkw 0x1422080000201000 0x000ac0ca004a0000 0xffffff0000000000 0x000fc1fe03fe0000

def z142 : W := mkw 0x9a228c9462700000 0x4006da0000ca6400 0xffc00f00787e0000 0x000e4a0001c62c00

def z143 : W := mkw 0x9e238c9c66701000 0xc20ffedaf4ca6400 0xffc00f00787e0000 0x000ffffffdc62c00

def z144 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0xe03ff0ffff81ffff 0xfff1bdf9f239f3ff

def z145 : W := mkw 0x9b3bdcfee778a8aa 0x4ba7ff3192fbf631 0xfffffffffffe0000 0x000fffb9c3fffc00

def z146 : W := mkw 0x823084c422380000 0x4100000000daf400 0xfffffffffffe0000 0x0000000003fffc00

def z147 : W := mkw 0x1d1b587ac548b8aa 0x8baffffbf6319231 0x0003f01f80000000 0x000fb1b9c239c000

def z148 : W := mkw 0x2004010008844111 0x104000040804094a 0xe0000f00787e1f00 0xfc004a462c062d8c

def z149 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1ffff0000001e0f0 0x000f81b803f80260

def z150 : W := mkw 0x0011004804080000 0x0101240000109000 0x003ff00007800000 0x0001840000381000

def z151 : W := mkw 0x74a62a0000255440 0x304ac0ce014e01c0 0xffc00f0000001f00 0x000fc1fe01c60180

def z152 : W := mkw 0x3c0709184cc45111 0x924ffedefc04094a 0xe03c0fe07fffffff 0xfffffffffc063fff

def z153 : W := mkw 0x658c62020005dcc8 0x30c801ee032403e0 0x000000000001fff0 0x000001fe000003e0

def z154 : W := mkw 0x4500400200011888 0x200801c003000280 0xffc000000001ff00 0x000e01c003c00380

def z155 : W := mkw 0x0011106885082022 0x0b21241190119011 0x000000ff8780000f 0x03f1b5b9d001d013

def z156 : W := mkw 0x8a1184dc66580000 0x41053e000090f400 0x000000fffffe0000 0x00003e000001fc00

def z157 : W := mkw 0x2004010008844111 0x104000040804094a 0x000000000001ffff 0xfff000463c0003ff

def z158 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0xffffff0000000000 0x000fc1b803fe0000

def z159 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff01f878000f0 0x03f1b5b9d239d063

def z160 : W := mkw 0x113b586a8528a8aa 0x0ba3e531927b9231 0xffffffff8781e0ff 0x03fff5b9d3ffd273

def z161 : W := mkw 0x1803081844400000 0x0207fe1a94000000 0x0000000000000000 0x000ffe3e1c000000

def z162 : W := mkw 0xcd5850f3d119baae 0xe9ac19e163b1f2b5 0xfffff0ffff81ffff 0xfffe39c1e3f9f3ff

def z163 : W := mkw 0x8800009040100000 0x4004180000806000 0xffc000fff8000000 0x000e380003c1e000

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0xe03c0fe07ffe0000 0x00004e463c063c00

def z165 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff000001ffff 0xffffc1fe3ffe03ff

def z166 : W := mkw 0x884000b150102204 0xc824180160816014 0xffc000fff800000f 0xfc0e3801e3c1e01c

def z167 : W := mkw 0xc14040a310112a8c 0x6820010103816294 0xffc000fff801ff0f 0xfc003181c3c1e39c

def z168 : W := mkw 0xba268d946af44111 0x5046da0408ce6d4a 0xffc00f00787e1f00 0xfc0e4a462dc62d8c

def z169 : W := mkw 0x0c00001040001000 0x800c18c060000000 0x0000000000000000 0x000e084020000000

def z170 : W := mkw 0xfdee6bb358b5ffdd 0xf8eed9ef6bef6bfe 0xffffffffffffffff 0xffffffffffffffff

def z171 : W := mkw 0x821084c422180000 0x410000000090f400 0x000000fffffe0000 0x000000000001fc00

def z172 : W := mkw 0x201d11488d8cc133 0x13c124349834996b 0x003fff0007fe00f0 0x03f1c63e1c3e1c63

def z173 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000001e0ff 0x03f0000010000273

def z174 : W := mkw 0x210c51228984e9bb 0x1ae001359a250b7b 0xe03c0fe07fffffff 0xfff04ffffc063fff

def z175 : W := mkw 0x0018104081088022 0x0180002000309021 0x003ff000078000f0 0x03f0000000381063

def z176 : W := mkw 0x5dab6a1a44619cc8 0xa28ffffaf76a02a0 0x1fc3f00000000000 0x000fb1b9c3f80000

def z177 : W := mkw 0x0019104885088022 0x0381243090309021 0x0003f00000000000 0x0001803800380000

def z178 : W := mkw 0x4d40403350013a8c 0xa82c19c163010294 0x000000000001ff0f 0xfc0e39c1e000039c

def z179 : W := mkw 0x9a338cdc66780000 0x4307fe1090daf400 0xfffffffffffe0000 0x000fffb9d3fffc00

def z180 : W := mkw 0x0100402200002888 0x0820010102010210 0x0000001f80000000 0x00003181c201c000

def z181 : W := mkw 0x0c00001040001000 0x800c18c060000000 0x0000000000000000 0x000e39c1e0000000

def z182 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe00781ffff 0x03ffc5fe13fe13f3

def z183 : W := mkw 0xc54040a310113a8c 0x682801c103816294 0xffc000fff801ff0f 0xfc0e01c003c1e39c

def z184 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffc3ff0000001f00 0x000fc1fe03fe0180

def z185 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff01f8001e0f0 0x0001b1b9c239c260

def z186 : W := mkw 0xde738cdd76791204 0xe10ffec061daf484 0xfffffffffffe1f00 0xfc0ffe4023fffd8c

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e07ffe0000 0x00000e0000003c00

def z188 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07fffffff 0xfff000463c063fff

def z189 : W := mkw 0x65ac62020025dcc8 0x30c801e4036e03e0 0xffffff000001fff0 0x000e01c003fe03e0

def z190 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffffffffffff0f 0xfc0ffe4023ffff9c

def z191 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x000000ff8781e0ff 0x03f035b9d001d273

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0x003ff00000000000 0x0001800002380000

def z193 : W := mkw 0x0000000000000000 0x0200001090000000 0x0000000000000000 0x000001b9d0000000

def z194 : W := mkw 0x0001000804000000 0x0201241090000000 0x0000000000000000 0x00003401d0000000

def z195 : W := mkw 0x4500402200013888 0x282801c103010290 0xffc000ff8001ff0f 0x000e31c1c3c1c390

def z196 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00000e07801ff0f 0xfc004e463c00239c

def z197 : W := mkw 0x894040b350102a8c 0xc824190162816214 0x000000fff801e00f 0xfc003981e201e21c

def z198 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffc00ffffffe0000 0x000e7e0001c7fc00

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0xe000000078001f00 0xfc0008402000218c

def z200 : W := mkw 0x0c01001844401000 0x820d3edaf4000000 0x0000000000000000 0x00003ffffc000000

def z201 : W := mkw 0x2404010008845111 0x924800defc04094a 0xe03c0fe07fffffff 0xfff04ffffc063fff

def z202 : W := mkw 0x6504400200055888 0x304801c4030403c0 0xfffc0f000001fff0 0x000e41c603c603e0

def z203 : W := mkw 0x1c13085844481000 0x830ffedaf4109000 0x003ff0ff87800000 0x000ffffffe39d000

def z204 : W := mkw 0x4140402310012a8c 0x2820010103010294 0x000000000001ff0f 0xfc0000000000039c

def z205 : W := mkw 0xcd4041b358913b9d 0xe82c19c16b816a9e 0xffc000ffffffff0f 0xfffe3fc1ffc1ff9f

def z206 : W := mkw 0xed4441b358957b9d 0xf86c19c56b856bde 0xfffc0fffffffffff 0xfffe39c1e3c7ffff

def z207 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x000000463c000000

def z208 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07fffffff 0xfff04e0000063fff

def z209 : W := mkw 0x8338d4e6a338a8aa 0x49a0012102fbf631 0xffffffffffffe0ff 0x03f0000003fffe73

def z210 : W := mkw 0xed4440b350157a8c 0xf86c19c5638563d4 0xfffc0ffff801ffff 0xfc0e79c7e3c7e3fc

def z211 : W := mkw 0x9a228c9462700000 0x4006da0000ca6400 0xfffc0fe07ffe0000 0x000e4e0001c63c00

def z212 : W := mkw 0xbabfaedc667cc440 0x51c7fe2e00fef560 0xfffffffffffe00f0 0x000ffe3e03fffc60

def z213 : W := mkw 0x1022080000200000 0x0002c000004a0000 0x1fc3f00000000000 0x000f800003f80000

def z214 : W := mkw 0x30ae2b0008a4c551 0x10c2c02e086e096a 0x003fff0007fe00f0 0x03f1c63e1c3e1c63

def z215 : W := mkw 0x74ae2a000025d440 0x30cac0ee016e01e0 0xffffff0000001ff0 0x000fc07e01fe01e0

def z216 : W := mkw 0xcd5140fb54193a8c 0xe92d3dc16391f294 0xfffff0ffff81ff0f 0xfc0fbdc1e3f9f39c

def z217 : W := mkw 0xcd5950fbd519baae 0xebad3df1f3b1f2b5 0x1fc3f01f80000000 0x000fb1b9c3f9c000

def z218 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z219 : W := mkw 0x0000010008800111 0x000000000800080a 0x000000e07ffe000f 0xfff04e463c003c1f

def z220 : W := mkw 0x9a138cdc66580000 0x4107fe000090f400 0x000000fffffe0000 0x000ffe000001fc00

def z221 : W := mkw 0x0000000000000000 0x0000000000000000 0x003c00e007800000 0x0000040000001000

def z222 : W := mkw 0x151b586a8508b8aa 0x0babe5fb92319231 0x003ff0ff8781e0ff 0x03fff5ffd239d273

def z223 : W := mkw 0xcd4840b35011ba8c 0xe8ac19e163a162b4 0xfffff0fff801ffff 0xfc0fb9f9e3f9e3fc

def z224 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0xe00000e07801ff0f 0xfc0ffffffc00239c

def z225 : W := mkw 0x0108400200008888 0x0080012002200220 0x003ff0e00781e0ff 0x03f185b812381273

def z226 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0x1fc000ff8001e00f 0x000e3181c3c1c210

def z227 : W := mkw 0x010850228100a8aa 0x0aa0013192210231 0x000000ff8001e0ff 0x03f031b9d201c273

def z228 : W := mkw 0xc94040b350112a8c 0x6824190103816294 0xffc000fff801ff0f 0xfc0e380003c1e39c

def z229 : W := mkw 0x1c03081844401000 0x800ffeca64000000 0x0000000000000000 0x000ffe462c000000

def z230 : W := mkw 0x1403080804401000 0x820be6daf4000000 0x0000000000000000 0x0001c7fffc000000

def z231 : W := mkw 0x7daf6b1a4ce5ddd9 0xb2cffffeff6e0bea 0xffffffe07fffffff 0xfffffffffffe3fff

def z232 : W := mkw 0x2004010008844111 0x104000040804094a 0xe00000e07801ffff 0xfff008463c0023ff

def z233 : W := mkw 0xdfbbeede66799cc8 0x618fffea03faf6a0 0xfffffffffffe0000 0x000fffb803fffc00

def z234 : W := mkw 0x7dae6a124025dcc8 0xb0ced9ee636e03e0 0xffffff000001fff0 0x000ff9ffe3fe03e0

def z235 : W := mkw 0x5d03481a44411888 0xa20fffdaf7000280 0xffc000000001ff00 0x000fffffffc00380

def z236 : W := mkw 0xc14040a310112a8c 0x6820010103816294 0x1fc0001f80000000 0x0000000003c1c000

def z237 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000f81b803fe03e0

def z238 : W := mkw 0x7daf6a1a4465dcc8 0x30cfffee036e03e0 0xffffff000001fff0 0x000ffffe03fe03e0

def z239 : W := mkw 0xfdae6a924035dcc8 0x70ced9ee03ee63e0 0xfffffffff801fff0 0x000ff9fe03ffe3e0

def z240 : W := mkw 0x0400000000001000 0x820800daf4000000 0x0000000000000000 0x000001b9c0000000

def z241 : W := mkw 0x12338c4c26680000 0x0303e61a945a9400 0x003fff0007fe0000 0x0001c63e1c3e1c00

def z242 : W := mkw 0x55bb7a6a8529bcea 0x2babe5fb937b92b1 0x1ffff0ff8781e0ff 0x03ffb5b9d3f9d273

def z243 : W := mkw 0x8a3084d462380000 0x4104180000daf400 0xfffffffffffe0000 0x000e380003fffc00

def z244 : W := mkw 0x9e338cdc66781000 0xc10ffec060daf400 0xfffffffffffe0000 0x000fffc1e3fffc00

def z245 : W := mkw 0x0008000000008000 0x0080002000200020 0x003ff000000000f0 0x0001803800380060

def z246 : W := mkw 0x211d506a850ce8aa 0x1be1253592359371 0xe03fffff8781ffff 0x03f1f5ffd23fd3f3

def z247 : W := mkw 0x9c03089844501000 0xc20ffedaf4806000 0xffc000fff8000000 0x000fffffffc1e000

def z248 : W := mkw 0x10aa2a0000208440 0x0082c02a006a0020 0x0003f00000000000 0x0001803800380000

def z249 : W := mkw 0x0011106885082022 0x0b21241190119011 0x003ff0ff8780000f 0x03f1b401d239d013

def z250 : W := mkw 0x30af2a080464c440 0x12c3e63e946e0160 0x003fff00000000f0 0x0001c63e1c3e0060

def z251 : W := mkw 0x0401000804001000 0x820924daf4000000 0x0000000000000000 0x0001b5fffc000000

def z252 : W := mkw 0x9f3bdcfee778b8aa 0xcbaffffbf6fbf631 0xffffffffffffe0ff 0x03fffffffffffe73

def z253 : W := mkw 0xed4441b358957b9d 0xf86c19c56b856bde 0xffc000fff801ffff 0xfffe39c7ffc1e3ff

def z254 : W := mkw 0x2004010008844111 0x104000040804094a 0x003c0f0007fe00f0 0x03f046061c061c63

def z255 : W := mkw 0x5dab6a1a44619cc8 0xa28ffffaf76a02a0 0x1fc3f00000000000 0x000ffffffff80000

def z256 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e3181c3c1e39c

def z257 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00000000001ff00 0x0000004000000380

def z258 : W := mkw 0x2004010008844111 0x104000040804094a 0x000000e07fffffff 0xfff00e463c003fff

def z259 : W := mkw 0x8840009150100204 0xc004180060806004 0x0000000078000000 0xfc0008002000200c

def z260 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fbfb9fc000000

def z261 : W := mkw 0x0001000804000000 0x0001240000000000 0x0000000000000000 0x0001b40000000000

def z262 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fb1fffc000000

def z263 : W := mkw 0x9a3b9cdce7788022 0x4387fe3090faf421 0xfffffffffffe00f0 0x03fffe3813fffc63

def z264 : W := mkw 0x75ae6a220025fcc8 0x38eac1ef036f03f0 0xffffffff8001ffff 0x000ff1ffc3ffc3f0

def z265 : W := mkw 0xcc40009150111204 0xe00c18c061806084 0x1fc0000000000000 0x000e000001c00000

def z266 : W := mkw 0x9e338cdc66781000 0x410ffeca00daf400 0xfffffffffffe0000 0x000ffffe03fffc00

def z267 : W := mkw 0x1c02081040401000 0x800edaca64000000 0x0000000000000000 0x000fcbfe2c000000

def z268 : W := mkw 0xdd6248b350313a8c 0xe82ed9c163cb6294 0xfffffffff801ff0f 0xfc0ff9c1e3ffe39c

def z269 : W := mkw 0x1823081844600000 0x0007fe00004a0000 0xffffff0000000000 0x000ffe0003fe0000

def z270 : W := mkw 0x7ca72a1844655440 0xb24ffedef54e01c0 0xffc00f0000001f00 0x000ffffffdc60180

def z271 : W := mkw 0x30ae2b0008a4c551 0x10c2c02e086e096a 0xe03fffe07fffffff 0xfff1ce7e3c3e3fff

def z272 : W := mkw 0x1c23081844601000 0x820ffedaf44a0000 0xffffff0000000000 0x000ffffffffe0000

def z273 : W := mkw 0x208c22000004c440 0x10c0002e00240160 0x00000000000000f0 0x0000003e00000060

def z274 : W := mkw 0x9a228c9462700000 0x4006da0000ca6400 0x1fc0000000000000 0x000e000001c00000

def z275 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0xe03fffffffffe0ff 0x03f1ffb9d23ffe73

def z276 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07ffe1f00 0xfc004e462c063d8c

def z277 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0xffc3f0000001ff00 0x000f81f803f80380

def z278 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0000781e0ff 0x03f185b9d0381273

def z279 : W := mkw 0xdd4348bb54513a8c 0xe82fffc163816294 0xffc000fff801ff0f 0xfc0fffc1e3c1e39c

def z280 : W := mkw 0x0011004804080000 0x0301241090109000 0x003ff0ff87800000 0x0001b5b9d239d000

def z281 : W := mkw 0x31bf7a6a852cecea 0x1be3e53f927f9371 0x003fffff8781e0ff 0x03f1f5bfd23fd273

def z282 : W := mkw 0x4500400200011888 0x200801c003000280 0x000000000001ff00 0x000001c000000380

def z283 : W := mkw 0x54a22a0000211440 0x200ac0ca014a0080 0x1fc0000000000000 0x000e000001c00000

def z284 : W := mkw 0x8a1184dc66580000 0x41053e000090f400 0xe03c0ffffffe0000 0x00007e000007fc00

def z285 : W := mkw 0x60a4220000254440 0x30400004014e01c0 0xffc00f0000001f00 0x0000000001c60180

def z286 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f03401d239d273

def z287 : W := mkw 0x9a328cd462780000 0x4106da0000daf400 0xfffffffffffe0000 0x000e4a0003fffc00

def z288 : W := mkw 0x2004010008844111 0x104000040804094a 0x000000000001ffff 0xfff00000000003ff

def z289 : W := mkw 0x0100402200002888 0x0820010102010210 0x000000ff8001e00f 0x000000000201c210

def z290 : W := mkw 0xdd4248b350513a8c 0xe82edbcb67816294 0xffc000fff801ff0f 0xfc0e7bc7efc1e39c

def z291 : W := mkw 0x0000000000000000 0x0000000000000000 0x003c0f0007fe0000 0x0000460000061c00

def z292 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f1fffffe39d273

def z293 : W := mkw 0x75bf6a4a042ddcc8 0x31cbe5ee037e93e0 0xffffffff8781fff0 0x000ff5fe03ffd3e0

def z294 : W := mkw 0x0108400200008888 0x0080012002200220 0x0003f00000000000 0x000181b802380000

def z295 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0x1fc3f0fffffe0000 0x000fbe0003f9fc00

def z296 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe07801ffff 0xfc0fc9fe23fe23fc

def z297 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0x1fc3f01f80000000 0x000fb1b9c3f9c000

def z298 : W := mkw 0x32378d4c2eec4111 0x1143e604085e9d4a 0xe03fffe07fffffff 0xfff1ce463c3e3fff

def z299 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffff007ffe0000 0x000fce0001fe3c00

def z300 : W := mkw 0x0000000000000000 0x0000000000000000 0x003c00000001e0f0 0x0000000000000260

def z301 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0f000001ffff 0xfff040463c0603ff

def z302 : W := mkw 0x454850239101baae 0xaaa801f1f32102b5 0x000000000001ffff 0xfff001f9f00003ff

def z303 : W := mkw 0x0000000000000000 0x0000000000000000 0xe03c0fe07fffe0ff 0x03f04e0010063e73

def z304 : W := mkw 0x4500400200011888 0x200801c003000280 0x1fc0000000000000 0x000e018003c00000

def z305 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000ffbffec000000

def z306 : W := mkw 0x55bb7a6a8529bcea 0x2babe5fb937b92b1 0x1fc3f01f80000000 0x000fb1b9c3f9c000

def z307 : W := mkw 0x5502480200011888 0x200ac1ca03000280 0xffc000000001ff00 0x000fc1fe03c00380

def z308 : W := mkw 0xfdef6abb5475fecc 0xfaeffffff7ef63f4 0xfffffffff801ffff 0xfc0fffffffffe3fc

def z309 : W := mkw 0x001910688508a022 0x0ba1243190319031 0x003ff0ff878000ff 0x03f1b439d039d073

def z310 : W := mkw 0xc040008110110204 0x6000000001806084 0xffc0000078001f00 0xfc00000001c0218c

def z311 : W := mkw 0xcc4000b150113204 0xe82c18c161816094 0xffc000fff8001f0f 0xfc0e3841e1c1e19c

def z312 : W := mkw 0xfea6ae9462755440 0x704edace01ce65c0 0xffc00f00787e1f00 0x000e4a4601c62d80

def z313 : W := mkw 0x0800001040000000 0x0004180000000000 0x0000000000000000 0x000e380000000000

def z314 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff0007fffff0 0x03ffc7fe1ffe1fe3

def z315 : W := mkw 0x3c07081844445000 0x924ffedef4040140 0xe03c0f000001fff0 0x000ffffffc0603e0

def z316 : W := mkw 0x010850228100a8aa 0x0aa0013192210231 0x003ff0000001e0ff 0x03f181b9d2380273

def z317 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffc3ff1ff87e0000 0x000ffa0003ffec00

def z318 : W := mkw 0x12338c4c26680000 0x0103e600005a9400 0xffffff0007fe0000 0x000fc60003fe1c00

def z319 : W := mkw 0x9e138cdc66581000 0xc30ffedaf490f400 0x000000fffffe0000 0x000ffffffc01fc00

def z320 : W := mkw 0x1d0b481a44409888 0x828ffffaf6200220 0x003ff0000001e0f0 0x000ffffffe380260

def z321 : W := mkw 0x2004010008844111 0x104000040804094a 0x003c0f0007ffffff 0xfff046463c061fff

def z322 : W := mkw 0xba268d946af44111 0x5046da0408ce6d4a 0xfffc0fe07fffffff 0xfffe4e463dc63fff

def z323 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1fc3f00000000000 0x000fc1fe03f80000

def z324 : W := mkw 0xdc43089954511204 0xe20ffedaf5806084 0xffc0000078001f00 0xfc0ffffffdc0218c

def z325 : W := mkw 0x758e6a020005dcc8 0x30cac1ee032403e0 0x000000000001fff0 0x000fc1fe000003e0

def z326 : W := mkw 0x9a338cdc66780000 0xc307fe10f4daf400 0xfffffffffffe0000 0x000ffe01fffffc00

def z327 : W := mkw 0x0111406a04082888 0x0921250102119210 0x003ff0ff8781e00f 0x0001b581c239d210

def z328 : W := mkw 0x3caf2a184464d440 0x92cffefef46e0160 0x003fff00000000f0 0x000ffffffc3e0060

def z329 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0f0007fffff0 0x03f046461c061fe3

def z330 : W := mkw 0x30bf3a48852cc462 0x13c3e43e907e9161 0x003fff00078000f0 0x03f1c43e103e1063

def z331 : W := mkw 0xcd4140bb54513a8c 0xea2d3fd1f7816294 0xffc000fff801ff0f 0xfc0e3fc1ffc1e39c

def z332 : W := mkw 0xcd4040b350113a8c 0xea2c19dbf7816294 0xffc000fff801ff0f 0xfc0e39ffffc1e39c

def z333 : W := mkw 0x1c02081040401000 0x800edaca64000000 0x0000000000000000 0x000e000000000000

def z334 : W := mkw 0x010850228100a8aa 0x0aa0013192210231 0x003c00e00781e0ff 0x03f005b9d0001273

def z335 : W := mkw 0x804000a110102204 0x4820000100816014 0x000000fff800000f 0xfc0000000001e01c

def z336 : W := mkw 0x0010106081082022 0x0920000100119011 0x000000ff8780000f 0x03f000000001d013

def z337 : W := mkw 0x658c62020005dcc8 0xb2c801fef72403e0 0x000000000001fff0 0x000001fffc0003e0

def z338 : W := mkw 0x75ae6a020025dcc8 0xb2cac1fef76e03e0 0xffffff000001fff0 0x000fc1fffffe03e0

def z339 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000e7e47fc000000

def z340 : W := mkw 0x658c62020005dcc8 0x30c801ee032403e0 0xe03c0f000001fff0 0x000041fe000603e0

def z341 : W := mkw 0x75af6a0a0465dcc8 0x32cbe7fe976e03e0 0xffffff000001fff0 0x000fc7fe1ffe03e0

def z342 : W := mkw 0x8339d4eea738a8aa 0x4ba1253192fbf631 0xffffffffffffe0ff 0x03f1b5b9d3fffe73

def z343 : W := mkw 0xf7beeec6223ddcc8 0x71cac1ee03fef7e0 0xfffffffffffffff0 0x000fc1fe03ffffe0

def z344 : W := mkw 0x4400000000011000 0x200800c001000080 0xffc0000000001f00 0x000e004001c00180

def z345 : W := mkw 0x9a338cdc66780000 0x4307fe1a94daf400 0xfffffffffffe0000 0x000ffe3e1ffffc00

def z346 : W := mkw 0x111b586a8548a8aa 0x0ba3e73b96319231 0x003ff0ff8781e0ff 0x03f1f7bfde39d273

def z347 : W := mkw 0xdd5b58fbd559baae 0xebaffffbf7b1f2b5 0xfffff0ffff81ffff 0xfffffffffff9f3ff

def z348 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000001ff0f 0xfc0000402000039c

def z349 : W := mkw 0x0119506a8508a8aa 0x09a1252102319231 0x003ff0ff8781e0ff 0x03f1b4000239d273

def z350 : W := mkw 0x1022080000200000 0x0002c000004a0000 0xffffffe07ffe0000 0x000fce0003fe3c00

def z351 : W := mkw 0x6504410208855999 0x304801c40b040bca 0xfffc0fe07fffffff 0xfffe4fc63fc63fff

def z352 : W := mkw 0x0011106885082022 0x0b21241190119011 0x003c00ff8781e0ff 0x03f03401d001d273

def z353 : W := mkw 0x2004010008844111 0x104000040804094a 0x003c0f0007fe00f0 0x03f04e463c061c63

def z354 : W := mkw 0x2004000000044000 0x1040000400040140 0xe03c0fe00781ffff 0x03f04446100613f3

def z355 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffc3f0fff8000000 0x000fb80003f9e000

def z356 : W := mkw 0x8220848422300000 0x4000000000ca6400 0xffc00f00787e0000 0x0000000001c62c00

def z357 : W := mkw 0x0000010008800111 0x000000000800080a 0x0000000007fe0000 0x03f006001c001c03

def z358 : W := mkw 0x0040002110002204 0x8820000160010014 0x000000000000000f 0xfc000001e000001c

def z359 : W := mkw 0x2004010008844111 0x104000040804094a 0x003c0f0007fe00f0 0x03f0000000061c63

def z360 : W := mkw 0x4540402310013a8c 0xa82801c163010294 0x000000ff8001ff0f 0xfc0031c1e201c39c

def z361 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x00003181c0000000

def z362 : W := mkw 0x12228c0422600000 0x0002c200004a0400 0x00000f00007e0000 0x0000420000060c00

def z363 : W := mkw 0x1c02081040401000 0x820edadaf4000000 0x0000000000000000 0x000e4bfffc000000

def z364 : W := mkw 0x1c0309184cc01111 0x820ffedafc00080a 0x000000e07ffe000f 0xfffffffffc003c1f

def z365 : W := mkw 0x2004010008844111 0x104000040804094a 0x000000000001ffff 0xfff04e463c0003ff

def z366 : W := mkw 0x112a480200208888 0x0082c120026a0220 0xffffff000001e0f0 0x000fc1b803fe0260

def z367 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffffffffffe0ff 0x03fffe0013fffe73

def z368 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe07ffffff0 0x000fcffe03fe3fe0

def z369 : W := mkw 0x8c00009040101000 0xc00c18c060806000 0xffc000fff8000000 0x000e39c1e3c1e000

def z370 : W := mkw 0x1003080804400000 0x0203e61a94000000 0x0000000000000000 0x0001f7bfdc000000

def z371 : W := mkw 0x0119504a850888aa 0x0381253092309221 0x003ff0000781e0f0 0x03f185b812381263

def z372 : W := mkw 0x2004010008844111 0x104000040804094a 0x00000f00007e0000 0x000042060c060c00

def z373 : W := mkw 0x3406080000045000 0x104ac0ce00040140 0xe03c0f000001fff0 0x000fc1fe000603e0

def z374 : W := mkw 0x0400000000001000 0x800800c060000000 0x0000000000000000 0x000001c1e0000000

def z375 : W := mkw 0xcd4850b3d111baae 0xeaac19f1f3a162b5 0xffc000fff801ffff 0xfffe39f9f3c1e3ff

def z376 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000f00787e0000 0x00004a0000062c00

def z377 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fffb9c0000000

def z378 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000ff1ffc0000000

def z379 : W := mkw 0x4500400200011888 0x200801c003000280 0xffc000e07801ff0f 0xfc0e09c023c0239c

def z380 : W := mkw 0x658c62020005dcc8 0x30c801ee032403e0 0x003ff0000001fff0 0x000181fe023803e0

def z381 : W := mkw 0x30ae2a000024c440 0x10c2c02e006e0160 0xffffff00000000f0 0x000fc03e03fe0060

def z382 : W := mkw 0x9c4308b954503204 0xca2ffedbf4816014 0x000000fff800000f 0xfc0ffffffc01e01c

def z383 : W := mkw 0x71ae6a020025ccc8 0x30c2c12e036e03e0 0xffffff000001fff0 0x0001c03e03fe03e0

def z384 : W := mkw 0x0001000804400000 0x0201261094000000 0x0000000000000000 0x000006001c000000

def z385 : W := mkw 0x8a1184dc66580000 0xc3053e10f490f400 0x000000fffffe0000 0x00003e01fc01fc00

def z386 : W := mkw 0x61ac630208a5cdd9 0x30c001240b6e0bea 0xffffffe07fffffff 0xfff0000003fe3fff

def z387 : W := mkw 0x1803081844400000 0x8207fe10f4000000 0x0000000000000000 0x000ffe01fc000000

def z388 : W := mkw 0x34ae2a000024d440 0x10cac0ee006e0160 0x003fff00000000f0 0x000fc1fe003e0060

def z389 : W := mkw 0x1402080000001000 0x000ac0ca00000000 0x0000000000000000 0x000f81b800000000

def z390 : W := mkw 0x3c06091048c45111 0x904edace6c04094a 0xe0000f00787e1f00 0xfc0e4a462c062d8c

def z391 : W := mkw 0x9b3bdcfee778a8aa 0x4ba7ff3192fbf631 0x1fc3f01f80000000 0x000fb1b9c3f9c000

def z392 : W := mkw 0xaa1585dc6edc4111 0x51453e040894fd4a 0xe03c0fffffffffff 0xfff07e463c07ffff

def z393 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc0001ff8001f00 0xfc0e39c1e3c1e18c

def z394 : W := mkw 0x9a238c9c66700000 0x4007fe0000ca6400 0xffc00f00787e0000 0x000ffe0001c62c00

def z395 : W := mkw 0x75a66a0200255cc8 0x304ac1ce034e03c0 0xffc00f000001ff00 0x000e41c603c60380

def z396 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0x000000fff801ff0f 0xfc0039c1e001e39c

def z397 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0x1fffff00000000f0 0x000fc1be03fe0060

def z398 : W := mkw 0x1402080000001000 0x000ac0ca00000000 0x0000000000000000 0x000fcffe3c000000

def z399 : W := mkw 0x0800001040400000 0x80041a0064000000 0x0000000000000000 0x00000a002c000000

def z400 : W := mkw 0xbb3fddfeeffce9bb 0x5be7ff359affff7b 0xffffffffffffffff 0xffffffffffffffff

def z401 : W := mkw 0x1e338c5c66681000 0x830ffedaf45a9400 0x003fff0007fe0000 0x000ffffffc3e1c00

def z402 : W := mkw 0x0000000000000000 0x0000000000000000 0xe03c0f0000000000 0x0000400000060000

def z403 : W := mkw 0xa804019048944111 0x504418040884694a 0xfffc0fffffffffff 0xfffe7e463fc7ffff

def z404 : W := mkw 0x9e338cdc66781000 0xc10ffeca64daf400 0xfffffffffffe0000 0x000ffe462ffffc00

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00000e078000000 0x0000080000002000

def z406 : W := mkw 0x1003080804400000 0x0203e61a94000000 0x0000000000000000 0x0001ce7e3c000000

def z407 : W := mkw 0xff77cdff7efd7b9d 0xf96fffc56bdfffde 0xffffffffffffffff 0xffffffc7ffffffff

def z408 : W := mkw 0x0801001844400000 0x82053e10f4000000 0x0000000000000000 0x00003001c0000000

def z409 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0x1fc0001f8001ff0f 0xfc0e31c1e3c1c39c

def z410 : W := mkw 0xe1ec62a31035eecc 0x78e0012503ef63f4 0xfffffffff801ffff 0xfc00000003ffe3fc

def z411 : W := mkw 0x010850228100a8aa 0x0aa0013192210231 0x0000000000000000 0x000001b9c0000000

def z412 : W := mkw 0x658c72228105fcea 0x3ae801ff932503f1 0x000000000001ffff 0x03f001ffd00003f3

def z413 : W := mkw 0x71ae6a020025ccc8 0x30c2c124036e03e0 0xffffff000001fff0 0x000fc00003fe03e0

def z414 : W := mkw 0xffbfefde6efdddd9 0x71cfffee0bfeffea 0xffffffffffffffff 0xfffffffe3fffffff

def z415 : W := mkw 0x1402080000001000 0x820ac0daf4000000 0x0000000000000000 0x000fc1fffc000000

def z416 : W := mkw 0x010840220000a888 0x08a0012102210230 0x003ff0ff8001e0ff 0x0001b1b9c239c270

def z417 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x0003f01f80000000 0x0001b5b9d239c000

def z418 : W := mkw 0x1022080000200000 0x0002c000004a0000 0xffc00f0000000000 0x000e400001c60000

def z419 : W := mkw 0xedcc62b35015fecc 0xf8ec19ef63a563f4 0xffc000fff801ffff 0xfc0e39ffe3c1e3fc

def z420 : W := mkw 0x4100400200010888 0x2000010003000280 0xffc000000001ff00 0x0000000003c00380

def z421 : W := mkw 0xdf33ccde66791888 0x610fffc003daf680 0xffffffffffffff00 0x000fffc003ffff80

def z422 : W := mkw 0x75af6a0a0425dcc8 0x32cbe5fe936e03e0 0xffffff000001fff0 0x000ff5ffd3fe03e0

def z423 : W := mkw 0x0519506a8508b8aa 0x8ba925fbf6319231 0x003ff0ff8781e0ff 0x03f1b5fffe39d273

def z424 : W := mkw 0x9b3bdcfee778a8aa 0x49a7ff2102fbf631 0xffffffffffffe0ff 0x03fffe0003fffe73

def z425 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0x1fc3f0000001fff0 0x000f81fe03f803e0

def z426 : W := mkw 0x1803081844400000 0x8207fe1af4000000 0x0000000000000000 0x0001fe3ffc000000

def z427 : W := mkw 0x0011106885082022 0x0b21241190119011 0x0000001f80000000 0x00003001c001c000

def z428 : W := mkw 0xc15950eb9519aaae 0x6ba1253193b1f2b5 0xfffff0ffff81ffff 0xfff1b5b9d3f9f3ff

def z429 : W := mkw 0xffbfeede667ddcc8 0xf3cffffef7fef7e0 0xfffffffffffffff0 0x000fffffffffffe0

def z430 : W := mkw 0x4588620200019cc8 0x208801ea032002a0 0x0000000000000000 0x000001b800000000

def z431 : W := mkw 0x1c03081844401000 0x000ffeca00000000 0x0000000000000000 0x000ffffe00000000

def z432 : W := mkw 0x2004000000044000 0x1040000400040140 0xe03c0f000001fff0 0x00004e463c0603e0

def z433 : W := mkw 0x0001000804000000 0x0201241090000000 0x003c00e00781e0ff 0x03f1b5b9d0001273

def z434 : W := mkw 0x2004000000044000 0x1040000400040140 0x003c0f00000000f0 0x0000400600060060

def z435 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc0001f8001ff00 0x000e31c1c3c1c380

def z436 : W := mkw 0x41a8620200218cc8 0x20800120036a02a0 0x1fc3f00000000000 0x0000000003f80000

def z437 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000ff7bfdc000000

def z438 : W := mkw 0x618c62020005ccc8 0x30c00124032403e0 0x000000000001fff0 0x00000000000003e0

def z439 : W := mkw 0x881100d844180000 0x41053c000090f000 0xfffff0ffff800000 0x000fbc0003f9f000

def z440 : W := mkw 0x011850628108a8aa 0x09a0012102319231 0x003ff0ff8781e0ff 0x03f03181c239d273

def z441 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x0003f0ff8001e00f 0x0001b1b9c239c210

def z442 : W := mkw 0xcd40409350111a8c 0xe00c19c063806284 0xffc000007801ff00 0xfc0e09c023c0238c

def z443 : W := mkw 0x823084c422380000 0x4100000000daf400 0xfffffffffffe0000 0x00004e0003fffc00

def z444 : W := mkw 0x4540402310013a8c 0xa82801c163010294 0xffc000000001ff0f 0xfc0e01c1e3c0039c

def z445 : W := mkw 0xfeb7aedc667d5440 0x714ffece01def5c0 0xfffffffffffe1f00 0x000ffe4603fffd80

def z446 : W := mkw 0x1803081844400000 0x0007fe0000000000 0x0000000000000000 0x000ffe463c000000

def z447 : W := mkw 0x010850228100a8aa 0x08a0012102210231 0x000000000001e0ff 0x03f0000000000273

def z448 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffc00f000001fff0 0x000e41fe01c603e0

def z449 : W := mkw 0xe14441a318956b9d 0x786001050b856bde 0xfffc0fffffffffff 0xfff04e463fc7ffff

def z450 : W := mkw 0x0000000000000000 0x0000000000000000 0xe03c0fe07fffff0f 0xfc004e4020063f9c

def z451 : W := mkw 0x0100402200002888 0x0820010102010210 0xe00000fff801ff0f 0xfc0039c1e201e39c

def z452 : W := mkw 0x0400000000001000 0x820800daf4000000 0x0000000000000000 0x00004ffffc000000

def z453 : W := mkw 0xba378cdc667c4000 0x5147fe0400def540 0xfffffffffffffff0 0x000ffe4603ffffe0

def z454 : W := mkw 0x0001000804000000 0x0201241090000000 0x0000000000000000 0x0001fffffc000000

def z455 : W := mkw 0xba378ddc6efc4111 0x5147fe0408defd4a 0xffffffffffffffff 0xfffffe0003ffffff

def z456 : W := mkw 0x1402080000001000 0x000ac0ca00000000 0x0000000000000000 0x000e404600000000

def z457 : W := mkw 0x31ae6a020024ccc8 0x10c2c12e026e0360 0x003fff000001e0f0 0x0001c1be023e0260

def z458 : W := mkw 0x8800009040100000 0x4004180000806000 0xfffc0ffffffe0000 0x000e7e0003c7fc00

def z459 : W := mkw 0x0801001844400000 0x00053e0000000000 0x0000000000000000 0x00003e0000000000

def z460 : W := mkw 0x123b9c4ca7688022 0x0383e630907a9421 0x003fff0007fe00f0 0x03f1c638103e1c63

def z461 : W := mkw 0x1d0b583ac540b8aa 0x8aaffffbf6210231 0x000000000001e0ff 0x03fffffffc000273

def z462 : W := mkw 0x0109502a8500a8aa 0x0aa1253192210231 0x000000000001e0ff 0x03f1b5b9d0000273

def z463 : W := mkw 0x658c63020885ddd9 0x30c801ee0b240bea 0x000000000001ffff 0xfff001fe3c0003ff

def z464 : W := mkw 0x9a228c9462700000 0x4006da0000ca6400 0xffc00ffff87e0000 0x000e7a0003c7ec00

def z465 : W := mkw 0x9a228c9462700000 0x4006da0000ca6400 0xffffff00787e0000 0x000fca0003fe2c00

def z466 : W := mkw 0xffffeeff767dfecc 0xf9efffef63fff7f4 0xffffffffffffffff 0xfc0fffffe3fffffc

def z467 : W := mkw 0xdf73ccff76793a8c 0xe92fffc163dbf694 0xfffffffffffe0000 0x000fff81c3fffc00

def z468 : W := mkw 0xfd4749bb5cd57b9d 0xfa6fffdfff856bde 0xfffc0fffffffffff 0xffffffffffc7ffff

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000404600000000

def z470 : W := mkw 0x61bd726a852decea 0x3be12535937f93f1 0xffffffff8781ffff 0x03f1b5b9d3ffd3f3

def z471 : W := mkw 0x200501080c844111 0x124124149804094a 0xe03c0fe07fffffff 0xfff1fffffc063fff

def z472 : W := mkw 0x658c63020885ddd9 0x30c801ee0b240bea 0xe03c0fe07fffffff 0xfff04ffe3c063fff

def z473 : W := mkw 0x211d516a8d8ce9bb 0x1be125359a359b7b 0x003ff0ff8781ffff 0xfff1b5fffe39d3ff

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e07800000f 0xfc0008002000201c

def z475 : W := mkw 0xe14441a318956b9d 0x786001050b856bde 0xfffc0fffffffffff 0xfff0000003c7ffff

def z476 : W := mkw 0x300709080cc44111 0x1243e61e9c04094a 0xe03c0fe07fffffff 0xfff1ce7e3c063fff

def z477 : W := mkw 0x0019104885088022 0x0381243090309021 0x003ff0ff878000f0 0x03f1b4381239d063

def z478 : W := mkw 0xed4441b358957b9d 0xf86c19c56b856bde 0xffc00ffff87fff0f 0xfc0e7bc7efc7ef9c

def z479 : W := mkw 0x150a480200009888 0x008ac1ea02200220 0x003ff0000001e0f0 0x000fc1fe02380260

def z480 : W := mkw 0xcf70c4f772393a8c 0xe92c19c163dbf694 0xffffffffffffff0f 0xfc0e39c1e3ffff9c

def z481 : W := mkw 0x4d00401240011888 0xa00c19c063000280 0xffc000000001ff00 0x000e39c1e3c00380

def z482 : W := mkw 0x1803081844400000 0x0207fe1090000000 0x0000000000000000 0x000fffb9d0000000

def z483 : W := mkw 0xdc42089150511204 0xe00edaca65806084 0xffc0000078001f00 0xfc0e4a462dc0218c

def z484 : W := mkw 0x4440000110011204 0xa00800c061000084 0x0000000000001f00 0xfc0000402000018c

def z485 : W := mkw 0x9a738cfd76782204 0xc927fe0160dbf414 0xfffffffffffe000f 0xfc0ffe01e3fffc1c

def z486 : W := mkw 0xcf51c4ff76593a8c 0xe92d3fc16391f694 0xffc000ffffffff0f 0xfc0e3fc1e3c1ff9c

def z487 : W := mkw 0x011850628108a8aa 0x09a0012102319231 0x003ff0ff8781e0ff 0x03f004001239d273

def z488 : W := mkw 0x0c00001040001000 0x800c18c060000000 0x0000000000000000 0x000e7fc7fc000000

def z489 : W := mkw 0x20ac22000024c440 0x10c00024006e0160 0x003fff00000000f0 0x00000000003e0060

def z490 : W := mkw 0xa23485c42abc4111 0x5140000408defd4a 0xffffffffffffffff 0xfff0000003ffffff

def z491 : W := mkw 0x75bf7b6a8dadfdfb 0x3bebe5ff9b7f9bfb 0xffffffffffffffff 0xffffffffffffffff

def z492 : W := mkw 0x823084c422380000 0x4100000000daf400 0x1fc3f01f80000000 0x0000000003f9c000

def z493 : W := mkw 0x0211844c26480000 0x0101260000109400 0x0000000007fe0000 0x0000060000001c00

def z494 : W := mkw 0x884001b158902315 0xc82418016881681e 0x000000fffffe000f 0xfff03e01fc01fc1f

def z495 : W := mkw 0x0001000804000000 0x0201241090000000 0x0000000000000000 0x0001b1b9c0000000

def z496 : W := mkw 0x65ac62020025dcc8 0x30c801ee036e03e0 0xffffff000001fff0 0x000001fe03fe03e0

def z497 : W := mkw 0xcd4140bb54113a8c 0xea2d3dd1f3816294 0xffc000fff801ff0f 0xfc0fbdf9f3c1e39c

def z498 : W := mkw 0x3406090008845111 0x104ac0ce0804094a 0xe03c0fe07fffffff 0xffffcffe3c063fff

def z499 : W := mkw 0x8800009040100000 0x4004180000806000 0xffc000fff801ff0f 0xfc0e384023c1e39c

def z500 : W := mkw 0x8a1184dc66580000 0x41053e000090f400 0x003ff0fffffe0000 0x0001be000239fc00

def z501 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000040010000000

def z502 : W := mkw 0x201501480c8c4111 0x114124040814994a 0xe03fffffffffffff 0xfff1fe463e3fffff

def z503 : W := mkw 0x1002080000000000 0x0002c00000000000 0x0000000000000000 0x000fc00000000000

def z504 : W := mkw 0xec44019158955315 0xf04c18c4698469ce 0xfffc0fe07fffffff 0xfffe4e463dc63fff

def z505 : W := mkw 0x884000b150102204 0xc824180160816014 0xe00000fff801ff0f 0xfc003841e001e39c

def z506 : W := mkw 0x74a62a0000255440 0x304ac0ce014e01c0 0xfffc0f000001fff0 0x000e404601c603e0

def z507 : W := mkw 0xdf7bdcfff779baae 0xebaffff1f3fbf6b5 0xffffffffffffffff 0xfffffff9f3ffffff

def z508 : W := mkw 0x210c40020004c888 0x10c0012402240360 0xe03fff000001fff0 0x0001c1fe023e03e0

def z509 : W := mkw 0x6544412318857b9d 0xb86801c56b050bde 0x000000000001ffff 0xfff001c7fc0003ff

def z510 : W := mkw 0x1c02081040001000 0x800ed8ca60000000 0x0000000000000000 0x000ff9ffe0000000

def z511 : W := mkw 0x211d516a8d8ce9bb 0x1be125359a359b7b 0xe03fffffffffffff 0xfff1b5b9d23fffff

def z512 : W := mkw 0x2004000000044000 0x1040000400040140 0xe03c0f000001fff0 0x00000000000603e0

def z513 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000fcffe3ffe03e0

def z514 : W := mkw 0x5522480200211888 0x200ac1c0034a0280 0xffffff000001ff00 0x000fc1c003fe0380

def z515 : W := mkw 0x9b3bdcfee778a8aa 0x4ba7ff3192fbf631 0x1ffff0ff8781e0ff 0x03ffb5b9d3f9d273

def z516 : W := mkw 0x280501184cc44111 0x92453e14fc04094a 0xe03c0fe07fffffff 0xfff07e47fc063fff

def z517 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff00787ffff0 0xfc0fcbfe2ffe2fec

def z518 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000e404603fe03e0

def z519 : W := mkw 0x884100b954502204 0xca253e11f4816014 0x000000fff800000f 0xfc003e01fc01e01c

def z520 : W := mkw 0xba378ddc6efc4111 0x5147fe0408defd4a 0xfffffffffffe1f00 0xfc0ffe462ffffd8c

def z521 : W := mkw 0x4519506a8509b8aa 0x2ba925f1933192b1 0xfffff0ff8781ffff 0x03ffb5f9d3f9d3f3

def z522 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e00001e00f 0x0000000000000210

def z523 : W := mkw 0x0000102081002022 0x0a20001190010011 0x000000000000000f 0x03f00001d0000013

def z524 : W := mkw 0x1813085844480000 0x0107fe0000109000 0x003ff0ff87800000 0x000ffe000239d000

def z525 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0x1fc3f01f80000000 0x000ffe0003f9c000

def z526 : W := mkw 0xcc40009150111204 0xe00c18c061806084 0xffc000fff8001f00 0xfc0e384023c1e18c

def z527 : W := mkw 0xed5d51fbdd9dfbbf 0xfbed3df5fbb5fbff 0xffffffffffffffff 0xffffffffffffffff

def z528 : W := mkw 0x8800009040100000 0x4004180000806000 0x000000fff8000000 0x000038000001e000

def z529 : W := mkw 0x1002080000000000 0x0002c00a00000000 0x0000000000000000 0x0001c03e00000000

def z530 : W := mkw 0xdf62ccb772713a8c 0xe82edbc163cb6694 0xffc00ffff87fff0f 0xfc0e7bc1e3c7ef9c

def z531 : W := mkw 0xc14040a310112a8c 0x6820010103816294 0xffc000fff801ff0f 0xfc00084023c1e39c

def z532 : W := mkw 0xdd4248b350113a8c 0xe82ed9cb63816294 0xffc000fff801ff0f 0xfc0ff9ffe3c1e39c

def z533 : W := mkw 0xddea6ab35031becc 0xe8aed9eb63eb62b4 0x1fc3f01f80000000 0x000fb1b9c3f9c000

def z534 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x00004e0000000000

def z535 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0x1fffff1f87fe0000 0x000ff60003ffdc00

def z536 : W := mkw 0xfdee6a935035decc 0xf0ced9ee63ee63e4 0xffffff007801fff0 0xfc0fc9fe23fe23ec

def z537 : W := mkw 0x2c04011048845111 0x904c18c46804094a 0xe03c0fe07fffffff 0xfffe7fc7fc063fff

def z538 : W := mkw 0x0800001040000000 0x8004180060000000 0x0000000000000000 0x00003801e0000000

def z539 : W := mkw 0x0119404a04088888 0x0181252002309220 0x003ff0ff8781e0f0 0x0001b5b80239d260

def z540 : W := mkw 0x2004010008844111 0x104000040804094a 0xe0000f00787fffff 0xfff04a463c062fff

def z541 : W := mkw 0x3c06091048c45111 0x904edace6c04094a 0xe03c0fe07fffffff 0xfffe4e463c063fff

def z542 : W := mkw 0x191b587ac548a8aa 0x0ba7ff3192319231 0x003ff0ff8781e0ff 0x03ffffb9d239d273

def z543 : W := mkw 0x0230844422280000 0x01000000005a9400 0x003fff0007fe0000 0x00000000003e1c00

def z544 : W := mkw 0x0c01001844001000 0x820d3cd0f0000000 0x0000000000000000 0x000fbdf9f0000000

def z545 : W := mkw 0x8000008000100000 0x4000000000806000 0xffc000fff8000000 0x0000000003c1e000

def z546 : W := mkw 0xfdee6ab35035fecc 0xf8eed9ef63ef63f4 0xffffff1f8001fff0 0x000ff1ffc3ffc3e0

def z547 : W := mkw 0xcc40009150111204 0xe00c18c061806084 0xffc000e07801ff0f 0xfc0e084021c0239c

def z548 : W := mkw 0x011850628108a8aa 0x09a0012102319231 0x0003f01f80000000 0x000000000239c000

def z549 : W := mkw 0x2004010008844111 0x104000040804094a 0x00000000000000f0 0x03f000061c000063

def z550 : W := mkw 0x77bfee4e266ddcc8 0x31cbe7ee037e97e0 0xffffff0007fffff0 0x000fc7fe03fe1fe0

def z551 : W := mkw 0x8a1184dc66580000 0x41053e000090f400 0x0000001f80000000 0x000030000001c000

def z552 : W := mkw 0x0000000000000000 0x0200001a94000000 0x0000000000000000 0x0000003e1c000000

def z553 : W := mkw 0x3d1f597acdccf9bb 0x9beffffffe359b7b 0xe03fffffffffffff 0xfffffffffe3fffff

def z554 : W := mkw 0x8a3184dc66780000 0x41053e0000daf400 0xfffffffffffe0000 0x00003e0003fffc00

def z555 : W := mkw 0x201d11488d8cc133 0x13c124349834996b 0xe03fffe07fffffff 0xfff1ce7e3c3e3fff

def z556 : W := mkw 0xdf73ccff76793a8c 0xeb2fffdbf7dbf694 0xffffffffffffff0f 0xfc0fffffffffff9c

def z557 : W := mkw 0x32378d4c2eec4111 0x1143e604085e9d4a 0x003fff0007fe00f0 0x03f1c6061c3e1c63

def z558 : W := mkw 0x7daf6a1a4465dcc8 0xb2cffffef76e03e0 0xffffff000001fff0 0x000ff1ffc3fe03e0

def z559 : W := mkw 0x1403080804401000 0x020be6da94000000 0x0000000000000000 0x000fc7fe1c000000

def z560 : W := mkw 0x0011104885080022 0x0301241090109001 0x0000000007800000 0x03f0040010001003

def z561 : W := mkw 0x2004010008844111 0x104000040804094a 0x003c0fe07ffe00ff 0xfff04e063c063c7f

def z562 : W := mkw 0x0011004804080000 0x0101240000109000 0x003ff0ff8781e0ff 0x03f1b4001239d273

def z563 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07fffffff 0xfff0404600063fff

def z564 : W := mkw 0x2004000000044000 0x1040000400040140 0xe0000f0000001f00 0x0000404600060180

def z565 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07fffffff 0xfff0040010063fff

def z566 : W := mkw 0x9803089844500000 0x4007fe0000806000 0xffc000fff8000000 0x000ffe0003c1e000

def z567 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07ffe00f0 0x03f04e061c063c63

def z568 : W := mkw 0x6484220000055440 0x304800ce010401c0 0x0000000000001f00 0x0000004600000180

def z569 : W := mkw 0xcc40009150111204 0xe00c18c061806084 0xffc0000078001f00 0xfc0e39c1e1c0218c

def z570 : W := mkw 0x0100402200002888 0x0820010102010210 0x000000000001e00f 0x00000181c0000210

def z571 : W := mkw 0x1d1b587ac548b8aa 0x8baffffbf6319231 0x003ff0ff8781e0ff 0x03ffb5b9d239d273

def z572 : W := mkw 0x8800009040100000 0x4004180000806000 0x1fc0001f80000000 0x000e300003c1c000

def z573 : W := mkw 0xffaeee966275dcc8 0x70cedbee03ee67e0 0xffffff00787ffff0 0x000fcbfe03fe2fe0

def z574 : W := mkw 0x0000010008800111 0x000000000800080a 0xe00000e07fffff0f 0xfff00e403c003f9f

def z575 : W := mkw 0xfbbfeede667dccc8 0x71c7ff2403fef7e0 0xfffffffffffffff0 0x000ffe0003ffffe0

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0xffc0000000000000 0x000e000003c00000

def z577 : W := mkw 0x6544412318857b9d 0xb86801c56b050bde 0xe03c0fe07fffffff 0xfff04fc7fc063fff

def z578 : W := mkw 0x0d00403240003888 0x882c19c162010210 0x000000ff8001e00f 0x000e39c1e201c210

def z579 : W := mkw 0x75be7a62812dfcea 0x39eac1ef037f93f1 0xffffffff8781ffff 0x03ffc1fe03ffd3f3

def z580 : W := mkw 0x0010004000080000 0x0100000000109000 0x003ff0ff87800000 0x000000000239d000

def z581 : W := mkw 0x9b33ccfe66782888 0x4927ff0102dbf610 0xffffffffffffe00f 0x000fff81c3fffe10

def z582 : W := mkw 0x0000002000002000 0x0820000100010010 0x000000ff8000000f 0x00003001c001c010

def z583 : W := mkw 0x0000010008800111 0x000000000800080a 0x000000000000000f 0xfff000003c00001f

def z584 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0x1fc0001f80000000 0x000e39c1e3c1c000

def z585 : W := mkw 0x0d19507ac508b8aa 0x8bad3df1f2319231 0x003ff0ff8781e0ff 0x03ffbdf9f239d273

def z586 : W := mkw 0x201511688d8c6133 0x1b6124159815995b 0xe03c0fffffffffff 0xfff07e47fc07ffff

def z587 : W := mkw 0x1c03081844401000 0x800ffec060000000 0x0000000000000000 0x000fffc1e0000000

def z588 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0x1ffff0ff87800000 0x000fb40003f9d000

def z589 : W := mkw 0xa23485c42abc4111 0x5140000408defd4a 0xffffffffffffffff 0xfff04e463fffffff

def z590 : W := mkw 0xcd5950fbd519baae 0xebad3df1f3b1f2b5 0x1ffff0ff8781e0ff 0x03ffb5b9d3f9d273

def z591 : W := mkw 0xfde66ab350357ecc 0xf86ed9cf63cf63d4 0xffc00ffff801ff0f 0xfc0e79c7e3c7e39c

def z592 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f184381239d273

def z593 : W := mkw 0x1c02081040401000 0x800edaca64000000 0x0000000000000000 0x000e7bc7ec000000

def z594 : W := mkw 0x4540402310013a8c 0xa82801c163010294 0xe00000e07801ff0f 0xfc0009c1e000239c

def z595 : W := mkw 0x0000010008800111 0x000000000800080a 0x003c00e07fffe0ff 0xfff00e003c003e7f

def z596 : W := mkw 0x0000000000000000 0x0000000000000000 0x003c0000078000f0 0x03f0040010001063

def z597 : W := mkw 0x74a62b0008a55551 0x304ac0ce094e09ca 0xfffc0fe07fffffff 0xfffe4e463dc63fff

def z598 : W := mkw 0x0001000804000000 0x0201241090000000 0x0000000000000000 0x0001843810000000

def z599 : W := mkw 0x210c41020884c999 0x10c001240a240b6a 0xe03fffe07fffffff 0xfff1cffe3e3e3fff

def z600 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07fffffff 0xfff046061c063fff

def z601 : W := mkw 0x1c131878c5483022 0x8b2ffedbf4119011 0x000000ff8780000f 0x03fffffffc01d013

def z602 : W := mkw 0x1003080804400000 0x0003e60000000000 0x0000000000000000 0x0001c60000000000

def z603 : W := mkw 0x61ac62020025ccc8 0x30c00124036e03e0 0xffffff000001fff0 0x0000404603fe03e0

def z604 : W := mkw 0xc15850e39119aaae 0x69a0012103b1f2b5 0xfffff0ffff81ffff 0xfff0000003f9f3ff

def z605 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0x1fc000fff800000f 0xfc0e3981e3c1e01c

def z606 : W := mkw 0x658c62020005dcc8 0x30c801ee032403e0 0xffc000000001fff0 0x000e01fe03c003e0

def z607 : W := mkw 0xdd4348bb54513a8c 0xea2fffdbf7816294 0xffc000fff801ff0f 0xfc0fb9f9e3c1e39c

def z608 : W := mkw 0x0109400a04008888 0x0281253092200220 0x003ff0000001e0f0 0x0001b5b9d2380260

def z609 : W := mkw 0x0011004804080000 0x0101240000109000 0x0003f01f80000000 0x0001b0000239c000

def z610 : W := mkw 0x1002080000400000 0x0002c20a04000000 0x0000000000000000 0x000042060c000000

def z611 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0f00787ffff0 0xfc004a462c062fec

def z612 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000084020000000

def z613 : W := mkw 0x0008100081008022 0x0280003090200021 0x00000000000000f0 0x03f0003810000063

def z614 : W := mkw 0x050850228100b8aa 0x8aa801fbf6210231 0x000000000001e0ff 0x03f001fffc000273

def z615 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0x003ffffffffe0000 0x0001fe00003ffc00

def z616 : W := mkw 0xcd00409240111888 0x600c19c003806280 0xffc000fff801ff00 0x000e39c003c1e380

def z617 : W := mkw 0x0000000000000000 0x0000000000000000 0x003c00e00781e0ff 0x03f0000000001273

def z618 : W := mkw 0x101b184885488022 0x0383e63a94309021 0x003ff000078000f0 0x03f1c63e1c381063

def z619 : W := mkw 0x1c02081040401000 0x800edaca64000000 0x0000000000000000 0x000e4e463c000000

def z620 : W := mkw 0x4559506b9509baae 0xaba925f1f33192b5 0x003ff0ff8781ffff 0xfff1b5f9f239d3ff

def z621 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07fffffff 0xfff00e003c063fff

def z622 : W := mkw 0x0c01001844401000 0x820d3ed0f4000000 0x0000000000000000 0x000e3fc1fc000000

def z623 : W := mkw 0xe3bce6c6223dccc8 0x71c0012403fef7e0 0xfffffffffffffff0 0x0000000003ffffe0

def z624 : W := mkw 0xec44019158955315 0xf04c18c4698469ce 0xffc00f00787e1f00 0xfc0e4a462dc62d8c

def z625 : W := mkw 0x1803081844400000 0x0007fe0000000000 0x0000000000000000 0x000fb00000000000

def z626 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff8000000 0x000e3981c3c1e000

def z627 : W := mkw 0xdf73ccff76793a8c 0xe92fffc163dbf694 0xffc3f0fff801ff0f 0xfc0fb9c1e3f9e39c

def z628 : W := mkw 0x2004010008844111 0x104000040804094a 0x003c00e00781ffff 0xfff004463c0013ff

def z629 : W := mkw 0x3026080000244000 0x1042c004004e0140 0xffffff000001fff0 0x000fc04603fe03e0

def z630 : W := mkw 0x2004000000044000 0x1040000400040140 0x000000000001fff0 0x00000046000003e0

def z631 : W := mkw 0xfdff7afbd53dfeee 0xfbeffdfff3fff3f5 0xffffffffff81ffff 0xfffffdfff3fff3ff

def z632 : W := mkw 0x92338ccc26780000 0x4103e60000daf400 0xfffffffffffe0000 0x0001c60003fffc00

def z633 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x0003f0ff8780000f 0x03f1b5b9d239d013

def z634 : W := mkw 0x0020000000200000 0x00000000004a0000 0xffffff0000000000 0x0000000003fe0000

def z635 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07fffffff 0xfff0084020063fff

def z636 : W := mkw 0x12338c4c26680000 0x0103e600005a9400 0x0003f00000000000 0x0001800000380000

def z637 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fb9f9e0000000

def z638 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fb5b9d0000000

def z639 : W := mkw 0x2104412208846999 0x186001050a050b5a 0xe03c0fffffffffff 0xfff07fc7fe07ffff

def z640 : W := mkw 0x823184cc26380000 0x4101240000daf400 0xfffffffffffe0000 0x0001b40003fffc00

def z641 : W := mkw 0x0019104885088022 0x0381243090309021 0x003ff000078000f0 0x03f1b5b9d0381063

def z642 : W := mkw 0x9e228c9462701000 0xc00edaca64ca6400 0xffc00f00787e0000 0x000e4a462dc62c00

def z643 : W := mkw 0x0000010008800111 0x000000000800080a 0x00000000787e0000 0xfc000a002c002c0c

def z644 : W := mkw 0xc94040b350112a8c 0xe824190163816294 0xffc000fff801ff0f 0xfc003801e3c1e39c

def z645 : W := mkw 0x2004010008844111 0x104000040804094a 0xe0000fe0787fff0f 0xfc004a462c062f9c

def z646 : W := mkw 0x8a1184dc66580000 0x41053e000090f400 0xffc000fffffe0000 0x000e3e0003c1fc00

def z647 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x000046061c000000

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x003c00e00781e0ff 0x03f04e463c001273

def z649 : W := mkw 0xcd5150fbd5193aae 0xeb2d3dd1f391f295 0xffc000ffff81ff0f 0xfffe3dc1f3c1f39f

def z650 : W := mkw 0x080101184cc00111 0x82053e10fc00080a 0x000000e07ffe000f 0xfff03e01fc003c1f

def z651 : W := mkw 0x2004000000044000 0x1040000400040140 0xe03c0fe07ffffff0 0x00004e4600063fe0

def z652 : W := mkw 0x3c0709184cc45111 0x924ffedefc04094a 0x000000000001ffff 0xfffffffffc0003ff

def z653 : W := mkw 0x5d43483b54413a8c 0xaa2fffdbf7010294 0x000000000001ff0f 0xfc0ffffffc00039c

def z654 : W := mkw 0x08111078c5482022 0x8b253e11f4119011 0x000000ff8780000f 0x03f03e01fc01d013

def z655 : W := mkw 0x75bf7a4a852ddcea 0x33cbe5fe937e93e1 0xffffff000781fff0 0x03ffc5fe13fe13e3

def z656 : W := mkw 0x0000000000000000 0x0000000000000000 0xe03c0fe07ffe0000 0x0000000000063c00

def z657 : W := mkw 0x0c00001040001000 0x800c18c060000000 0xe00000e07801ff0f 0xfc0e39c1e000239c

def z658 : W := mkw 0x011850628108a8aa 0x0ba0013192319231 0x003ff0ff8781e0ff 0x03f001b9d239d273

def z659 : W := mkw 0x1003080804400000 0x0203e61a94000000 0x0000000000000000 0x0001803800000000

def z660 : W := mkw 0x211d516a8d8ce9bb 0x1be125359a359b7b 0x003fffff87ffe0ff 0x03f1f7bfde3fde73

def z661 : W := mkw 0x7d8f6a1a4445dcc8 0xb2cffffef72403e0 0x000000000001fff0 0x000ffffffc0003e0

def z662 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e084023c1e39c

def z663 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fce7e3c000000

def z664 : W := mkw 0x61ac62020025ccc8 0x30c00124036e03e0 0xffffff000001fff0 0x000181b803fe03e0

def z665 : W := mkw 0x0000010008800111 0x000000000800080a 0xe03c0fe07ffe000f 0xfff04e003c063c1f

def z666 : W := mkw 0x0119516a8d88a9bb 0x0ba125319a319a3b 0x003ff0ffffffe0ff 0xfff1bfb9fe39fe7f

def z667 : W := mkw 0xf5ee6aa31035fecc 0x78eac1ef03ef63f4 0xfffffffff801ffff 0xfc0fc1fe03ffe3fc

def z668 : W := mkw 0x891950fac518a8aa 0x4ba53d3192b1f231 0xfffff0ffff81e0ff 0x03ffbdb9d3f9f273

def z669 : W := mkw 0xde628c9572711204 0xe00edac061ca6484 0xffc00f00787e1f00 0xfc0e4a4021c62d8c

def z670 : W := mkw 0x2004010008844111 0x104000040804094a 0xe0000f00787e1f00 0xfc004e463c062d8c

def z671 : W := mkw 0xc370c4e732392a8c 0x6920010103dbf694 0xffffffffffffff0f 0xfc00000003ffff9c

def z672 : W := mkw 0x0919507ac548a8aa 0x8ba53f31f6319231 0x003ff0ff8781e0ff 0x03f1bfb9fe39d273

def z673 : W := mkw 0x2004010008844111 0x104000040804094a 0xe0000f00787e1f00 0xfc00000000062d8c

def z674 : W := mkw 0x3c0709184cc45111 0x924ffedefc04094a 0x003c0f0007fe00f0 0x03fffffffc061c63

def z675 : W := mkw 0x75ae7a228125fcea 0x3aeac1ff936f03f1 0xffffff000001ffff 0x03ffc1ffd3fe03f3

def z676 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0xfffffffffffe0000 0x000fffb9c3fffc00

def z677 : W := mkw 0xffbffefee77dfcea 0x7befffff93fff7f1 0xffffffffffffffff 0x03ffffffd3fffff3

def z678 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00000e07801ff0f 0xfc0000000000239c

def z679 : W := mkw 0x8800009040100000 0x4004180000806000 0xffc0000078000000 0x000e080001c02000

def z680 : W := mkw 0x1d1b587ac548b8aa 0x8baffffbf6319231 0x0003f01f80000000 0x000ffffffe39c000

def z681 : W := mkw 0x65cc62231005fecc 0xb8e801ef632503f4 0x000000000001ffff 0xfc0001ffe00003fc

def z682 : W := mkw 0x8a5184fd76582204 0xc9253e016091f414 0x000000fffffe000f 0xfc003e01e001fc1c

def z683 : W := mkw 0xdf73ccff76793a8c 0xe92fffc163dbf694 0x1fc3f01f80000000 0x000fb181c3f9c000

def z684 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07fffffff 0xfff04a462c063fff

def z685 : W := mkw 0xdb73ccff76792a8c 0x6927ff0103dbf694 0xffffffffffffff0f 0xfc0ffe0003ffff9c

def z686 : W := mkw 0x001111688d882133 0x0b2124119811981b 0x000000fffffe000f 0xfff03e01fc01fc1f

def z687 : W := mkw 0x300709080cc44111 0x1243e61e9c04094a 0x003c0f0007fe00f0 0x03f1c63e1c061c63

def z688 : W := mkw 0xc54040a310113a8c 0xe82801c163816294 0xffc000fff801ff0f 0xfc0001c1e3c1e39c

def z689 : W := mkw 0xdfbbeede66799cc8 0x618fffea03faf6a0 0x1fc3f01f80000000 0x000fb1b803f9c000

def z690 : W := mkw 0x0000010008800111 0x000000000800080a 0x000000e07ffe000f 0xfff0000000003c1f

def z691 : W := mkw 0x0801001844400000 0x82053e10f4000000 0x0000000000000000 0x0001bfb9fc000000

def z692 : W := mkw 0x1c1b1858c5489022 0x838ffefaf4309021 0x003ff000078000f0 0x03fffffffc381063

def z693 : W := mkw 0x9822089040300000 0x4006d80000ca6000 0xfffffffff8000000 0x000ff80003ffe000

def z694 : W := mkw 0x0011004804080000 0x0101240000109000 0xe03ffffffffe0000 0x0001fe00023ffc00

def z695 : W := mkw 0x210c51228984e9bb 0x1ae001359a250b7b 0x000000000001ffff 0xfff001fffc0003ff

def z696 : W := mkw 0x0011004804080000 0x0101240000109000 0x000000ff87800000 0x000034000001d000

def z697 : W := mkw 0x30a62a0000244440 0x1042c00e004e0140 0x00000f0000000000 0x0000400600060000

def z698 : W := mkw 0xba378ddc6efc4111 0x5147fe0408defd4a 0xfffffffffffe00f0 0x03fffe061ffffc63

def z699 : W := mkw 0x2004000000044000 0x1040000400040140 0xe03c0fe07801ffff 0xfc004846200623fc

def z700 : W := mkw 0x9a339cfce7782022 0x4b27fe1190dbf411 0xfffffffffffe000f 0x03fffe01d3fffc13

def z701 : W := mkw 0x0100400200000888 0x0000010002000200 0x000000000001e000 0x0000018002000200

def z702 : W := mkw 0x12338c4c26680000 0x0103e600005a9400 0x003fffff87fe0000 0x0001f600023fdc00

def z703 : W := mkw 0x61bc7262812decea 0x39e00125037f93f1 0xffffffff8781ffff 0x03f0000003ffd3f3

def z704 : W := mkw 0x890040b240102888 0x4824190102816210 0xffc000fff801e00f 0x000e3981c3c1e210

def z705 : W := mkw 0xffbfeede667ddcc8 0x71cfffee03fef7e0 0xffffff1f8001fff0 0x000ff1fe03ffc3e0

def z706 : W := mkw 0x659d726a850dfcea 0x3be925ff933593f1 0x003ff0ff8781ffff 0x03f1b5ffd239d3f3

def z707 : W := mkw 0x69ad621a4465ccc8 0xb2c53f34f76e03e0 0xffffff000001fff0 0x00003e01fffe03e0

def z708 : W := mkw 0x12338c4c26680000 0x0303e61a945a9400 0x003fffff87fe0000 0x0001f7bfde3fdc00

def z709 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000fc07e03fe03e0

def z710 : W := mkw 0x894840b35010aa8c 0xc8a4192162a16234 0x003ff0fff801e0ff 0xfc01b9b9e239e27c

def z711 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x0003f01f8001e0ff 0x03f1b1b9c239c273

def z712 : W := mkw 0x890040b240102888 0x4824190102816210 0xffc000fff801ff0f 0xfc0e39c1e3c1e39c

def z713 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xfffc0fffffffff0f 0xfc0e39c1e3c7ff9c

def z714 : W := mkw 0x74a62a0000255440 0x304ac0ce014e01c0 0xffffff0000001f00 0x000fc1fe03fe0180

def z715 : W := mkw 0x0400000000001000 0x820800daf4000000 0x000000000001ff0f 0xfc0001fffc00039c

def z716 : W := mkw 0x0c00001040001000 0x820c18daf4000000 0x0000000000000000 0x000039fffc000000

def z717 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe000f 0x03fffe0013fffc13

def z718 : W := mkw 0x1c02081040401000 0x820edadaf4000000 0x0000000000000000 0x000e4bffec000000

def z719 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0xe03ff0ffff81ffff 0xfff1b5b9d239f3ff

def z720 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x0003f0ff8001e0ff 0x03f1b1b9d239c273

def z721 : W := mkw 0x9a328cd462380000 0x4106d80000daf400 0xfffffffffffe0000 0x000ff80003fffc00

def z722 : W := mkw 0x2004010008844111 0x104000040804094a 0xfffc0fe07fffffff 0xfffe4e463fc63fff

def z723 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0xffc3f0e07801ff0f 0xfc0f89f823f8239c

def z724 : W := mkw 0x9a338cdc66780000 0x4307fe1094daf400 0xfffffffffffe0000 0x000ffe001ffffc00

def z725 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x003c00000001e0f0 0x000ffffffc000260

def z726 : W := mkw 0x1c131858c5481022 0x830ffedaf4109001 0x0000000007800000 0x03fffffffc001003

def z727 : W := mkw 0x9c03089844501000 0xc20ffedaf4806000 0xfffc0ffffffe0000 0x000fffffffc7fc00

def z728 : W := mkw 0x0400000000001000 0x820800daf4000000 0x0000000000000000 0x000047fffc000000

def z729 : W := mkw 0x1c23081844601000 0x820ffedaf44a0000 0xffffffe07ffe0000 0x000ffffffffe3c00

def z730 : W := mkw 0x8a1184dc66580000 0x43053e109090f400 0x000000fffffe0000 0x00003e01d001fc00

def z731 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff01f878000f0 0x03f1b1b9c239d063

def z732 : W := mkw 0x8a1184dc66580000 0x43053e109490f400 0x000000fffffe0000 0x00003e001c01fc00

def z733 : W := mkw 0x211d516a8d8ce9bb 0x19e125250a359b7b 0xe03fffffffffffff 0xfff1fe00023fffff

def z734 : W := mkw 0x9a338cdc66780000 0x4307fe1a94daf400 0xfffffffffffe0000 0x000fffbfdffffc00

def z735 : W := mkw 0x885110f9d5582226 0xcb253e11f491f015 0x000000ffff80000f 0xfff03e01fc01f01f

def z736 : W := mkw 0x8a1184dc66580000 0xc3053e10f490f400 0x0000001f80000000 0x00003001c001c000

def z737 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x000000e07800000f 0xfc0ffffffc00201c

def z738 : W := mkw 0x0000000000000000 0x0200001090000000 0x0000000000000000 0x000001fffc000000

def z739 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f1f5ffd239d273

def z740 : W := mkw 0x4508400200019888 0x208801e0032002a0 0x1ffff0000001e0f0 0x000f81b803f80260

def z741 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xfffff0fff801ff0f 0xfc0fb9c1e3f9e39c

def z742 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x0003f01f800000f0 0x03f1b1b9d239c063

def z743 : W := mkw 0x75ee6a231025fecc 0xb8eac1ef636f03f4 0xffffffe07801ffff 0xfc0fc9ffe3fe23fc

def z744 : W := mkw 0x0c00001040001000 0x820c18daf4000000 0x0000000000000000 0x000e7ffffc000000

def z745 : W := mkw 0x658c73228985fdfb 0x3ae801ff9b250bfb 0x000000000001ffff 0xfff001fffc0003ff

def z746 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0xffffffffffffff0f 0xfc0fffffffffff9c

def z747 : W := mkw 0x1403080804401000 0x820be6daf4000000 0x0000000000000000 0x0001f7fffc000000

def z748 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x000000000001e0ff 0x03fffffffc000273

def z749 : W := mkw 0x1022080000200000 0x0002c00a004a0000 0xffffff0000000000 0x000fc03e03fe0000

def z750 : W := mkw 0x1c02081040401000 0x820edadaf4000000 0x0000000000000000 0x000fcbfffc000000

def z751 : W := mkw 0xde738cdd76791204 0xe30ffedaf5daf484 0xfffffffffffe1f00 0xfc0ffffffffffd8c

def z752 : W := mkw 0xcc5910d9d5199226 0xe38d3cf0f1b0f0a5 0xfffff0007f801ff0 0xffff8c7831f831ef

def z753 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000ffe462ffffc00

def z754 : W := mkw 0x1402080000001000 0x820ac0daf4000000 0x0000000000000000 0x000f81fffc000000

def z755 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0xffffff000001ff00 0x000fc1f803fe0380

def z756 : W := mkw 0xd14348ab14512a8c 0x6a23e71b97816294 0xffc000fff801ff0f 0xfc01c63e1fc1e39c

def z757 : W := mkw 0xcd4040b350113a8c 0xe82c19cb67816294 0xffc000fff801ff0f 0xfc0e39c7efc1e39c

def z758 : W := mkw 0x30ae2a000024c440 0x10c2c02e006e0160 0x1fffff00000000f0 0x000fc03e03fe0060

def z759 : W := mkw 0x9c03089844501000 0xc20ffedaf4806000 0x1fc0001f80000000 0x000fffffffc1c000

def z760 : W := mkw 0x010840220000a888 0x08a0012102210230 0x003ff0ff8781e0ff 0x03f1b5b9d239d273

def z761 : W := mkw 0x8e1184dc66581000 0xc30d3edaf490f400 0x000000fffffe0000 0x00003ffffc01fc00

def z762 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fb5fffc000000

def z763 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffffffffffff0f 0xfc0ffe0003ffff9c

def z764 : W := mkw 0xe1ec63a318b5efdd 0x78e001250bef6bfe 0xffffffffffffffff 0xfff0000003ffffff

def z765 : W := mkw 0x9a328cd462780000 0x4106da0000daf400 0xfffffffffffe0000 0x000e000003fffc00

def z766 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe07801ffff 0xfc0fc1fe03fe23fc

def z767 : W := mkw 0x9b2adcb6e370a8aa 0x4aa6db3192eb6631 0xffc00f00787fe0ff 0x03fe4bb9d1c62e73

def z768 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0x1ffff0ff87800000 0x000ffffffff9d000

def z769 : W := mkw 0xcd4040b350113a8c 0xe82c19cb63816294 0xffc000fff801ff0f 0xfc0e39ffe3c1e39c

def z770 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0xffffffe07ffe0000 0x000fcfb803fe3c00

def z771 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e39c7ffc1e39c

def z772 : W := mkw 0x0c00001040401000 0x820c1adaf4000000 0x0000000000000000 0x00000bfffc000000

def z773 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000ff7ffdc000000

def z774 : W := mkw 0x881110f8c5182022 0x4b253c119091f011 0x000000ffff80000f 0x03f03c01d001f013

def z775 : W := mkw 0x1c23081844601000 0x820ffedaf44a0000 0x1fc3f00000000000 0x000ffffffff80000

def z776 : W := mkw 0xcdc862b35011becc 0xe8ac19eb63a162b4 0xffc000fff801ff0f 0xfc0e39f9e3c1e39c

def z777 : W := mkw 0x75ae6a020065dcc8 0x30cac3ee076e03e0 0xffffff000001fff0 0x000fc3fe0ffe03e0

def z778 : W := mkw 0x8a1194fce7582022 0xcb253e11f491f411 0x000000fffffe000f 0x03f03e01fc01fc13

def z779 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffc3ff1ff87e0000 0x000ffe0003ffec00

def z780 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000f81fe03fe03e0

def z781 : W := mkw 0xe15c51e3999debbf 0x79e001250bb5fbff 0xffffffffffffffff 0xfff0000003ffffff

def z782 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0x1ffffffffffe0000 0x000ffe0003fffc00

def z783 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff0007fffff0 0x03ffc1fe03fe1fe3

def z784 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0x1fffff1f87fe0000 0x000fffffffffdc00

def z785 : W := mkw 0x1d1a5872c148b8aa 0x89aedbeb66319231 0x003ff0ff8781e0ff 0x03fe4a462e39d273

def z786 : W := mkw 0x0400000000001000 0x820800daf4000000 0x0000000000000000 0x000001ffec000000

def z787 : W := mkw 0x92328cc422380000 0x4102c00000daf400 0xfffffffffffe0000 0x000f800003fffc00

def z788 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0x1fffff1f87fe0000 0x000ffe0003ffdc00

def z789 : W := mkw 0x1022080000200000 0x0002c000004a0000 0xffffff0000000000 0x000fc1b803fe0000

def z790 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03fffe07fffffff 0xfff1ce463e3e3fff

def z791 : W := mkw 0x884000b150102204 0xc824180160816014 0xffc000fff801ff0f 0xfc0e3841e3c1e39c

def z792 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0xffffff000001e0f0 0x000fc1b803fe0260

def z793 : W := mkw 0x1422080000201000 0x000ac0ca004a0000 0x1fc3f00000000000 0x000f81b803f80000

def z794 : W := mkw 0x0001000804000000 0x0201241a94000000 0x0000000000000000 0x0001b5bfdc000000

def z795 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0xffc3ff0000000000 0x000fc1b803fe0000

def z796 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001ffff 0x03ffc1fe13fe03f3

def z797 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe0787fffff 0xfc0fcbfe2ffe2ffc

def z798 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff007ffffff0 0xffffcffe3ffe3fef

def z799 : W := mkw 0x552a480200219888 0x208ac1e0036a02a0 0xffffff000001fff0 0x000fc1f803fe03e0

def z800 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe07801ffff 0xffffc9fe3ffe23ff

def z801 : W := mkw 0x75ae6a220025fcc8 0x38eac1ef036f03f0 0xfffffffff801ffff 0xfc0ff9ffe3ffe3fc

def z802 : W := mkw 0x1403080804401000 0x020be6da94000000 0x0000000000000000 0x000ff7ffdc000000

def z803 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000fc1fe3ffe03e0

def z804 : W := mkw 0x4500402200013888 0x282801c103010290 0xffc000fff801ff0f 0xfc0e39c1e3c1e39c

def z805 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xfffc00ffff81ff0f 0xfc0e3dc1e3c1f39c

def z806 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0xe03fffff8781e0ff 0x03f1f5b9d23fd273

def z807 : W := mkw 0x0c01001844401000 0x820d3edaf4000000 0x0000000000000000 0x00007ffffc000000

def z808 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000fff81c3fffc00

def z809 : W := mkw 0x658c62020005dcc8 0x30c801ee032403e0 0xfffff0000001fff0 0x000f81fe03f803e0

def z810 : W := mkw 0x16338c4c26681000 0x830be6daf45a9400 0x003fff0007fe0000 0x0001c7fffc3e1c00

def z811 : W := mkw 0x8a3084d462380000 0x4104180000daf400 0xfffffffffffe0000 0x000e080003fffc00

def z812 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e39c1e1c1e39c

def z813 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0x003ffffffffe0000 0x000ffffffc3ffc00

def z814 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff0000001f00 0x000fc1fe03fe0180

def z815 : W := mkw 0x8a1195fcefd82133 0x4b253e119891fc1b 0x000000fffffe000f 0xfff03e01fc01fc1f

def z816 : W := mkw 0x0400000000001000 0x820800daf4000000 0x0000000000000000 0x000181fffc000000

def z817 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffffffffffff00 0x000ffe4003ffff80

def z818 : W := mkw 0x0400000000001000 0x820800daf4000000 0x0000000000000000 0x000031fffc000000

def z819 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ffff 0xfffe39c1f3c1e3ff

def z820 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1ffff000000000f0 0x000f81b803f80060

def z821 : W := mkw 0x9c03089844501000 0xc20ffedaf4806000 0xffc000fff801ff0f 0xfc0fffffffc1e39c

def z822 : W := mkw 0x9a738cdd76780204 0xc107fe0060daf404 0xfffffffffffe0000 0xfc0ffe0023fffc0c

def z823 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1ffff0e00781e0ff 0x03ff85b813f81273

def z824 : W := mkw 0xde638c9d76711204 0xe20ffedaf5ca6484 0xffc00f00787e1f00 0xfc0ffffffdc62d8c

def z825 : W := mkw 0x1402080000401000 0x820ac2daf4000000 0x0000000000000000 0x000043fffc000000

def z826 : W := mkw 0x312e490208a4c999 0x10c2c1240a6e0b6a 0xffffffe07fffffff 0xffffcffe3ffe3fff

def z827 : W := mkw 0x8a1194fce7582022 0x4b253e119091f411 0x000000fffffe0000 0x00003e01c001fc00

def z828 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0x1fffff000001e0f0 0x000fc1be03fe0260

def z829 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xfffc0fffffffff0f 0xfc0e7fc7ffc7ff9c

def z830 : W := mkw 0x9c1308d844581000 0xc30ffedaf490f000 0xfffff0ffff800000 0x000ffffffff9f000

def z831 : W := mkw 0x112a480200208888 0x0082c120026a0220 0x1fc3f00000000000 0x000f81b803f80000

def z832 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000fc5fe13fe03e0

def z833 : W := mkw 0x9a228c9462700000 0x4006da0000ca6400 0xfffffffff87e0000 0x000ffa0003ffec00

def z834 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0fb9f9e3c1e39c

def z835 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f1bfb9fe39d273

def z836 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0x1fc3ff0000000000 0x000fc1be03fe0000

def z837 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000f81f803fe03e0

def z838 : W := mkw 0x0411004804081000 0x830924daf4109000 0x003ff0ff87800000 0x0001b5fffe39d000

def z839 : W := mkw 0xcc4000b150113204 0xe82c18c161816094 0xffc000fff801ff0f 0xfc0e3841e1c1e39c

def z840 : W := mkw 0x5522480200211888 0x200ac1ca034a0280 0xffffff000001ff00 0x000fc1fe03fe0380

def z841 : W := mkw 0x1c02081040401000 0x820edadaf4000000 0x0000000000000000 0x000e01fffc000000

def z842 : W := mkw 0x4159506b9509aaae 0x2ba12531933192b5 0x003ff0ff8781ffff 0xfff1b5b9d239d3ff

def z843 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000ffbfffc000000

def z844 : W := mkw 0x55ea6a231021becc 0xa8aac1eb636b02b4 0x1fc3f00000000000 0x000f81b9c3f80000

def z845 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc0001ff8001f00 0xfc0e3181c3c1e18c

def z846 : W := mkw 0x1c02081040401000 0x820edadaf4000000 0x0000000000000000 0x000e7bfffc000000

def z847 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000fce0003fffc00

def z848 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f1b5b9c239d273

def z849 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffc3ff00787e1f00 0xfc0fcbfe2ffe2d8c

def z850 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff00000000f0 0x000fc1be03fe0060

def z851 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0xffc3f0fff8000000 0x000ffffffff9e000

def z852 : W := mkw 0x010850228100a8aa 0x0aa0013192210231 0x003ff0ff8001e0ff 0x03f1b1b9d239c273

def z853 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000fb40003fffc00

def z854 : W := mkw 0x4540402310013a8c 0xa82801c163010294 0xffc000ff8001ff0f 0xfc0e31c1e3c1c39c

def z855 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e3981c3c1e39c

def z856 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e79c7e3c1e39c

def z857 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07fffffff 0xfff1cffe3c063fff

def z858 : W := mkw 0x4119506a8509a8aa 0x2ba12531933192b1 0xfffff0ff8781ffff 0x03f1b5b9d3f9d3f3

def z859 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0x1fc3f0000001fff0 0x000f81b803f803e0

def z860 : W := mkw 0x0001000804000000 0x0201241090000000 0x0000000000000000 0x0001b5fffc000000

def z861 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe00f0 0x03fffe0013fffc63

def z862 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000ff1ffc3fe03e0

def z863 : W := mkw 0x75ee6b2318a5ffdd 0xb8eac1ef6b6f0bfe 0xffffffe07fffffff 0xffffcffffffe3fff

def z864 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0xffffff007ffe0000 0x000ffffffdfe3c00

def z865 : W := mkw 0x0119506a8548a8aa 0x0ba1273196319231 0x003ff0ff8781e0ff 0x03f1b7b9de39d273

def z866 : W := mkw 0x30ae2b0008a4c551 0x10c2c02e086e096a 0xffffffe07fffffff 0xffffce7e3ffe3fff

def z867 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e3841e3c1e39c

def z868 : W := mkw 0x9a338cdc66780000 0x4107fe0a04daf400 0xfffffffffffe0000 0x000ffe060ffffc00

def z869 : W := mkw 0xba378ddc6efc4111 0x5147fe0408defd4a 0x1fc3f01f8001ffff 0xffffb0463ff9c3ff

def z870 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffffffffffffff 0xfffffe4033ffffff

def z871 : W := mkw 0x1403080804401000 0x820be6daf4000000 0x0000000000000000 0x0001c7bfdc000000

def z872 : W := mkw 0x1402080000001000 0x820ac0daf4000000 0x0000000000000000 0x000fcffffc000000

def z873 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000ffe003ffffc00

def z874 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe00781ffff 0x03ffc1fe03fe13f3

def z875 : W := mkw 0x3426080000245000 0x104ac0ce004e0140 0xffffff000001fff0 0x000fc1fe03fe03e0

def z876 : W := mkw 0x152a480200209888 0x008ac1ea026a0220 0xffffff000001e0f0 0x000fc1fe03fe0260

def z877 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff878000f0 0x03f1b5b9d239d063

def z878 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0xe03fffffffffe0ff 0x03f1fffffe3ffe73

def z879 : W := mkw 0xdc43089954511204 0xe20ffedaf5806084 0xffc000fff8001f00 0xfc0fffffffc1e18c

def z880 : W := mkw 0x3c0709184cc45111 0x924ffedefc04094a 0xe03c0fe07fffffff 0xffffb1b9c0063fff

def z881 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f1b5fffe39d273

def z882 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc0001f8001ff0f 0xfc0e31c1e3c1c39c

def z883 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff000001ffff 0xffffc1fe03fe03ff

def z884 : W := mkw 0x1c33085844681000 0x830ffedaf45a9000 0xffffffff87800000 0x000fffffffffd000

def z885 : W := mkw 0x881100d844180000 0x41053c000090f000 0xfffffffffffe0000 0x000ffe0003fffc00

def z886 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fffbfdc000000

def z887 : W := mkw 0x4511506a850938aa 0x2b2925d193119291 0xffc000ff8781ff0f 0x03fe35c1d3c1d393

def z888 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ffffffe0ff 0x03f1bfb9d239fe73

def z889 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff000001fff0 0xfc0fc1fe2ffe03ec

def z890 : W := mkw 0x1c23081844601000 0x820ffedaf44a0000 0x003fff0000000000 0x000ffffffc3e0000

def z891 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffc3ff000001fff0 0x000fc1fe03fe03e0

def z892 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0x1fffff1f87fe0000 0x000fb00003ffdc00

def z893 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe000f 0xfc0ffe0023fffc1c

def z894 : W := mkw 0x011850628108a8aa 0x09a0012102319231 0x003ff0ff8781e0ff 0x03f1b1b9c239d273

def z895 : W := mkw 0xcd4840b35011ba8c 0xe8ac19e163a162b4 0xfffff0ffff81ffff 0xffffbdf9f3f9f3ff

def z896 : W := mkw 0xcd4850b3d111baae 0xe8ac19e163a162b5 0xffc000fff801ffff 0xfffe39c1e3c1e3ff

def z897 : W := mkw 0x0400000000001000 0x820800daf4000000 0x000000000001e0ff 0x03f001fffc000273

def z898 : W := mkw 0x9a338cdc66780000 0x4307fe1090daf400 0xfffffffffffe0000 0x000ffe3813fffc00

def z899 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe00781ffff 0xffffc5fe3ffe13ff

def z900 : W := mkw 0x8a5194fdf7582226 0xcb253e11f091f415 0x000000fffffe000f 0xfff03e01f001fc1f

def z901 : W := mkw 0x74ae2a000025d440 0x30cac0ee016e01e0 0xffffff0000001ff0 0x000fc07e03fe01e0

def z902 : W := mkw 0xcd4840b35011ba8c 0xe8ac19e163a162b4 0xfffff0fff801ffff 0xfc0e39c1e3f9e3fc

def z903 : W := mkw 0x75ae7a228125fcea 0x38eac1ef036f03f1 0xffffff000001ffff 0x03ffc1fe03fe03f3

def z904 : W := mkw 0x0019104885088022 0x0381243090309021 0x003ff0ff878000f0 0x03f1b5b9d239d063

def z905 : W := mkw 0x0400000000001000 0x820800daf4000000 0xe03c0fe07ffe0000 0x00004ffffc063c00

def z906 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc0001ff801ff0f 0xfc0e39c1e3c1e39c

def z907 : W := mkw 0x9a328cd462780000 0x4106da0000daf400 0xfffffffffffe0000 0x000e4e0003fffc00

def z908 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe07801fff0 0x000fc9fe03fe23e0

def z909 : W := mkw 0x1033084804280000 0x0103e400005a9000 0xfffffffffffe0000 0x000ffe0003fffc00

def z910 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fbffffc000000

def z911 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe00781fff0 0x000fc5fe03fe13e0

def z912 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0x1fc3f0000001ffff 0xffff81fe3ff803ff

def z913 : W := mkw 0x61bc736289adedfb 0x39e001250b7f9bfb 0xffffffffffffffff 0xfff0000003ffffff

def z914 : W := mkw 0x0401000804001000 0x820924daf4000000 0x0000000000000000 0x0001b1fffc000000

def z915 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000ffffffff0f 0xfc0e3fc1e3c1ff9c

def z916 : W := mkw 0x885110f9d5182226 0xcb253c11f091f015 0xe03c00ffff81ffff 0xfff03c41f001f3ff

def z917 : W := mkw 0x8c00009040101000 0xc20c18daf4806000 0xffc000fff8000000 0x000e39ffffc1e000

def z918 : W := mkw 0x9c43089954501204 0xc20ffedaf4806004 0x0000000078000000 0xfc0ffffffc00200c

def z919 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1fc3f0000001e000 0x000f81b803f80200

def z920 : W := mkw 0x74ae2a000025d440 0x30cac0ee016e01e0 0x1fffff00000000f0 0x000fc03e01fe0060

def z921 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe07fffffff 0xffffc9fe23fe3fff

def z922 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0x1fffffff87fe0000 0x000ff60003ffdc00

def z923 : W := mkw 0x75ae6b2208a5fdd9 0x38eac1ef0b6f0bfa 0xffffffffffffffff 0xffffffffffffffff

def z924 : W := mkw 0x9e238c9c66701000 0xc20ffedaf4ca6400 0xfffc0fe07ffe0000 0x000ffffffdc63c00

def z925 : W := mkw 0x211d516a8d8ce9bb 0x1be125359a359b7b 0xe003ff1ff87e1f00 0xfc01fbffee3fed8c

def z926 : W := mkw 0x1e138c5c66481000 0x830ffedaf4109400 0x0000000007fe0000 0x000ffffffc001c00

def z927 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f1b5b9d039d273

def z928 : W := mkw 0x1c02081040001000 0x800ed8ca60000000 0x0000000000000000 0x000ffffffc000000

def z929 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffffffffffe0ff 0x03fffe463ffffe73

def z930 : W := mkw 0x9a338cdc66780000 0xc307fe10f4daf400 0xfffffffffffe0000 0x000ffe47fffffc00

def z931 : W := mkw 0xbb3fddfeeffce9bb 0x59e7ff250affff7b 0xffffffffffffffff 0xfffffe0003ffffff

def z932 : W := mkw 0x9e138cdc66581000 0xc30ffedaf490f400 0x003ff0fffffe0000 0x000ffffffe39fc00

def z933 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff01f8781e0ff 0x03f1b5b9d239d273

def z934 : W := mkw 0x74b73a68852d7462 0x3b6be4df915f91d1 0xffc00fff87801f0f 0x03fe7447d1c7d193

def z935 : W := mkw 0x9a328cd462780000 0x4106da0000daf400 0xffc3ff1ff87e0000 0x000e4a0003ffec00

def z936 : W := mkw 0x5ca32a1844611440 0xa20ffedaf54a0080 0x1fc0000000000000 0x000ffffffdc00000

def z937 : W := mkw 0x1403080804001000 0x020be4da90000000 0x0000000000000000 0x000ffffffc000000

def z938 : W := mkw 0x0400000000001000 0x820800daf4000000 0x0000000000000000 0x000041fffc000000

def z939 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0xffc3f00000000000 0x000f81b803f80000

def z940 : W := mkw 0x77aeee062265dcc8 0x30cac3ee036e07e0 0xffffff00007ffff0 0x000fc3fe03fe0fe0

def z941 : W := mkw 0x9e138cdc66581000 0xc30ffedaf490f400 0xe03c0ffffffe0000 0x000ffffffc07fc00

def z942 : W := mkw 0x8a3184dc66780000 0x41053e0000daf400 0xfffffffffffe0000 0x000e3e0003fffc00

def z943 : W := mkw 0xef9de6de665ddcc8 0x71cd3fee03b4f7e0 0x000000fffffffff0 0x00003ffe0001ffe0

def z944 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xfffc0ffff801ff0f 0xfc0e79c1e3c7e39c

def z945 : W := mkw 0xcc4000b150113204 0xe82c18c161816094 0xffc0001ff8001f00 0xfc0e3841e1c1e18c

def z946 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000ffe4023fffc00

def z947 : W := mkw 0x0400000000001000 0x820800daf4000000 0x0000000000000000 0x000001bfdc000000

def z948 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0xffc3f0000001ff00 0x000fc1fe03f80380

def z949 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0x1fffff0007fe00f0 0x03ffc7be1ffe1c63

def z950 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0x1fffff00000000f0 0x000fc1fe03fe0060

def z951 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000ffa0003fffc00

def z952 : W := mkw 0x9e238c9c66701000 0xc20ffedaf4ca6400 0x1fc0000000000000 0x000ffffffdc00000

def z953 : W := mkw 0x112a480200208888 0x0082c120026a0220 0xffffff0000000000 0x000fc1b803fe0000

def z954 : W := mkw 0x34ae2a000024d440 0x10cac0ee006e0160 0xffffff00000000f0 0x000fc1fe03fe0060

def z955 : W := mkw 0x1c23081844601000 0x820ffedaf44a0000 0xffc00f0000000000 0x000ffffffdc60000

def z956 : W := mkw 0x0011004804080000 0x0301241090109000 0x003ff0ff8781e0ff 0x03f1b5b9d239d273

def z957 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e3fc1ffc1e39c

def z958 : W := mkw 0x9a338cdc66780000 0xc307fe10f4daf400 0xfffffffffffe0000 0x000ffe01c3fffc00

def z959 : W := mkw 0x75ee6a231025fecc 0x38eac1ef036f03f4 0xffffff000001ffff 0xfc0fc1fe03fe03fc

def z960 : W := mkw 0x75ae6a220025fcc8 0x38eac1ef036f03f0 0xffffffff8001ffff 0x000fc1fe03ffc3f0

def z961 : W := mkw 0x0000000000000000 0x0200001090000000 0x0000000000000000 0x00004ffffc000000

def z962 : W := mkw 0x1422080000201000 0x000ac0ca004a0000 0xffffffe07ffe0000 0x000fcffe3ffe3c00

def z963 : W := mkw 0x0c01001844401000 0x820d3edaf4000000 0x0000000000000000 0x000031fffc000000

def z964 : W := mkw 0x112a480200208888 0x0082c120026a0220 0xffffffe07fffe0ff 0x03ffcfb813fe3e73

def z965 : W := mkw 0x550a480200019888 0x208ac1ea032002a0 0xfffff0000001fff0 0x000fc1fe03f803e0

def z966 : W := mkw 0x75ee6a031025decc 0xb0cac1ee636e03e4 0xffffff000001fff0 0xfc0fc1fe23fe03ec

def z967 : W := mkw 0x885110f9d5182226 0xcb253c11f091f015 0x0000001f80000000 0x00003001c001c000

def z968 : W := mkw 0xa33cd5e6abbce9bb 0x59e001250affff7b 0xffffffffffffffff 0xfff0000003ffffff

def z969 : W := mkw 0x9c03089844501000 0xc20ffedaf4806000 0x000000fff8000000 0x000ffffffc01e000

def z970 : W := mkw 0x9e138cdc66581000 0xc30ffedaf490f400 0x0000001f80000000 0x000ffffffc01c000

def z971 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe07fffffff 0xffffc7fe1ffe3fff

def z972 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffc3ff1ff87e0000 0x000fb00003ffec00

def z973 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xfffc0fffffffffff 0xfffe7fc1f3c7ffff

def z974 : W := mkw 0x885110f9d5182226 0xcb253c11f091f015 0x000000ff8780000f 0x03f03401d001d013

def z975 : W := mkw 0x74ae2b0008a5d551 0x30cac0ee096e09ea 0xffffff007ffe1ff0 0xffffce7e3dfe3def

def z976 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000fc1fe01fe03e0

def z977 : W := mkw 0x1c13085844481000 0x830ffedaf4109000 0xe03ffffffffe0000 0x000ffffffe3ffc00

def z978 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1fc3f00000000000 0x000f81fe03f80000

def z979 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000fc1be03fe03e0

def z980 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f1bdf9f239d273

def z981 : W := mkw 0x32378d4c2eec4111 0x1343e61e9c5e9d4a 0x003fff0007fe00f0 0x03f1c63e1c3e1c63

def z982 : W := mkw 0xcd4840b35011ba8c 0xe8ac19e163a162b4 0xffc000fff801ffff 0xfc0e39f9e3c1e3fc

def z983 : W := mkw 0x55aa6a220021bcc8 0x28aac1eb036b02b0 0x1fc3f01f80000000 0x000fb1b9c3f9c000

def z984 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1fffff0000000000 0x000fc1b803fe0000

def z985 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff8001f00 0xfc0e39c1e3c1e18c

def z986 : W := mkw 0x55aa6b0208a19dd9 0x208ac1ea0b6a0aaa 0x1fc3f0e07ffe000f 0xffff8fb83ff83c1f

def z987 : W := mkw 0x211c5162898ce9bb 0x19e001250a359b7b 0x003fffff87ffe0ff 0x03f00000023fde73

def z988 : W := mkw 0x5c43081954411204 0xa20ffedaf5000084 0x0000000000001f00 0xfc0ffffffc00018c

def z989 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0xe00000000001ff00 0x000ffffffc000380

def z990 : W := mkw 0x0400000000001000 0x820800daf4000000 0x0000000000000000 0x000005fffc000000

def z991 : W := mkw 0x0401000804001000 0x820924daf4000000 0x0000000000000000 0x0001fffffc000000

def z992 : W := mkw 0x12338c4c26680000 0x0103e600005a9400 0xffffffff87fe0000 0x000ff60003ffdc00

def z993 : W := mkw 0x54aa2a0000219440 0x208ac0ea016a00a0 0x1fc3f00000000000 0x000f803801f80000

def z994 : W := mkw 0x9a328cd462780000 0x4106da0000daf400 0xfffffffffffe0000 0x000e7a0003fffc00

def z995 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0xffc00ffffffe0000 0x000ffffffdc7fc00

def z996 : W := mkw 0x1c02081040401000 0x800edaca64000000 0x0000000000000000 0x000ffbffec000000

def z997 : W := mkw 0x9a338cdc66780000 0x4307fe1a94daf400 0xfffffffffffe0000 0x000ffe7e3ffffc00

def z998 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffffffffffe00f 0x000ffe0003fffe10

def z999 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x000000ff80000000 0x000ffffffe01c000

def z1000 : W := mkw 0x8a1184dc66580000 0xc3053e10f490f400 0x0000001f80000000 0x00003e01fc01c000

def z1001 : W := mkw 0x55ea6a231021becc 0xa8aac1eb636b02b4 0x1fc3f0000001ff0f 0xfc0f81f9e3f8039c

def z1002 : W := mkw 0x0c01001844001000 0x820d3cdaf4000000 0x0000000000000000 0x000fbdfffc000000

def z1003 : W := mkw 0x863084c422381000 0xc30800daf4daf400 0xfffffffffffe0000 0x000001fffffffc00

def z1004 : W := mkw 0xcf40c4b772513a8c 0xe82c1bc163816694 0xffc000fff87fff0f 0xfc0e3bc1e3c1ef9c

def z1005 : W := mkw 0x9c03089844501000 0xc20ffedaf4806000 0xffc0000078000000 0x000ffffffdc02000

def z1006 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001ffff 0xfc0fc1fe23fe03fc

def z1007 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0xfffffffffffe0000 0x000fffffeffffc00

def z1008 : W := mkw 0x0801001844400000 0x82053e10f4000000 0x0000000000000000 0x0001fffffc000000

def z1009 : W := mkw 0xcc40009150111204 0xe20c18daf5806084 0xffc0000078001f00 0xfc0e09fffdc0218c

def z1010 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffc3fffffffe0000 0x000ffe0003fffc00

def z1011 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xfffc00fff801ffff 0xfc0e39c1e3c1e3fc

def z1012 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe07ffffff0 0x03ffcffe1ffe3fe3

def z1013 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fcffffc000000

def z1014 : W := mkw 0x1c02081040401000 0x820edadaf4000000 0x0000000000000000 0x000e4ffffc000000

def z1015 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000e7ffffc000000

def z1016 : W := mkw 0x650c40020005d888 0x30c801e4032403e0 0xffffff000001fff0 0x000fc1fe03fe03e0

def z1017 : W := mkw 0x74ae2b0008a5d551 0x30cac0ee096e09ea 0xffffffe07fffffff 0xffffce7e3dfe3fff

def z1018 : W := mkw 0x92328cc422380000 0x4102c00000daf400 0xfffffffffffe0000 0x000fce0003fffc00

def z1019 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0xe03c0f0000000000 0x000ffffffc060000

def z1020 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffc3f0000001fff0 0x000f81fe03f803e0

def z1021 : W := mkw 0xcd4840b35011ba8c 0xe8ac19e163a162b4 0xffc3f0fff801ff0f 0xfc0fb9f9e3f9e39c

def z1022 : W := mkw 0x9a338cdc66780000 0x4107fe0a00daf400 0xfffffffffffe0000 0x000ffe3e03fffc00

def z1023 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ffff81e0ff 0xfff1bdb9f239f27f

def z1024 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1fc3f00000000000 0x000f81f803f80000

def z1025 : W := mkw 0x55aa6a220021bcc8 0x28aac1eb036b02b0 0x1fc3f0ff8001e00f 0x000fb1b9c3f9c210

def z1026 : W := mkw 0x8a1184dc66580000 0xc3053e10f490f400 0xe03c0ffffffe0000 0x00007e47fc07fc00

def z1027 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000fc1b803fe03e0

def z1028 : W := mkw 0x30bf3b488dacc573 0x13c3e43e987e996b 0x003fff0007fe00f0 0x03f1c63e1c3e1c63

def z1029 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0x1fc3ff1f807e0000 0x000ff20003ffcc00

def z1030 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc00ffff87fff0f 0xfc0e7bc1e3c7ef9c

def z1031 : W := mkw 0x9822089040300000 0x4006d80000ca6000 0xfffffffffffe0000 0x000ffe0003fffc00

def z1032 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0xe000000078001f00 0xfc0ffffffc00218c

def z1033 : W := mkw 0x1c13085844481000 0x830ffedaf4109000 0x0003f01f80000000 0x000ffffffe39c000

def z1034 : W := mkw 0x71ae6a020025ccc8 0x30c2c124036e03e0 0xffffff000001fff0 0x000fc1b803fe03e0

def z1035 : W := mkw 0x2004010008844111 0x104000040804094a 0xe0000fe07fffffff 0xfff04e463c063fff

def z1036 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0xffc3ff1ff87e0000 0x000ffbffefffec00

def z1037 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0xe0000f00787e0000 0x000ffffffc062c00

def z1038 : W := mkw 0x112a480200208888 0x0082c120026a0220 0x1ffff0000001e0f0 0x000f81b803f80260

def z1039 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0x1fffff1f87fe0000 0x000ff7bfdfffdc00

def z1040 : W := mkw 0x8a1194dce7580022 0x43053e109090f401 0x000000fffffe0000 0x03f03e001001fc03

def z1041 : W := mkw 0x0400000000001000 0x820800daf4000000 0x0000000000000000 0x000009fffc000000

def z1042 : W := mkw 0x9c23089844701000 0xc20ffedaf4ca6000 0xfffffffff8000000 0x000fffffffffe000

def z1043 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0xffffff1f80000000 0x000fffffffffc000

def z1044 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f1b1b9d239d273

def z1045 : W := mkw 0x10aa2a0000208440 0x0082c02a006a0020 0x1fc3f00000000000 0x000f803803f80000

def z1046 : W := mkw 0x001910688508a022 0x0ba1243190319031 0x003ff0ff878000ff 0x03f1b5b9d039d073

def z1047 : W := mkw 0xdc43089954511204 0xe20ffedaf5806084 0x1fc0000000000000 0x000ffffffdc00000

def z1048 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xfffc00ffff81ffff 0xfffe39c1e3c1f3ff

def z1049 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000fc9fe23fe03e0

def z1050 : W := mkw 0x4440000110011204 0xa20800daf5000084 0x0000000000001f00 0xfc0001fffc00018c

def z1051 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0xffc3f0000001ff00 0x000f81b803f80380

def z1052 : W := mkw 0x1403080804001000 0x820be4daf4000000 0x0000000000000000 0x000ff5fffc000000

def z1053 : W := mkw 0xed4441b358957b9d 0xf86c19c56b856bde 0x1ffc0f1f87fe00f0 0x03fe7787dfc7dc63

def z1054 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0x1fc0001f8001ff0f 0xfc0e39c1e3c1c39c

def z1055 : W := mkw 0x75ae6a020025dcc8 0xb0cac1ee676e03e0 0xffffff000001fff0 0x000fc1fe2ffe03e0

def z1056 : W := mkw 0x8a1185dc6ed80111 0xc3053e10fc90fc0a 0x000000fffffe000f 0xfff03e01fc01fc1f

def z1057 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e31c1e3c1e39c

def z1058 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0x1fffff000001fff0 0x000fc1fe03fe03e0

def z1059 : W := mkw 0x8a1194fce7582022 0x4b253e119091f411 0xe03c0fffffffe0ff 0x03f07e01d007fe73

def z1060 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0x1fc3f0fffffe0000 0x000ffffffff9fc00

def z1061 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000ffe061ffffc00

def z1062 : W := mkw 0x8a1184dc66580000 0xc3053e10f490f400 0x000000fffffe0000 0x00003e01c001fc00

def z1063 : W := mkw 0x0401000804001000 0x820924daf4000000 0x0000000000000000 0x000185fffc000000

def z1064 : W := mkw 0xc54040a310113a8c 0x682801c103816294 0xffc000fff801ff0f 0xfc0e31c1c3c1e39c

def z1065 : W := mkw 0x75ee6a231025fecc 0xb8eac1ef636f03f4 0xffffffff8001ffff 0xfc0ff1ffe3ffc3fc

def z1066 : W := mkw 0x0401000804001000 0x820924daf4000000 0x0000000000000000 0x000035fffc000000

def z1067 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff01f8001e0ff 0x03f1b1b9d239c273

def z1068 : W := mkw 0x0c00001040001000 0x820c18daf4000000 0x0000000000000000 0x000e09fffc000000

def z1069 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffffffffffff0f 0xfc0ffe463fffff9c

def z1070 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0xe03fffffffffe0ff 0x03f1b5b9d23ffe73

def z1071 : W := mkw 0x1403080804401000 0x820be6daf4000000 0x0000000000000000 0x000181fffc000000

def z1072 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0xffffffffffffe0ff 0x03fffffffffffe73

def z1073 : W := mkw 0xcc40009150111204 0xe00c18c061806084 0xffc000fff8001f00 0xfc0e39c1e3c1e18c

def z1074 : W := mkw 0x1c13085844481000 0x830ffedaf4109000 0x000000ff87800000 0x000ffffffc01d000

def z1075 : W := mkw 0x5c03081844411000 0xa20ffedaf5000080 0xffc0000000001f00 0x000ffffffdc00180

def z1076 : W := mkw 0x1422080000201000 0x820ac0daf44a0000 0xffffff0000000000 0x000fc1fffffe0000

def z1077 : W := mkw 0x9a338cdc66780000 0xc107fe0060daf400 0xfffffffffffe0000 0x000ffe01e3fffc00

def z1078 : W := mkw 0xb8ee2ab15034e644 0xd8e6d82f60ef6174 0x003ffffff80000ff 0xfc01f83fe03fe07c

def z1079 : W := mkw 0xaa1585dc6edc4111 0xd3453e14fc94fd4a 0xe03c0fffffffffff 0xfff07e47fc07ffff

def z1080 : W := mkw 0x1003080804400000 0x0203e61a94000000 0x0000000000000000 0x0001fffffc000000

def z1081 : W := mkw 0xc94040b350112a8c 0xe824190163816294 0xffc000fff801ff0f 0xfc0e3801e3c1e39c

def z1082 : W := mkw 0x8c00009040101000 0xc00c18c060806000 0xffc000fff801ff0f 0xfc0e39c1e3c1e39c

def z1083 : W := mkw 0x71ae6a020025ccc8 0x30c2c12e036e03e0 0xffffff000001fff0 0x000fc03e03fe03e0

def z1084 : W := mkw 0x4508400200019888 0x208801e0032002a0 0xffc3f0000001ff00 0x000f81f803f80380

def z1085 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fb9fffc000000

def z1086 : W := mkw 0x9e038c9c66501000 0xc20ffedaf4806400 0x00000000787e0000 0x000ffffffc002c00

def z1087 : W := mkw 0x9a338cdc66780000 0x4307fe1090daf400 0xfffffffffffe0000 0x000fffb9c3fffc00

def z1088 : W := mkw 0x9a339cdce7780022 0x4307fe1090daf401 0xfffffffffffe0000 0x03fffe0013fffc03

def z1089 : W := mkw 0x9a338cdc66780000 0x4307fe1090daf400 0xfffffffffffe0000 0x000ffffffffffc00

def z1090 : W := mkw 0x210c51228984e9bb 0x18e001250a250b7b 0xe03c0fe07fffffff 0xfff0000000063fff

def z1091 : W := mkw 0x1422080000201000 0x000ac0ca004a0000 0x1fc3f00000000000 0x000fc1fe03f80000

def z1092 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000fc7fe1ffe03e0

def z1093 : W := mkw 0x011850628108a8aa 0x09a0012102319231 0x003ff0ff8781e0ff 0x03f04e463e39d273

def z1094 : W := mkw 0x1e338c5c66681000 0x830ffedaf45a9400 0x003fffff87fe0000 0x000ffffffe3fdc00

def z1095 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0x1fc0001f8001ff0f 0xfc0e3181c3c1c39c

def z1096 : W := mkw 0xfce62b9158b55755 0xf04ed8ce69ce69ce 0xffc00f00787e1f00 0xfc0e4a462dc62d8c

def z1097 : W := mkw 0x0c01001844001000 0x820d3cd0f0000000 0x0000000000000000 0x000ffffffc000000

def z1098 : W := mkw 0xdc43089954511204 0xe20ffedaf5806084 0xffc000e07801ff0f 0xfc0ffffffdc0239c

def z1099 : W := mkw 0x102a080000208000 0x0082c020006a0020 0xffffff00000000f0 0x000fc03803fe0060

def z1100 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1ffff00000000000 0x000f81b803f80000

def z1101 : W := mkw 0x75ae6a020025dcc8 0xb0cac1ee636e03e0 0xffffff000001fff0 0x000fc1ffe3fe03e0

def z1102 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e7fc1e3c1e39c

def z1103 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fffffffffff 0xfff07e463e07ffff

def z1104 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff00787fffff 0xffffcbfe3ffe2fff

def z1105 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff0007ffffff 0xffffc7fe3ffe1fff

def z1106 : W := mkw 0x3426090008a45111 0x104ac0ce084e094a 0xffffffe07fffffff 0xffffcffe3ffe3fff

def z1107 : W := mkw 0x0401000804401000 0x820926daf4000000 0x0000000000000000 0x000007fffc000000

def z1108 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff00787ffff0 0x000fcbfe03fe2fe0

def z1109 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffffffffffe0f0 0x000ffe0003fffe60

def z1110 : W := mkw 0x9a338cdc66780000 0x4307fe1090daf400 0xfffffffffffe0000 0x000ffe01d3fffc00

def z1111 : W := mkw 0x1402080000001000 0x820ac0daf4000000 0x0000000000000000 0x000e41fffc000000

def z1112 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe07fffffff 0x03ffcffe13fe3ff3

def z1113 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000fffb803fffc00

def z1114 : W := mkw 0x0c01001844401000 0x820d3edaf4000000 0x0000000000000000 0x000e3ffffc000000

def z1115 : W := mkw 0x323f9d4cafecc133 0x13c3e634987e9d6b 0x003fff0007fe00f0 0x03f1c63e1c3e1c63

def z1116 : W := mkw 0x1422080000201000 0x000ac0ca004a0000 0xffffff0000000000 0x000fc1b803fe0000

def z1117 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0xe00000e078000000 0x000ffffffc002000

def z1118 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff01f8781e0f0 0x03f1b5b9d239d263

def z1119 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e3dc1f3c1e39c

def z1120 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe07ffffff0 0x000fcffe3ffe3fe0

def z1121 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000fbe0003fffc00

def z1122 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000ffe4603fffc00

def z1123 : W := mkw 0x0011004804080000 0x0301241090109000 0xe03ffffffffe0000 0x0001fffffe3ffc00

def z1124 : W := mkw 0xbe268d946af45111 0xd04edace6cce6d4a 0xffc00f00787e1f00 0xfc0e4a462dc62d8c

def z1125 : W := mkw 0x0001000804000000 0x0201241090000000 0x0000000000000000 0x0001f7bfdc000000

def z1126 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0x1fffff00000000f0 0x000f81b803fe0060

def z1127 : W := mkw 0x8a1194fce7582022 0x4b253e119091f411 0x0000001f80000000 0x00003001c001c000

def z1128 : W := mkw 0x74ae2a000025d440 0x30cac0ee016e01e0 0xffffff0000001ff0 0x000fc1fe01fe01e0

def z1129 : W := mkw 0xc94040b350112a8c 0x6824190103816294 0xffc000fff801ff0f 0xfc0e3981c3c1e39c

def z1130 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x003c0f0007fe0000 0x000ffffffc061c00

def z1131 : W := mkw 0x9a338cdc66780000 0xc307fe1af4daf400 0xfffffffffffe0000 0x000ffe3ffffffc00

def z1132 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe07fffffff 0xffff81b803fe3fff

def z1133 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff00787ffff0 0xfc0fcffe3ffe2fec

def z1134 : W := mkw 0x8a1194fce7582022 0x4b253e119091f411 0x000000ff8780000f 0x03f03401d001d013

def z1135 : W := mkw 0x0400000000001000 0x820800daf4000000 0x0000000000000000 0x00004bfffc000000

def z1136 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1fc3f0000001ff00 0x000f81f803f80380

def z1137 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffff1ffffe0000 0x000ffe0003fffc00

def z1138 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000e7e0003fffc00

def z1139 : W := mkw 0x1803081844400000 0x8207fe1af4000000 0x0000000000000000 0x0001ffbffc000000

def z1140 : W := mkw 0x65cc63231885ffdd 0xb8e801ef6b250bfe 0x000000000001ffff 0xfff001fffc0003ff

def z1141 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000ff7fffc000000

def z1142 : W := mkw 0x10aa2a0000208440 0x0082c02a006a0020 0xffffff0000000000 0x000fc03803fe0000

def z1143 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1fc3f00000000000 0x000fc1be03f80000

def z1144 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000fb80003fffc00

def z1145 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f1f7bfde39d273

def z1146 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff8001f0f 0xfc0e39c1e3c1e19c

def z1147 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0f007fffffff 0xfff04e463c063fff

def z1148 : W := mkw 0x885110f9d5182226 0xcb253c11f091f015 0x000000fff800000f 0xfc003801e001e01c

def z1149 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0xffc3f00000001f00 0x000f81f803f80180

def z1150 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0xe03ff0ffff81ffff 0xfff1fffffe39f3ff

def z1151 : W := mkw 0x1e238c1c66601000 0x820ffedaf44a0400 0x00000f00007e0000 0x000ffffffc060c00

def z1152 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0xe03fffffffffffff 0xfff1fff9f23fffff

def z1153 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x0003f01f8001e0ff 0x03f1b5b9d239c273

def z1154 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff0000001ff0 0x000fc1fe03fe01e0

def z1155 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1fc3f00000000000 0x000fcffe3ff80000

def z1156 : W := mkw 0x75ee6b2318a5ffdd 0xb8eac1ef6b6f0bfe 0xffffff000001ffff 0xffffc1fffffe03ff

def z1157 : W := mkw 0x210c51228984e9bb 0x18e001250a250b7b 0x000000000001ffff 0xfff00000000003ff

def z1158 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781ffff 0xfff1b5f9f239d3ff

def z1159 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0xe03ff0ffff81e0ff 0x03f1bdb9d239f273

def z1160 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffc3ff000001ff00 0x000fc1fe03fe0380

def z1161 : W := mkw 0x8a5184fd76582204 0xcb253e11f491f414 0x000000fffffe000f 0xfc003e01fc01fc1c

def z1162 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0xe03c0fe07fffff0f 0xfc0ffffffc063f9c

def z1163 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0xffffff0000000000 0x000fc1fe03fe0000

def z1164 : W := mkw 0x9e238c9c66701000 0xc20ffedaf4ca6400 0xffffff00787e0000 0x000ffffffffe2c00

def z1165 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1fc3f0000001e0f0 0x000f81b803f80260

def z1166 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe07fffffff 0xffffcbfe2ffe3fff

def z1167 : W := mkw 0x75ee6a231025fecc 0xb8eac1ef636f03f4 0xffffff000001fff0 0x000fc1ffc3fe03e0

def z1168 : W := mkw 0x9e138cdc66581000 0xc30ffedaf490f400 0xffc000fffffe0000 0x000fffffffc1fc00

def z1169 : W := mkw 0x1403080804401000 0x820be6daf4000000 0x0000000000000000 0x000fc7fffc000000

def z1170 : W := mkw 0x30ae2a000024c440 0x10c2c02e006e0160 0xffffff000001fff0 0x000fc07e03fe03e0

def z1171 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x003ff00000000000 0x000ffffffe380000

def z1172 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0x1ffff0000001fff0 0x000f81fe03f803e0

def z1173 : W := mkw 0x5773cc6f36693a8c 0xa92be7c1635b9694 0x003fff0007ffff0f 0xfc01c7c1e03e1f9c

def z1174 : W := mkw 0x1803081844400000 0x0207fe1a94000000 0x0000000000000000 0x000fffbfdc000000

def z1175 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0x1fc3f00000001f00 0x000f81fe03f80180

def z1176 : W := mkw 0x0400000000001000 0x820800daf4000000 0x0000000000000000 0x00000ffffc000000

def z1177 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0x1fc3f01f80000000 0x000fb1fffff9c000

def z1178 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe07fffffff 0xffffcffe03fe3fff

def z1179 : W := mkw 0x2004010008844111 0x104000040804094a 0xe03c0fe07fffffff 0xfff07fc7fc063fff

def z1180 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fb1ffec000000

def z1181 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1fc3f00000000000 0x000fc1b803f80000

def z1182 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff0007fffff0 0x000fc7fe03fe1fe0

def z1183 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe00001ffff 0x000fc1fe03fe03f0

def z1184 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000781fff0 0x03ffc5fe13fe13e3

def z1185 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe07ffffff0 0xfc0fcffe2ffe3fec

def z1186 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffc3fffff87e0000 0x000ffa0003ffec00

def z1187 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x0001fffffc000000

def z1188 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffff8001fff0 0x000ff1fe03ffc3e0

def z1189 : W := mkw 0x0c00001040001000 0x820c18daf4000000 0x0000000000000000 0x000e31fffc000000

def z1190 : W := mkw 0xcc4000b150113204 0xe82c18c161816094 0xffc000fff8001f0f 0xfc0e39c1e1c1e19c

def z1191 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x0003f0ff8781e0ff 0x03f1b5b9d239d273

def z1192 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0x1fc000ff8001ff0f 0xfc0e31c1e3c1c39c

def z1193 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe07801ffff 0xfc0fcffe3ffe23fc

def z1194 : W := mkw 0x31ae6a020024ccc8 0x10c2c12e026e0360 0xffffff000001e0f0 0x000fc1be03fe0260

def z1195 : W := mkw 0x823084c422380000 0x4100000000daf400 0xfffffffffffe0000 0x000e000003fffc00

def z1196 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000ff3bfcc000000

def z1197 : W := mkw 0x8a3084d462380000 0x4104180000daf400 0xfffffffffffe0000 0x000e7e0003fffc00

def z1198 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0x1fc3f000000000f0 0x000f81be03f80060

def z1199 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e31c1c3c1e39c

def z1200 : W := mkw 0x312e48020024c888 0x10c2c124026e0360 0xffffff000001fff0 0x000fc1fe03fe03e0

def z1201 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x000000000001ff0f 0xfc0ffffffc00039c

def z1202 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xfffc00ffff81ffff 0xfffe7fc7ffc1f3ff

def z1203 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x003c00e007800000 0x000ffffffc001000

def z1204 : W := mkw 0x1e338c5c66681000 0x830ffedaf45a9400 0xe03fffe07ffe0000 0x000ffffffc3e3c00

def z1205 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0x1fc000fff801ff0f 0xfc0e39c1e3c1e39c

def z1206 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0xffc3ff1ff87e0000 0x000fffffffffec00

def z1207 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0xe03c00e07f81ffff 0xfffffffffc0033ff

def z1208 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0xfffff0000001fff0 0x000f81f803f803e0

def z1209 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000ffe0013fffc00

def z1210 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003fffff87ffe0ff 0x03f1f7b9d23fde73

def z1211 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff0007fffff0 0x03ffcffe3ffe1fe3

def z1212 : W := mkw 0x1403080804401000 0x820be6daf4000000 0x0000000000000000 0x0001cffffc000000

def z1213 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffffffffffe0ff 0x03fffe0003fffe73

def z1214 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0xffc0000000000000 0x000fffffffc00000

def z1215 : W := mkw 0x0400000000001000 0x820800daf4000000 0x0000000000000000 0x000e01fffc000000

def z1216 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0xe03c0fe07fffe0ff 0x03fffffffc063e73

def z1217 : W := mkw 0x9a338cdc66780000 0x4307fe1090daf400 0xffffffffffffe0ff 0x03ffffb9d3fffe73

def z1218 : W := mkw 0x9a338cdc66780000 0xc307fe10f4daf400 0xfffffffffffe0000 0x000fffb9fffffc00

def z1219 : W := mkw 0x4508400200019888 0x208801e0032002a0 0xfffff0e07f81ffff 0xffff8df833f833ff

def z1220 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff8781e0ff 0x03f1ffb9d239d273

def z1221 : W := mkw 0x92338ccc26780000 0x4103e60000daf400 0xfffffffffffe0000 0x000fc60003fffc00

def z1222 : W := mkw 0xa85511f9dd9c6337 0xdb653c15f895f95f 0xe03c0fffffffffff 0xfff07e47fc07ffff

def z1223 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x000000e00780000f 0x03fffffffc001013

def z1224 : W := mkw 0x200501080c844111 0x124124149804094a 0xe03c0fe07fffffff 0xfff1b5b9d0063fff

def z1225 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000ffff81ff0f 0xfffe3dc1f3c1f39f

def z1226 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x000000e07ffe0000 0x000ffffffc003c00

def z1227 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000ff1fffc000000

def z1228 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fffbffc000000

def z1229 : W := mkw 0x211c5162898ce9bb 0x19e001250a359b7b 0x003ff0ff8781ffff 0xfff000000239d3ff

def z1230 : W := mkw 0x0319d46ea748a8aa 0x0ba1273192319631 0x003ff0ff87ffe0ff 0x03f1b7b9d239de73

def z1231 : W := mkw 0x1003080804400000 0x0203e61a94000000 0x0000000000000000 0x0001c7bfdc000000

def z1232 : W := mkw 0xcc4000b150113204 0xe82c18c161816094 0xffc000fff8001f0f 0xfc0e3841e3c1e19c

def z1233 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc0001ff801ff00 0xfc0e39c1e3c1e38c

def z1234 : W := mkw 0x1c13085844481000 0x830ffedaf4109000 0x003ff00007800000 0x000ffffffc381000

def z1235 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffff1f87fe0000 0x000ff60003ffdc00

def z1236 : W := mkw 0x885111f9dd982337 0xcb253c11f891f81f 0x000000fffffe000f 0xfff03e01fc01fc1f

def z1237 : W := mkw 0x1803081844400000 0x0207fe1090000000 0x0000000000000000 0x000ffffffc000000

def z1238 : W := mkw 0x0400000000001000 0x820800daf4000000 0x003c00e00781e0ff 0x03f005fffc001273

def z1239 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffc3ff0000001f00 0x000f81b803fe0180

def z1240 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000ff00003fffc00

def z1241 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0x1fc3f0000001fff0 0x000fc1fe03f803e0

def z1242 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x003c0000078000f0 0x03fffffffc001063

def z1243 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fffffec000000

def z1244 : W := mkw 0x65ac62020025dcc8 0x30c801e4036e03e0 0xffffff000001fff0 0x000f81f803fe03e0

def z1245 : W := mkw 0x92338ccc26380000 0x4103e40000daf400 0xfffffffffffe0000 0x000ff40003fffc00

def z1246 : W := mkw 0x1e338c5c66681000 0x830ffedaf45a9400 0x0003f00000000000 0x000ffffffc380000

def z1247 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0x003ff0ff878000ff 0x03f1b5b9d239d073

def z1248 : W := mkw 0x0108400200008888 0x0080012002200220 0xfffff0000001e0f0 0x000f81b803f80260

def z1249 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e7bc7efc1e39c

def z1250 : W := mkw 0x30ae2a000024c440 0x10c2c02e006e0160 0xffffff00000000f0 0x000fc03e01fe0060

def z1251 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe07fffffff 0xffffc1fe3ffe3fff

def z1252 : W := mkw 0x9e238c9c66701000 0xc20ffedaf4ca6400 0xffc00ffff87e0000 0x000fffffffc7ec00

def z1253 : W := mkw 0x4508400200019888 0x208801e0032002a0 0x1fc3f00000000000 0x000f81b803f80000

def z1254 : W := mkw 0xcd4040b350513a8c 0xe82c1bc167816294 0xffc000fff801ff0f 0xfc0e3bc1efc1e39c

def z1255 : W := mkw 0x8a3184dc66380000 0x41053c0000daf400 0xfffffffffffe0000 0x000fbc0003fffc00

def z1256 : W := mkw 0x9e338cdc66781000 0xc30ffedaf4daf400 0xfffffffffffe0000 0x000fffbfdffffc00

def z1257 : W := mkw 0x75ae6a220025fcc8 0x38eac1ef036f03f0 0xffffff000001ffff 0x000fc1ffc3fe03f0

def z1258 : W := mkw 0x9e228c9462701000 0xc20edadaf4ca6400 0xffc00f00787e0000 0x000e4bfffdc62c00

def z1259 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0xffc000fff801ff0f 0xfc0e3981e3c1e39c

def z1260 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff00007ffff0 0x000fc3fe0ffe0fe0

def z1261 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0xfffff0ff8781e0ff 0x03ffb5b9d3f9d273

def z1262 : W := mkw 0x654c51239985fbbf 0xbae801f5fb250bff 0x000000000001ffff 0xfff001fffc0003ff

def z1263 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe07ffffff0 0x000fc1fe03fe3fe0

def z1264 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff000001fff0 0x03ffc1fe1ffe03e3

def z1265 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000fcbfe2ffe03e0

def z1266 : W := mkw 0x75ae6a220025fcc8 0x38eac1ef036f03f0 0xffffff1f8001fff0 0x000ff1ffc3ffc3e0

def z1267 : W := mkw 0x0000000000000000 0x0200001a94000000 0x0000000000000000 0x000001bfdc000000

def z1268 : W := mkw 0xcd4040b350113a8c 0xe82c19c163816294 0x1fc0001f80001f00 0xfc0e31c1e3c1c18c

def z1269 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe007ffffff 0x03ffc7fe1ffe1ff3

def z1270 : W := mkw 0x8a3084d462380000 0x4104180000daf400 0xfffffffffffe0000 0x000e300003fffc00

def z1271 : W := mkw 0x0119506a8508a8aa 0x0ba1253192319231 0xe03ff0ff8781ffff 0x03f1b5f9d239d3f3

def z1272 : W := mkw 0x9a338cdc66780000 0x4307fe1a94daf400 0xfffffffffffe0000 0x000ffe3803fffc00

def z1273 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe00781ffff 0x03ffcffe3ffe13f3

def z1274 : W := mkw 0x75ae6a220025fcc8 0x38eac1ef036f03f0 0xffffffff8781ffff 0x03fff5ffd3ffd3f3

def z1275 : W := mkw 0x650c41020885d999 0x30c801e40b240bea 0xffffffe07fffffff 0xffffcffe3ffe3fff

def z1276 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff00787ffff0 0xfc0fc1fe03fe2fec

def z1277 : W := mkw 0x1c13085844481000 0x830ffedaf4109000 0x003ff0ff8781e0ff 0x03fffffffe39d273

def z1278 : W := mkw 0x9a328cd462780000 0x4106da0000daf400 0xfffffffffffe0000 0x000fca0003fffc00

def z1279 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff007801fff0 0xfc0fc9fe23fe23ec

def z1280 : W := mkw 0x74ae2a000025d440 0x30cac0ee016e01e0 0xffffff000001fff0 0x000fc07e01fe03e0

def z1281 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffffe07fffffff 0xffffc5fe13fe3fff

def z1282 : W := mkw 0x9a338cdc66780000 0xc107fe0064daf400 0xfffffffffffe0000 0x000ffe002ffffc00

def z1283 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe07fffffff 0xfc0fcffe23fe3ffc

def z1284 : W := mkw 0x75ae6b0208a5ddd9 0x30cac1ee0b6e0bea 0xffffff000001ffff 0xffffcffe3ffe03ff

def z1285 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffffe07f81ffff 0xffffcdfe33fe33ff

def z1286 : W := mkw 0x1402080000001000 0x820ac0daf4000000 0x0000000000000000 0x0001c1fffc000000

def z1287 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x000000e00001e00f 0x000ffffffc000210

def z1288 : W := mkw 0x74ae2a000025d440 0x30cac0ee016e01e0 0xffc3ff0000001f00 0x000fc07e01fe0180

def z1289 : W := mkw 0x0c01001844401000 0x820d3edaf4000000 0x0000000000000000 0x0001bffffc000000

def z1290 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0xffffff0000000000 0x000f81b803fe0000

def z1291 : W := mkw 0x2004010008844111 0x104000040804094a 0x003c0fe07fffffff 0xfff04e463c063fff

def z1292 : W := mkw 0x0400000000001000 0x820800daf4000000 0xe00000e07801ff0f 0xfc0009fffc00239c

def z1293 : W := mkw 0x30ae2b0008a4c551 0x10c2c02e086e096a 0xffffffe07ffe00f0 0x03ffce3e1ffe3c63

def z1294 : W := mkw 0x75ae6a020025dcc8 0x30cac1ee036e03e0 0xffffff000001fff0 0x000fcffe03fe03e0

def z1295 : W := mkw 0x55aa6a0200219cc8 0x208ac1ea036a02a0 0x1ffff0000001e0f0 0x000fc1fe03f80260

def z1296 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe1f00 0xfc0ffe4023fffd8c

def z1297 : W := mkw 0x1c03081844401000 0x820ffedaf4000000 0x0000000000000000 0x000fb1bfdc000000

def z1298 : W := mkw 0x1c02081040001000 0x820ed8daf4000000 0x0000000000000000 0x000ff9fffc000000

def z1299 : W := mkw 0x1e338c5c66681000 0x830ffedaf45a9400 0xffffff0007fe0000 0x000ffffffffe1c00

def z1300 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xfffffffffffe0000 0x000ff60003fffc00

def z1301 : W := mkw 0x92328cc422380000 0x4102c00000daf400 0xfffffffffffe0000 0x000e400003fffc00

def z1302 : W := mkw 0x9a338cdc66780000 0x4107fe0000daf400 0xffffff1ff87e0000 0x000ffa0003ffec00

def z1303 : W := mkw 0xaa1595fcefdc6133 0x5b653e159895fd5b 0xe03c0fffffffffff 0xfff07e47fc07ffff

def z1304 : W := mkw 0x9a338cdc66780000 0xc307fe10f4daf400 0xfffffffffffe0000 0x000ffffffffffc00

def z1305 : W := mkw 0x8a1184dc66580000 0x43053e109090f400 0x000000fffffe0000 0x00003e01fc01fc00

def z1306 : W := mkw 0x8a1184dc66580000 0x43053e109490f400 0x000000fffffe0000 0x00003e01dc01fc00

def z1307 : W := mkw 0x71ae6a020025ccc8 0xb2c2c134f76e03e0 0xffffff000001fff0 0x000fc001fffe03e0

def z1308 : W := mkw 0x9a338cdc66780000 0x4307fe1090daf400 0xfffffffffffe0000 0x000fffbfdffffc00

def z1309 : W := mkw 0x1022080000200000 0x0002c000004a0000 0xffffff0000000000 0x000fc1fe03fe0000

def z1310 : W := mkw 0x8e1184dc66581000 0xc30d3ed0f490f400 0x000000fffffe0000 0x00003fc1fc01fc00

def z1311 : W := mkw 0x9a338cdc66780000 0x4307fe1a94daf400 0xfffffffffffe0000 0x000ffffffffffc00

def z1312 : W := mkw 0x112a58228120a8aa 0x08a2c121026b0231 0xffffff000001e0ff 0x03ffc1b803fe0273

def z1313 : W := mkw 0x1022080000200000 0x0002c00a004a0000 0xffffff0000000000 0x000fc1be03fe0000

def z1314 : W := mkw 0xcf51c4ff76593a8c 0xeb2d3fd1f791f694 0x000000ffffffff0f 0xfc003fc1fc01ff9c

def z1315 : W := mkw 0x5373cc6f36692a8c 0x2b23e71b975b9694 0x003fff0007ffff0f 0xfc01c63e1c3e1f9c

def z1316 : W := mkw 0xeb9de6de665dccc8 0xf3c53f34f7b4f7e0 0x000000fffffffff0 0x00003e01fc01ffe0

def z1317 : W := mkw 0xc94040b350112a8c 0x6a24191b97816294 0xffc000fff801ff0f 0xfc0e383e1fc1e39c

def z1318 : W := mkw 0x8e1184dc66581000 0xc30d3edaf490f400 0x000000fffffe0000 0x00003e47fc01fc00

def z1319 : W := mkw 0x0519506a8508b8aa 0x89a925eb66319231 0x003ff0ff8781e0ff 0x03f1b4462e39d273

def z1320 : W := mkw 0x9f2adcb6e370b8aa 0xc8aedbeb66eb6631 0xffc00f00787fe0ff 0x03fe4a462dc62e73

def z1321 : W := mkw 0x9a338cdc66780000 0xc307fe1af4daf400 0xfffffffffffe0000 0x000fffbffffffc00

def bk0_0 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z2,z3,z4,z5,z6])],[],[(0,[z7,z0,z2,z8,z4,z5,z6]),(0,[z9,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z10,z4,z5,z6])],[(0,[z11,z0,z2,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z5,z6,z13]),(0,[z14,z2,z3,z4,z15,z5,z6]),(0,[z0,z16,z17,z3,z4,z5,z6]),(0,[z0,z2,z18,z3,z4,z5,z6]),(0,[z0,z2,z19,z3,z4,z5,z6]),(0,[z0,z2,z3,z20,z4,z5,z6])],[(0,[z0,z21,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z22,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z23,z6])],[(0,[z0,z2,z3,z4,z5,z24,z6])],[(0,[z25,z0,z2,z3,z4,z5,z6]),(0,[z26,z0,z2,z3,z4,z5,z27]),(0,[z0,z17,z3,z4,z28,z5,z6]),(0,[z0,z2,z3,z29,z4,z5,z6])],[(0,[z30,z0,z17,z3,z4,z5,z6]),(0,[z0,z21,z31,z3,z4,z5,z6])],[(0,[z32,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z33,z5,z6]),(0,[z0,z2,z3,z4,z5,z34,z6]),(0,[z0,z2,z3,z4,z5,z6,z35])],[(0,[z0,z36,z2,z3,z4,z6,z37]),(0,[z0,z2,z3,z4,z38,z5,z6]),(0,[z0,z2,z3,z4,z5,z39,z6]),(0,[z0,z2,z3,z40,z5,z6,z27]),(1,[z0,z2,z3,z4,z5,z41])],[(0,[z42,z0,z2,z3,z4,z5,z6]),(0,[z0,z17,z3,z4,z43,z5,z6]),(0,[z0,z3,z44,z45,z4,z5,z6]),(1,[z0,z2,z3,z46,z5,z6])],[(0,[z47,z0,z3,z4,z5,z48,z6]),(0,[z49,z0,z2,z3,z4,z5,z6]),(0,[z50,z0,z17,z3,z4,z5,z6]),(0,[z0,z2,z51,z3,z4,z5,z6]),(1,[z0,z36,z3,z4,z48,z6])],[(0,[z52,z0,z2,z3,z4,z5,z6]),(0,[z53,z0,z2,z3,z54,z5,z6]),(0,[z0,z17,z3,z55,z4,z5,z6]),(0,[z0,z56,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z57,z4,z5,z58]),(0,[z0,z2,z3,z4,z5,z59,z60]),(0,[z0,z2,z3,z4,z5,z6,z61]),(0,[z0,z2,z3,z40,z5,z6,z62])],[(0,[z63,z0,z2,z3,z4,z5,z6]),(0,[z64,z0,z2,z3,z4,z5,z6]),(0,[z0,z65,z2,z3,z4,z5,z6]),(0,[z0,z17,z66,z3,z4,z5,z6]),(0,[z0,z67,z2,z3,z4,z5,z6]),(1,[z0,z68,z3,z4,z5,z6])],[(0,[z0,z69,z2,z3,z55,z5,z6]),(0,[z0,z2,z70,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z71,z6,z72])],[(0,[z0,z17,z3,z4,z5,z60,z6]),(0,[z0,z73,z2,z3,z55,z5,z6]),(0,[z0,z3,z4,z40,z5,z48,z6])]]

def bk0_1 : List (List (ℕ × List W)) :=
  [[(0,[z0,z73,z2,z3,z43,z5,z6]),(0,[z0,z2,z3,z4,z74,z5,z6]),(1,[z0,z3,z4,z5,z75,z6])],[(0,[z14,z0,z36,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z37])],[(0,[z0,z76,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z77,z6])],[(0,[z78,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z79,z4,z5,z6]),(0,[z0,z2,z3,z4,z80,z5,z6])],[(0,[z0,z2,z3,z4,z81,z5,z6])],[(0,[z82,z0,z2,z3,z4,z83,z6]),(0,[z0,z2,z3,z84,z40,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z85]),(0,[z0,z3,z4,z5,z48,z86,z6])],[(0,[z0,z2,z3,z87,z4,z5,z6]),(0,[z0,z2,z3,z88,z4,z5,z6])],[(0,[z0,z89,z2,z3,z40,z5,z6]),(0,[z0,z90,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z4,z91,z5,z6])],[],[(0,[z92,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z93,z4,z5,z6])],[(0,[z53,z0,z2,z3,z40,z5,z6]),(0,[z0,z17,z3,z57,z4,z5,z6]),(0,[z0,z94,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z95,z40,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z96]),(0,[z2,z3,z45,z4,z5,z97,z6])],[(0,[z0,z17,z3,z4,z5,z6,z58]),(0,[z0,z31,z2,z3,z4,z5,z6])],[(0,[z98,z0,z70,z3,z4,z5,z6]),(0,[z99,z0,z2,z3,z28,z5,z6]),(0,[z0,z2,z3,z4,z100,z5,z6]),(0,[z0,z2,z3,z4,z101,z6,z72])],[(0,[z26,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z102,z5,z6]),(0,[z0,z2,z3,z4,z103,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z104])],[(0,[z98,z0,z2,z3,z54,z5,z6]),(0,[z0,z105,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z106,z4,z5,z6]),(0,[z0,z3,z4,z5,z48,z107,z6]),(1,[z108,z2,z3,z4,z5,z6])],[(0,[z109,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z110,z3,z111,z5,z6]),(0,[z0,z2,z3,z54,z5,z6,z112]),(0,[z0,z2,z3,z33,z5,z97,z6])]]

def bk0_2 : List (List (ℕ × List W)) :=
  [[(0,[z113,z0,z2,z3,z4,z5,z6])],[(0,[z82,z114,z2,z3,z4,z5,z6]),(0,[z115,z0,z17,z3,z4,z5,z6]),(0,[z116,z0,z2,z3,z4,z5,z6]),(0,[z0,z17,z3,z117,z4,z5,z6]),(0,[z0,z2,z3,z95,z4,z28,z5]),(0,[z0,z2,z3,z54,z28,z5,z6]),(0,[z0,z2,z3,z40,z5,z101,z6])],[(0,[z118,z0,z17,z3,z4,z5,z6]),(0,[z0,z119,z2,z3,z54,z5,z6]),(0,[z0,z120,z2,z3,z4,z5,z6]),(0,[z0,z121,z2,z3,z4,z5,z6]),(0,[z0,z122,z2,z3,z4,z5,z6])],[(0,[z0,z69,z2,z3,z4,z123,z6])],[(0,[z0,z2,z3,z54,z55,z5,z6])],[(0,[z124,z0,z2,z3,z4,z5,z6]),(0,[z125,z2,z3,z45,z4,z5,z6]),(0,[z0,z2,z3,z54,z43,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z126])],[(0,[z0,z127,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z128,z4,z5,z6]),(0,[z0,z2,z3,z129,z4,z5,z6]),(0,[z0,z2,z3,z4,z130,z5,z6]),(1,[z0,z3,z4,z71,z48,z6])],[(0,[z0,z131,z2,z3,z4,z5,z6]),(0,[z0,z2,z132,z3,z4,z5,z6]),(0,[z0,z2,z3,z133,z4,z5,z6]),(0,[z0,z2,z3,z134,z4,z5,z6]),(1,[z0,z119,z3,z4,z5,z107])],[(0,[z115,z0,z2,z3,z4,z5,z135]),(0,[z0,z2,z3,z4,z136,z5,z6]),(0,[z0,z2,z3,z4,z137,z5,z6]),(0,[z0,z2,z3,z4,z138,z5,z6])],[(0,[z0,z139,z89,z3,z4,z5,z6]),(0,[z0,z2,z140,z3,z4,z5,z6]),(1,[z0,z141,z2,z3,z5,z6])],[(0,[z0,z2,z3,z54,z5,z60,z6]),(0,[z0,z2,z3,z4,z15,z5,z6]),(0,[z0,z3,z4,z142,z5,z143,z6])],[(0,[z124,z144,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z145,z6])],[(0,[z98,z0,z2,z3,z40,z5,z6]),(0,[z47,z0,z2,z3,z4,z97,z6])],[(0,[z0,z17,z3,z4,z146,z5,z6]),(0,[z0,z2,z147,z3,z4,z5,z6]),(0,[z0,z2,z148,z3,z149,z5,z6])],[(0,[z150,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z151,z4,z5,z6]),(0,[z0,z3,z152,z4,z5,z6,z13]),(0,[z21,z2,z66,z3,z4,z5,z6]),(1,[z0,z3,z153,z4,z48,z6])]]

def bk0_3 : List (List (ℕ × List W)) :=
  [[(0,[z14,z0,z2,z3,z154,z5,z6]),(0,[z0,z119,z2,z3,z40,z5,z6])],[(0,[z155,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z156,z5,z6,z37]),(1,[z0,z17,z3,z4,z48,z6])],[(0,[z0,z2,z157,z3,z158,z5,z6]),(0,[z0,z2,z148,z3,z54,z5,z6]),(0,[z0,z3,z117,z4,z5,z48,z6])],[(0,[z124,z159,z2,z3,z4,z5,z6]),(0,[z0,z160,z2,z3,z4,z5,z6]),(0,[z0,z161,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z162])],[(0,[z82,z0,z17,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z163,z48,z6])],[(0,[z164,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z165,z5,z6]),(0,[z0,z2,z3,z4,z166,z5,z6]),(1,[z0,z2,z3,z165,z5,z6])],[(0,[z14,z0,z3,z4,z5,z48,z6]),(0,[z0,z69,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z54,z5,z6,z58]),(0,[z0,z2,z3,z4,z5,z6,z13])],[(0,[z0,z2,z3,z4,z5,z167,z6])],[(0,[z0,z2,z3,z4,z5,z168,z6])],[(0,[z0,z169,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z170]),(0,[z0,z2,z3,z40,z5,z59,z6]),(0,[z0,z110,z3,z4,z5,z48,z6])],[(0,[z124,z0,z2,z4,z5,z6,z58]),(0,[z0,z2,z3,z4,z171,z5,z6])],[(0,[z0,z36,z2,z3,z54,z5,z6]),(0,[z0,z2,z3,z172,z4,z5,z6])],[],[(0,[z173,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z174,z4,z5,z6])],[(0,[z175,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z176,z4,z5,z6]),(0,[z0,z2,z3,z4,z4,z5,z6])],[(0,[z177,z0,z2,z3,z4,z5,z6])]]

def bk0_4 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z178,z4,z5,z6])],[(1,[z0,z2,z3,z4,z179,z6])],[(0,[z180,z0,z2,z3,z4,z5,z6]),(0,[z0,z181,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z182,z5,z6]),(0,[z0,z2,z4,z5,z60,z6,z58]),(1,[z0,z2,z54,z40,z5,z6])],[(0,[z0,z2,z3,z4,z5,z183,z6]),(1,[z0,z2,z3,z184,z5,z6])],[(0,[z185,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z153,z40,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z186]),(1,[z144,z2,z3,z4,z5,z6])],[(0,[z187,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z188,z3,z4,z5,z6]),(0,[z0,z2,z3,z189,z4,z5,z6]),(0,[z0,z2,z3,z4,z142,z5,z6]),(1,[z0,z2,z3,z4,z190,z6])],[(0,[z191,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z72,z58])],[(0,[z192,z0,z2,z3,z4,z5,z6]),(0,[z193,z0,z17,z3,z4,z5,z6]),(0,[z0,z2,z3,z153,z4,z6,z37])],[(0,[z194,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z195,z4,z5,z6]),(0,[z0,z2,z3,z54,z146,z5,z6]),(0,[z0,z2,z3,z40,z5,z6,z72])],[(0,[z196,z0,z2,z3,z4,z5,z6]),(0,[z0,z36,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z4,z197,z5,z6]),(0,[z0,z2,z3,z4,z198,z5,z6])],[(0,[z199,z0,z2,z3,z4,z5,z6]),(1,[z0,z200,z3,z4,z5,z6])],[(1,[z0,z2,z3,z33,z5,z6])],[(0,[z0,z89,z2,z3,z54,z5,z6]),(0,[z0,z2,z3,z201,z4,z5,z6]),(0,[z0,z2,z3,z202,z4,z5,z6]),(1,[z0,z203,z3,z4,z5,z6])],[(0,[z0,z2,z3,z204,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z205]),(0,[z0,z2,z3,z4,z5,z6,z206])],[],[(0,[z207,z0,z17,z3,z4,z5,z6]),(0,[z0,z17,z208,z3,z4,z5,z6]),(0,[z0,z2,z3,z95,z54,z5,z6]),(0,[z0,z2,z3,z4,z209,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z210]),(1,[z0,z31,z110,z4,z5,z6])]]

def bk0_5 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z117,z5,z6,z62])],[(0,[z0,z2,z3,z4,z211,z5,z6]),(0,[z0,z2,z3,z4,z5,z212,z6])],[(0,[z0,z213,z2,z3,z4,z5,z6])],[],[(0,[z0,z17,z3,z95,z4,z5,z6]),(0,[z0,z2,z3,z214,z40,z5,z6]),(0,[z0,z2,z3,z215,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z216]),(0,[z0,z2,z3,z4,z5,z6,z217])],[(0,[z218,z0,z2,z3,z54,z5,z6]),(0,[z219,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z220,z5,z6])],[(0,[z221,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z153,z4,z5,z48,z6])],[(0,[z47,z2,z3,z4,z5,z97,z6]),(0,[z0,z222,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z223]),(1,[z0,z224,z3,z4,z5,z6])],[(0,[z0,z17,z2,z3,z4,z5,z6])],[],[],[(0,[z12,z0,z110,z3,z4,z5,z6]),(0,[z50,z0,z2,z3,z40,z5,z6]),(0,[z0,z36,z2,z3,z153,z5,z6]),(0,[z0,z2,z3,z4,z5,z27,z62])],[(0,[z115,z0,z2,z3,z4,z71,z6])],[(0,[z225,z0,z2,z3,z40,z5,z6])],[(0,[z47,z0,z203,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z226,z6])],[(0,[z82,z0,z2,z3,z4,z5,z61]),(0,[z124,z0,z2,z3,z4,z5,z60]),(0,[z12,z0,z66,z3,z4,z5,z6]),(0,[z26,z0,z2,z3,z215,z5,z6]),(0,[z227,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z228,z6]),(0,[z0,z3,z4,z5,z48,z60,z6])]]

def bk0_6 : List (List (ℕ × List W)) :=
  [[(0,[z115,z0,z2,z3,z4,z101,z6]),(0,[z0,z229,z2,z3,z4,z5,z6]),(1,[z26,z2,z3,z4,z5,z27]),(1,[z0,z2,z3,z103,z5,z6]),(1,[z0,z3,z40,z5,z48,z6])],[],[(0,[z0,z230,z2,z3,z4,z5,z6])],[(0,[z218,z0,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z4,z231,z5,z6]),(0,[z0,z2,z3,z4,z156,z5,z6]),(0,[z0,z3,z4,z5,z48,z48,z6])],[(0,[z0,z2,z232,z3,z4,z5,z6]),(0,[z0,z2,z3,z54,z5,z6,z233]),(0,[z0,z2,z3,z4,z234,z5,z6])],[(0,[z12,z0,z3,z4,z5,z48,z6])],[(0,[z125,z26,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z235,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z236,z6])],[(0,[z82,z0,z2,z3,z237,z5,z6]),(0,[z0,z2,z3,z4,z238,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z239])],[(0,[z0,z240,z17,z3,z4,z5,z6]),(0,[z0,z241,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z54,z242,z5,z6]),(0,[z2,z3,z4,z5,z59,z6,z27]),(1,[z0,z2,z3,z4,z243,z6])],[(0,[z7,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z57,z4,z48,z6]),(0,[z0,z2,z3,z4,z5,z244,z6])],[(0,[z0,z69,z2,z3,z54,z5,z6]),(0,[z0,z2,z3,z57,z46,z5,z6]),(0,[z0,z3,z4,z5,z48,z6,z58])],[(0,[z245,z0,z2,z3,z4,z5,z6]),(0,[z0,z73,z2,z3,z54,z5,z6]),(0,[z0,z2,z3,z246,z4,z5,z6]),(1,[z0,z3,z4,z5,z247,z6])],[(0,[z0,z248,z2,z3,z54,z5,z6]),(0,[z0,z2,z157,z3,z165,z5,z6])],[(0,[z249,z0,z2,z3,z4,z5,z6]),(0,[z0,z17,z181,z3,z4,z5,z6]),(0,[z0,z2,z3,z250,z4,z5,z6]),(0,[z0,z148,z3,z4,z5,z48,z6])],[(0,[z0,z36,z2,z3,z5,z6,z62]),(1,[z0,z251,z3,z4,z5,z6])]]

def bk0_7 : List (List (ℕ × List W)) :=
  [[(0,[z125,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z252,z6]),(0,[z0,z2,z3,z4,z5,z6,z253])],[],[(0,[z50,z0,z3,z4,z5,z6,z13]),(0,[z0,z2,z254,z3,z54,z5,z6]),(0,[z0,z2,z3,z255,z4,z5,z6])],[(0,[z82,z0,z2,z3,z4,z5,z256]),(0,[z257,z0,z2,z3,z4,z5,z6]),(0,[z0,z17,z3,z4,z40,z5,z6]),(0,[z0,z2,z258,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z259,z5,z6])],[(0,[z0,z260,z2,z3,z4,z5,z6]),(1,[z0,z230,z3,z4,z5,z6])],[(0,[z261,z0,z2,z3,z4,z5,z6]),(0,[z0,z17,z2,z3,z4,z146,z6]),(0,[z0,z262,z2,z3,z4,z5,z6]),(0,[z0,z2,z157,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z263,z6]),(0,[z0,z3,z4,z71,z5,z48,z6])],[(0,[z26,z0,z2,z3,z264,z5,z6]),(0,[z0,z2,z3,z54,z255,z5,z6]),(0,[z0,z2,z3,z4,z5,z265,z6])],[(0,[z0,z21,z3,z152,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z266,z6]),(0,[z0,z2,z3,z40,z5,z6,z37]),(0,[z0,z3,z57,z4,z5,z48,z6])],[],[(0,[z0,z17,z148,z3,z4,z5,z6]),(0,[z0,z73,z2,z3,z40,z5,z6]),(0,[z0,z267,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z268])],[(0,[z0,z269,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z153,z4,z156,z6])],[(0,[z99,z0,z2,z3,z54,z5,z6]),(0,[z50,z21,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z270,z5,z6])],[(0,[z50,z0,z119,z3,z4,z5,z6]),(0,[z0,z2,z3,z271,z4,z5,z6]),(0,[z0,z3,z4,z5,z5,z48,z6])],[(0,[z82,z0,z2,z3,z4,z34,z6]),(0,[z0,z2,z272,z3,z4,z5,z6]),(0,[z0,z2,z3,z273,z4,z5,z6]),(0,[z0,z2,z3,z4,z274,z5,z6]),(1,[z275,z2,z3,z4,z5,z6])],[(0,[z0,z2,z276,z3,z4,z5,z6]),(1,[z0,z2,z3,z277,z5,z6])]]

def bk0_8 : List (List (ℕ × List W)) :=
  [[(0,[z82,z0,z3,z152,z4,z5,z6]),(0,[z278,z0,z2,z3,z4,z5,z6]),(0,[z0,z181,z2,z3,z40,z5,z6]),(0,[z0,z36,z2,z3,z4,z156,z6]),(0,[z0,z2,z8,z4,z40,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z279])],[(0,[z0,z2,z254,z3,z40,z5,z6]),(0,[z0,z2,z3,z54,z54,z5,z6]),(1,[z0,z2,z3,z4,z5,z6])],[(0,[z280,z0,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z281,z4,z5,z6]),(0,[z0,z2,z3,z282,z4,z5,z6]),(0,[z0,z2,z3,z283,z4,z5,z6]),(0,[z0,z2,z3,z54,z284,z5,z6]),(0,[z0,z2,z3,z285,z4,z5,z6])],[(0,[z286,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z287,z5,z6]),(0,[z0,z288,z3,z4,z5,z48,z6]),(1,[z0,z3,z4,z5,z143,z6])],[(0,[z289,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z290])],[(0,[z291,z0,z2,z3,z4,z5,z6]),(0,[z0,z292,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z154,z4,z5,z62]),(0,[z0,z2,z3,z4,z293,z5,z6]),(1,[z0,z2,z3,z182,z5,z6])],[(0,[z294,z0,z2,z3,z54,z5,z6])],[(0,[z0,z2,z3,z4,z295,z5,z6]),(0,[z0,z3,z4,z5,z107,z6,z13])],[(0,[z124,z0,z2,z3,z296,z5,z6]),(0,[z26,z0,z17,z3,z4,z5,z6]),(1,[z0,z69,z3,z55,z5,z6])],[(0,[z0,z2,z3,z4,z5,z297,z6])],[(0,[z99,z0,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z298,z4,z5,z6])],[(0,[z0,z17,z3,z4,z5,z5,z6]),(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z2,z3,z277,z4,z5,z6])],[(0,[z0,z2,z3,z4,z299,z5,z6])],[(0,[z300,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z301,z3,z4,z5,z6]),(0,[z0,z2,z3,z302,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z86,z6]),(0,[z0,z3,z4,z71,z5,z75,z6])],[(0,[z303,z0,z2,z3,z4,z5,z6]),(0,[z0,z181,z2,z3,z4,z5,z107]),(0,[z0,z2,z3,z95,z154,z5,z6]),(0,[z0,z2,z3,z4,z146,z97,z6])],[(0,[z82,z50,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z304,z54,z5,z6]),(0,[z0,z2,z3,z54,z40,z5,z6]),(0,[z0,z2,z3,z4,z243,z5,z6]),(0,[z0,z2,z3,z40,z137,z5,z6]),(1,[z159,z2,z3,z4,z5,z6])]]

def bk0_9 : List (List (ℕ × List W)) :=
  [[(0,[z98,z0,z305,z3,z4,z5,z6]),(0,[z124,z0,z17,z3,z4,z5,z6]),(0,[z50,z0,z2,z3,z54,z5,z6])],[(0,[z99,z14,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z306,z4,z5,z6]),(0,[z0,z2,z3,z40,z15,z5,z6]),(0,[z0,z3,z152,z4,z5,z48,z6])],[(0,[z0,z131,z17,z3,z4,z5,z6]),(0,[z0,z2,z3,z307,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z308]),(0,[z0,z8,z3,z4,z5,z48,z6])],[(0,[z47,z0,z2,z3,z4,z5,z6]),(0,[z309,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z310,z6]),(0,[z2,z3,z4,z142,z5,z97,z6])],[(0,[z53,z0,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z4,z5,z311,z6]),(0,[z0,z2,z3,z4,z5,z6,z312])],[(0,[z0,z313,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z314,z5,z6]),(0,[z0,z2,z3,z4,z5,z107,z6])],[(0,[z26,z2,z3,z4,z5,z6,z27]),(0,[z0,z2,z3,z315,z4,z5,z6])],[(0,[z0,z181,z3,z4,z5,z6,z13]),(0,[z0,z2,z3,z4,z264,z5,z6]),(0,[z0,z2,z3,z4,z5,z48,z6])],[(0,[z316,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z154,z4,z5,z6]),(1,[z0,z2,z3,z4,z317,z6])],[(0,[z12,z2,z66,z3,z4,z5,z6]),(0,[z0,z318,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z45,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z319,z6])],[(0,[z0,z2,z320,z3,z4,z5,z6])],[(0,[z125,z0,z2,z3,z4,z5,z27])],[(0,[z53,z0,z2,z148,z4,z5,z6]),(0,[z0,z17,z36,z3,z4,z5,z6]),(0,[z0,z2,z321,z3,z4,z5,z6]),(0,[z0,z2,z3,z40,z5,z6,z13])],[(0,[z0,z17,z31,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z322,z6])],[(0,[z0,z90,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z323,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z324])]]

def bk0_10 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z325,z4,z5,z6]),(0,[z0,z2,z3,z40,z5,z6,z170])],[(0,[z98,z53,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z54,z153,z5,z6]),(1,[z0,z2,z3,z4,z326,z6])],[(0,[z0,z181,z119,z3,z4,z5,z6])],[(0,[z327,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z97,z101,z6])],[(0,[z0,z2,z3,z328,z4,z5,z6])],[(0,[z0,z2,z329,z3,z4,z5,z6])],[(0,[z98,z0,z3,z4,z5,z48,z6]),(0,[z115,z0,z2,z3,z54,z5,z6]),(0,[z0,z2,z3,z330,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z331]),(0,[z2,z3,z117,z4,z15,z5,z6])],[(0,[z118,z0,z2,z3,z54,z5,z6]),(0,[z0,z17,z3,z4,z5,z6,z332]),(0,[z0,z333,z2,z3,z4,z5,z6])],[(0,[z334,z0,z2,z3,z4,z5,z6]),(0,[z0,z119,z3,z4,z5,z107,z6]),(0,[z0,z2,z3,z4,z335,z5,z6]),(0,[z0,z2,z3,z4,z142,z71,z6])],[(0,[z336,z0,z2,z3,z4,z5,z6]),(0,[z0,z36,z272,z3,z4,z5,z6]),(0,[z0,z2,z3,z337,z4,z5,z6]),(0,[z0,z2,z3,z4,z338,z5,z6]),(0,[z0,z2,z3,z4,z5,z97,z6])],[(0,[z14,z0,z2,z3,z15,z5,z6]),(0,[z0,z119,z3,z4,z5,z48,z6]),(0,[z0,z339,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z340,z4,z5,z6])],[(0,[z0,z2,z3,z4,z341,z5,z6]),(0,[z0,z2,z3,z4,z163,z5,z6]),(0,[z0,z2,z3,z4,z142,z101,z6]),(0,[z0,z2,z3,z40,z142,z5,z6])],[(0,[z12,z0,z2,z3,z4,z179,z6]),(0,[z0,z2,z254,z3,z4,z5,z58])],[(0,[z0,z2,z3,z4,z342,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z343])],[(0,[z0,z2,z3,z344,z4,z5,z6]),(1,[z0,z2,z3,z4,z345,z6])]]

def bk0_11 : List (List (ℕ × List W)) :=
  [[(0,[z0,z346,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z347]),(1,[z0,z2,z3,z4,z287,z6]),(1,[z0,z2,z3,z4,z5,z135])],[(0,[z348,z0,z2,z3,z4,z5,z6]),(0,[z349,z0,z2,z3,z4,z5,z6])],[(0,[z0,z350,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z146,z5,z48,z6])],[(0,[z14,z0,z2,z3,z117,z5,z6]),(0,[z118,z0,z2,z3,z4,z142,z6]),(0,[z0,z2,z3,z351,z4,z5,z6])],[(0,[z115,z0,z2,z3,z40,z5,z6]),(0,[z352,z0,z2,z3,z4,z5,z6])],[(0,[z118,z0,z2,z3,z40,z5,z6]),(0,[z0,z181,z2,z3,z54,z5,z6]),(0,[z0,z2,z353,z3,z4,z5,z6]),(1,[z0,z139,z3,z4,z5,z6])],[(0,[z26,z0,z2,z3,z4,z5,z59]),(0,[z0,z2,z354,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z355,z5,z6])],[(0,[z0,z69,z73,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z356,z5,z6]),(0,[z0,z2,z3,z4,z28,z5,z27])],[(0,[z357,z0,z2,z3,z4,z5,z6]),(0,[z358,z0,z2,z3,z4,z5,z6]),(0,[z0,z17,z3,z4,z71,z5,z6]),(0,[z0,z2,z359,z3,z4,z5,z6]),(0,[z0,z2,z3,z360,z4,z5,z6])],[(0,[z82,z0,z2,z3,z54,z5,z6])],[],[(0,[z361,z0,z2,z3,z4,z5,z6]),(0,[z0,z17,z254,z3,z4,z5,z6]),(0,[z0,z362,z2,z3,z4,z5,z6]),(1,[z0,z363,z3,z4,z5,z6])],[(0,[z0,z2,z364,z3,z4,z5,z6]),(0,[z0,z2,z365,z3,z4,z5,z6]),(1,[z0,z366,z2,z3,z5,z6]),(1,[z0,z2,z3,z4,z367,z6])],[(0,[z115,z0,z2,z3,z368,z5,z6]),(0,[z0,z90,z2,z3,z4,z146,z6]),(0,[z0,z2,z3,z4,z369,z5,z6])],[(0,[z14,z0,z2,z3,z4,z5,z6]),(0,[z0,z370,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z57,z4,z163,z5]),(1,[z0,z3,z4,z48,z101,z6])],[(0,[z0,z2,z8,z3,z54,z5,z6])]]

def bk0_12 : List (List (ℕ × List W)) :=
  [[],[(0,[z0,z17,z3,z153,z4,z5,z6])],[(0,[z371,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z372,z3,z4,z5,z6])],[(0,[z0,z17,z17,z3,z4,z5,z6]),(0,[z0,z36,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z373,z4,z5,z6]),(1,[z0,z2,z3,z215,z5,z6])],[(0,[z0,z374,z2,z3,z4,z5,z6]),(0,[z0,z363,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z375])],[(0,[z376,z0,z2,z3,z4,z5,z6]),(0,[z0,z377,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z71,z48,z6])],[(0,[z0,z378,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z379,z4,z5,z6]),(0,[z0,z2,z3,z380,z4,z5,z6])],[(0,[z82,z0,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z381,z57,z5,z6]),(0,[z0,z2,z3,z152,z54,z5,z6])],[],[(0,[z53,z2,z66,z3,z4,z5,z6]),(0,[z0,z17,z3,z54,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z382,z6]),(0,[z0,z2,z3,z40,z231,z5,z6]),(0,[z0,z2,z3,z40,z156,z5,z6])],[],[],[(0,[z0,z2,z8,z3,z40,z5,z6]),(0,[z0,z2,z3,z383,z4,z5,z6]),(0,[z0,z66,z3,z4,z5,z48,z6]),(1,[z0,z2,z3,z4,z83,z6])],[(0,[z384,z0,z2,z3,z4,z5,z6]),(0,[z0,z69,z36,z2,z3,z5,z6]),(0,[z0,z89,z2,z3,z57,z4,z5]),(0,[z0,z2,z3,z4,z28,z5,z6]),(0,[z0,z2,z3,z4,z385,z5,z6]),(1,[z0,z2,z3,z385,z5,z6])],[(0,[z0,z2,z3,z386,z40,z5,z6])]]

def bk0_13 : List (List (ℕ × List W)) :=
  [[(0,[z50,z53,z2,z3,z4,z5,z6]),(0,[z0,z387,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z388,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z107,z60])],[(0,[z0,z389,z2,z3,z4,z5,z6]),(0,[z0,z2,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z390,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z391,z6]),(0,[z0,z2,z3,z4,z5,z392,z6]),(1,[z0,z2,z3,z4,z5,z393])],[(0,[z0,z2,z3,z4,z43,z5,z6]),(0,[z0,z2,z3,z4,z394,z5,z6])],[(0,[z0,z36,z2,z3,z4,z48,z6]),(0,[z0,z2,z3,z54,z71,z5,z6]),(0,[z0,z2,z3,z395,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z396,z6]),(1,[z0,z2,z3,z323,z5,z6])],[(0,[z124,z0,z2,z3,z397,z5,z6]),(0,[z7,z0,z17,z3,z4,z5,z6]),(0,[z0,z89,z3,z4,z5,z48,z6]),(0,[z0,z398,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z55,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z61])],[(0,[z0,z399,z2,z3,z4,z5,z6]),(0,[z0,z2,z66,z3,z4,z5,z6]),(0,[z0,z2,z3,z152,z40,z5,z6]),(0,[z0,z2,z3,z4,z5,z400,z6]),(1,[z0,z401,z3,z4,z5,z6])],[(0,[z402,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z71,z97,z6]),(0,[z0,z2,z3,z4,z5,z403,z6])],[(0,[z14,z0,z2,z3,z4,z5,z223]),(0,[z0,z2,z3,z4,z5,z60,z6])],[(0,[z26,z0,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z4,z5,z404,z6])],[(0,[z405,z0,z2,z3,z4,z5,z6]),(0,[z0,z406,z2,z3,z4,z5,z6]),(0,[z0,z2,z157,z3,z4,z71,z6]),(1,[z114,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z314,z5,z6])],[(0,[z0,z17,z3,z4,z5,z6,z27])],[(0,[z125,z0,z17,z3,z4,z5,z6]),(0,[z0,z17,z21,z3,z4,z5,z6]),(1,[z0,z2,z3,z264,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z407]),(1,[z0,z2,z3,z237,z5,z6])],[(0,[z218,z0,z3,z4,z5,z48,z6]),(0,[z0,z17,z3,z4,z5,z6,z62])],[(0,[z0,z408,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z409,z6]),(0,[z0,z2,z3,z4,z5,z6,z410]),(0,[z0,z2,z3,z15,z5,z6,z62]),(0,[z0,z157,z3,z4,z5,z48,z6])],[(0,[z99,z0,z36,z2,z3,z5,z6]),(0,[z411,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z412,z4,z5,z6])]]

def bk0_14 : List (List (ℕ × List W)) :=
  [[(0,[z124,z0,z2,z3,z40,z5,z6]),(0,[z53,z2,z3,z4,z5,z97,z6]),(0,[z0,z17,z90,z3,z4,z5,z6]),(0,[z0,z17,z3,z413,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z414]),(1,[z0,z415,z3,z4,z5,z6])],[(0,[z416,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z15,z5,z48,z6])],[(0,[z417,z0,z2,z3,z4,z5,z6]),(0,[z0,z275,z2,z3,z4,z5,z6]),(0,[z0,z418,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z57,z4,z5,z6]),(0,[z0,z3,z4,z163,z5,z48,z6]),(1,[z0,z3,z4,z97,z48,z6])],[(0,[z14,z0,z2,z3,z156,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z58])],[(0,[z0,z2,z3,z4,z296,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z419]),(0,[z0,z3,z45,z4,z5,z48,z6]),(1,[z0,z2,z3,z296,z5,z6])],[(0,[z115,z0,z2,z4,z5,z101,z6]),(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z420,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z421])],[],[(0,[z0,z2,z3,z4,z422,z5,z6]),(0,[z0,z3,z4,z385,z5,z48,z6])],[(0,[z0,z423,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z117,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z424,z6]),(1,[z0,z2,z3,z4,z5,z256])],[(0,[z115,z0,z2,z3,z425,z5,z6]),(0,[z0,z426,z2,z3,z4,z5,z6])],[(0,[z427,z0,z2,z3,z4,z5,z6]),(0,[z0,z144,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z142,z48,z6])],[(0,[z0,z69,z3,z55,z4,z5,z6]),(1,[z0,z17,z3,z4,z5,z6])],[(0,[z12,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z428,z6]),(0,[z0,z3,z4,z5,z48,z6,z429])],[(0,[z0,z2,z3,z430,z54,z5,z6])],[(0,[z0,z431,z2,z3,z4,z5,z6]),(0,[z0,z2,z68,z3,z4,z5,z6]),(0,[z0,z2,z432,z3,z4,z5,z6])]]

def bk0_15 : List (List (ℕ × List W)) :=
  [[(0,[z433,z0,z2,z3,z4,z5,z6]),(0,[z0,z241,z2,z3,z4,z5,z6]),(0,[z0,z415,z3,z4,z156,z5,z6]),(0,[z0,z2,z434,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z435,z6])],[(0,[z98,z0,z2,z148,z4,z5,z6]),(0,[z0,z17,z3,z4,z5,z101,z6]),(0,[z0,z36,z2,z3,z95,z5,z6]),(0,[z0,z2,z3,z436,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z75,z6]),(0,[z0,z2,z3,z103,z5,z6,z27]),(0,[z0,z2,z4,z71,z5,z101,z6])],[(0,[z124,z0,z437,z3,z4,z5,z6]),(0,[z0,z69,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z438,z4,z5,z6]),(0,[z0,z2,z3,z4,z439,z5,z6])],[(0,[z0,z73,z3,z4,z5,z48,z6]),(0,[z0,z21,z2,z3,z54,z5,z6])],[(0,[z0,z366,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z54,z5,z6,z27])],[(0,[z440,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z158,z4,z5,z6])],[(0,[z441,z0,z2,z3,z4,z5,z6]),(0,[z0,z251,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z442,z6])],[(0,[z0,z2,z3,z54,z5,z6,z62]),(0,[z0,z2,z3,z4,z443,z5,z6])],[(0,[z98,z0,z2,z3,z4,z5,z41]),(0,[z0,z2,z3,z444,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z445])],[(0,[z0,z446,z2,z3,z4,z5,z6])],[(0,[z447,z0,z3,z4,z5,z48,z6])],[(0,[z0,z2,z3,z4,z5,z59,z58]),(1,[z0,z3,z44,z4,z5,z6])],[(0,[z0,z2,z3,z40,z5,z107,z6])],[(0,[z124,z0,z2,z254,z4,z5,z6]),(0,[z47,z0,z17,z3,z4,z5,z6]),(0,[z99,z0,z2,z3,z154,z5,z6])],[(0,[z0,z2,z3,z40,z5,z48,z6])]]

def bk0_16 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z57,z4,z146,z6])],[(0,[z0,z2,z3,z448,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z449])],[(0,[z450,z0,z2,z3,z4,z5,z6]),(0,[z451,z0,z2,z3,z4,z5,z6]),(0,[z0,z452,z2,z3,z4,z5,z6]),(0,[z0,z21,z2,z3,z40,z5,z6]),(0,[z0,z2,z288,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z60,z27]),(0,[z0,z3,z154,z4,z5,z48,z6])],[(0,[z99,z0,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z4,z317,z5,z6]),(0,[z0,z2,z3,z4,z5,z453,z6])],[(0,[z454,z0,z3,z45,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z455,z6])],[(0,[z0,z456,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z457,z4,z5,z6]),(0,[z0,z2,z3,z4,z458,z5,z6])],[(0,[z115,z0,z2,z3,z4,z5,z409]),(0,[z0,z17,z8,z3,z4,z5,z6]),(0,[z0,z459,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z256,z6])],[(0,[z0,z460,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z95,z15,z5,z6])],[(0,[z125,z0,z2,z3,z4,z5,z59])],[(0,[z280,z0,z2,z3,z4,z5,z6]),(0,[z0,z17,z3,z4,z5,z59,z6]),(0,[z0,z2,z461,z3,z4,z5,z6]),(1,[z0,z17,z3,z4,z146,z6])],[(0,[z462,z0,z2,z3,z4,z5,z6]),(0,[z0,z31,z2,z3,z54,z5,z6]),(0,[z0,z2,z3,z463,z4,z5,z6])],[(0,[z0,z2,z3,z4,z464,z5,z6]),(0,[z0,z2,z3,z4,z465,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z466])],[(0,[z26,z0,z2,z3,z54,z5,z6]),(0,[z0,z2,z3,z54,z5,z101,z6]),(0,[z0,z2,z3,z4,z5,z6,z467]),(0,[z0,z2,z3,z4,z5,z6,z468])],[(0,[z469,z0,z2,z3,z4,z5,z6]),(0,[z50,z0,z110,z3,z4,z5,z6]),(1,[z0,z370,z3,z4,z5,z6])],[(0,[z0,z17,z3,z152,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z112])]]

def bk0_17 : List (List (ℕ × List W)) :=
  [[(0,[z47,z0,z363,z3,z4,z5,z6]),(0,[z0,z2,z3,z242,z4,z5,z6]),(0,[z0,z2,z3,z470,z4,z5,z6]),(0,[z0,z2,z3,z40,z5,z97,z6])],[(0,[z0,z2,z3,z153,z4,z48,z6]),(0,[z0,z2,z3,z4,z5,z6,z233])],[(0,[z50,z0,z66,z3,z4,z5,z6]),(0,[z0,z2,z3,z471,z4,z5,z6]),(0,[z0,z2,z3,z472,z4,z5,z6])],[(0,[z0,z141,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z473,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z179,z6]),(0,[z0,z2,z3,z40,z163,z5,z6]),(0,[z0,z3,z55,z4,z43,z5,z6]),(0,[z2,z3,z45,z4,z5,z6,z27])],[],[(0,[z82,z0,z2,z152,z4,z5,z6]),(0,[z124,z0,z2,z3,z54,z5,z6])],[(0,[z474,z0,z2,z3,z4,z5,z6]),(0,[z0,z127,z2,z3,z54,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z475])],[(0,[z118,z2,z3,z4,z142,z5,z6]),(0,[z0,z2,z208,z3,z4,z5,z6]),(0,[z0,z2,z3,z476,z4,z5,z6]),(0,[z0,z2,z3,z84,z4,z5,z6]),(0,[z0,z2,z3,z4,z163,z5,z72]),(0,[z0,z2,z3,z4,z5,z190,z6])],[(0,[z477,z0,z2,z3,z4,z5,z6]),(0,[z50,z0,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z4,z5,z6,z478])],[(0,[z0,z17,z3,z4,z5,z6,z72]),(0,[z0,z119,z2,z3,z4,z243,z6]),(0,[z0,z479,z2,z3,z4,z5,z6]),(0,[z0,z31,z2,z3,z40,z5,z6])],[(0,[z125,z2,z3,z4,z5,z59,z6]),(0,[z0,z2,z3,z4,z5,z6,z480])],[(0,[z0,z2,z3,z481,z4,z5,z6])],[(0,[z349,z0,z17,z3,z4,z5,z6]),(0,[z53,z0,z2,z3,z4,z5,z6]),(0,[z0,z482,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z95,z4,z5,z6]),(0,[z0,z2,z3,z57,z4,z5,z60]),(0,[z0,z2,z3,z425,z4,z5,z6]),(0,[z0,z3,z55,z4,z5,z48,z6])],[(0,[z0,z2,z3,z4,z5,z6,z483])],[(0,[z0,z36,z2,z3,z5,z6,z37])],[(0,[z114,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z484,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z485,z6])]]

def bk0_18 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z0,z2,z157,z3,z4,z101,z6]),(0,[z0,z2,z3,z4,z5,z6,z486])],[],[(0,[z0,z3,z4,z5,z59,z6,z324])],[(0,[z487,z0,z2,z3,z4,z5,z6]),(0,[z0,z488,z2,z3,z4,z5,z6]),(0,[z0,z2,z110,z3,z323,z5,z6]),(0,[z0,z2,z3,z489,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z490,z6])],[(0,[z0,z2,z3,z4,z491,z5,z6])],[(0,[z0,z2,z3,z54,z5,z59,z6]),(0,[z0,z2,z3,z4,z492,z5,z6])],[(0,[z82,z292,z2,z3,z4,z5,z6]),(0,[z98,z2,z3,z45,z4,z5,z6]),(0,[z0,z493,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z494,z5,z6])],[(0,[z495,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z496,z4,z5,z6])],[(0,[z0,z17,z89,z3,z4,z5,z6]),(0,[z0,z2,z157,z4,z71,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z497]),(0,[z0,z2,z3,z28,z5,z6,z62]),(0,[z0,z3,z95,z4,z5,z48,z6])],[(0,[z14,z0,z17,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z123,z6])],[(0,[z118,z53,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z498,z4,z5,z6]),(0,[z0,z2,z3,z4,z499,z5,z6]),(0,[z0,z2,z3,z4,z500,z5,z6]),(0,[z0,z2,z3,z4,z123,z5,z6]),(0,[z0,z2,z3,z4,z5,z13,z58])],[(0,[z501,z0,z2,z3,z4,z5,z6]),(0,[z53,z0,z2,z45,z4,z5,z6]),(0,[z0,z2,z3,z502,z4,z5,z6]),(0,[z0,z3,z4,z28,z5,z48,z6])],[(0,[z0,z503,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z504]),(1,[z0,z70,z3,z4,z5,z6])],[(0,[z12,z0,z21,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z48,z6,z62])],[(0,[z98,z0,z2,z3,z4,z5,z6]),(0,[z115,z0,z3,z4,z5,z48,z6]),(0,[z0,z73,z3,z4,z43,z5,z6]),(0,[z0,z2,z203,z3,z4,z5,z6])],[(0,[z118,z0,z3,z4,z5,z48,z6]),(0,[z0,z374,z17,z3,z4,z5,z6]),(0,[z0,z2,z3,z54,z505,z5,z6]),(0,[z0,z2,z3,z506,z4,z5,z6]),(0,[z0,z2,z3,z4,z284,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z507])]]

def bk0_19 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z237,z4,z5,z6]),(1,[z0,z2,z3,z397,z5,z6])],[(0,[z0,z31,z3,z4,z5,z6,z13])],[(0,[z98,z0,z2,z3,z182,z5,z6]),(0,[z0,z119,z2,z3,z4,z5,z6]),(1,[z0,z452,z3,z4,z5,z6])],[(0,[z98,z0,z2,z3,z184,z5,z6]),(0,[z0,z2,z3,z508,z4,z5,z6]),(0,[z0,z2,z3,z509,z4,z5,z6])],[(0,[z0,z510,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z511,z4,z5,z6]),(0,[z0,z2,z3,z54,z5,z6,z72])],[(0,[z0,z17,z119,z3,z4,z5,z6]),(0,[z0,z2,z512,z3,z4,z5,z6]),(0,[z0,z2,z3,z40,z28,z5,z6]),(0,[z0,z110,z3,z152,z4,z5,z6])],[(0,[z82,z0,z2,z3,z513,z5,z6]),(0,[z53,z2,z148,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z34,z6])],[(0,[z0,z2,z3,z514,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z515,z6])],[(0,[z0,z2,z3,z516,z4,z5,z6]),(0,[z0,z2,z3,z4,z517,z5,z6]),(0,[z0,z2,z3,z4,z146,z5,z6]),(1,[z0,z2,z3,z517,z5,z6])],[(0,[z0,z2,z224,z3,z4,z5,z6]),(0,[z0,z2,z3,z40,z43,z5,z6]),(1,[z0,z3,z385,z5,z48,z6])],[],[(0,[z0,z2,z3,z518,z4,z5,z6])],[(0,[z0,z2,z3,z4,z40,z5,z6]),(0,[z0,z2,z3,z4,z519,z5,z6]),(0,[z0,z2,z3,z4,z5,z520,z6]),(1,[z0,z2,z3,z40,z5,z6])],[(0,[z0,z181,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z521,z4,z5,z6])],[(0,[z0,z2,z3,z40,z5,z60,z6])],[]]

def bk0_20 : List (List (ℕ × List W)) :=
  [[(0,[z522,z0,z2,z3,z4,z5,z6]),(0,[z523,z0,z2,z3,z4,z5,z6]),(0,[z0,z524,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z525,z5,z6])],[(0,[z82,z0,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z95,z156,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z41])],[(0,[z0,z213,z2,z3,z54,z5,z6]),(0,[z0,z2,z148,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z60,z72])],[(0,[z0,z2,z3,z4,z5,z526,z6])],[(0,[z0,z2,z3,z4,z5,z6,z527])],[(0,[z0,z2,z3,z4,z368,z5,z6]),(0,[z0,z2,z3,z4,z528,z5,z6])],[(0,[z0,z529,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z530])],[(0,[z0,z2,z3,z40,z5,z6,z414])],[(0,[z0,z17,z2,z3,z54,z5,z6]),(0,[z0,z2,z3,z4,z5,z531,z6])],[(0,[z0,z17,z3,z4,z5,z6,z37]),(0,[z0,z2,z3,z4,z5,z6,z532]),(0,[z0,z2,z3,z4,z5,z6,z533])],[(0,[z534,z0,z2,z3,z4,z5,z6]),(0,[z124,z0,z2,z3,z4,z535,z6]),(0,[z0,z2,z3,z4,z5,z6,z536]),(0,[z0,z2,z3,z40,z5,z6,z58])],[(0,[z0,z36,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z537,z4,z5,z6]),(0,[z0,z2,z3,z95,z4,z5,z62])],[(0,[z0,z538,z2,z3,z4,z5,z6]),(0,[z0,z89,z2,z3,z57,z4,z6]),(1,[z0,z3,z54,z5,z48,z6])],[(0,[z539,z0,z2,z3,z4,z5,z6]),(0,[z159,z0,z2,z3,z4,z5,z6])],[(0,[z14,z0,z2,z3,z28,z5,z6]),(0,[z0,z2,z540,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z247,z6])],[(0,[z124,z0,z2,z3,z4,z5,z58]),(1,[z0,z437,z3,z4,z5,z6])]]

def bk0_21 : List (List (ℕ × List W)) :=
  [[(0,[z118,z0,z2,z3,z4,z97,z6]),(0,[z0,z2,z3,z541,z4,z5,z6])],[(0,[z0,z542,z2,z3,z4,z5,z6])],[(0,[z0,z543,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z163,z48,z6])],[(0,[z115,z108,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z5,z6])],[(0,[z0,z2,z3,z95,z117,z5,z6]),(0,[z0,z2,z3,z154,z40,z5,z6]),(0,[z0,z2,z3,z4,z5,z60,z13])],[(0,[z50,z2,z3,z45,z4,z5,z6]),(0,[z0,z544,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z545,z5,z6]),(0,[z0,z3,z4,z163,z5,z247,z6])],[(0,[z0,z17,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z214,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z546])],[],[(0,[z12,z0,z17,z3,z4,z5,z6])],[(0,[z7,z0,z2,z3,z54,z5,z6]),(0,[z0,z139,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z547,z6])],[(0,[z548,z0,z2,z3,z4,z5,z6]),(0,[z0,z90,z2,z3,z40,z5,z6]),(0,[z0,z3,z4,z5,z48,z59,z6])],[],[(0,[z0,z89,z2,z3,z4,z5,z6]),(0,[z0,z2,z549,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z550,z5,z6]),(0,[z0,z2,z3,z4,z551,z5,z6])],[(0,[z552,z0,z2,z3,z4,z5,z6]),(0,[z50,z0,z2,z3,z4,z5,z6]),(0,[z0,z69,z2,z3,z156,z5,z6]),(0,[z0,z3,z4,z142,z5,z48,z6])],[],[(0,[z12,z0,z2,z3,z4,z287,z6]),(0,[z225,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z553,z4,z5,z6])]]

def bk0_22 : List (List (ℕ × List W)) :=
  [[(0,[z125,z0,z2,z3,z54,z5,z6]),(0,[z0,z119,z2,z3,z4,z345,z6]),(0,[z0,z366,z2,z3,z5,z97,z6])],[(0,[z0,z2,z3,z4,z554,z5,z6]),(0,[z0,z3,z204,z4,z5,z48,z6])],[(0,[z0,z17,z3,z4,z15,z5,z6]),(0,[z0,z452,z3,z4,z71,z5,z6]),(0,[z0,z2,z3,z555,z4,z5,z6]),(0,[z0,z3,z4,z5,z48,z6,z556])],[(0,[z0,z2,z3,z557,z4,z5,z6])],[(0,[z0,z2,z3,z54,z5,z6,z37])],[(0,[z218,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z558,z5,z6]),(0,[z0,z2,z3,z4,z5,z143,z6]),(0,[z0,z2,z3,z4,z5,z6,z429])],[(0,[z0,z2,z157,z3,z54,z5,z6]),(0,[z0,z3,z4,z5,z97,z48,z6])],[(0,[z7,z0,z2,z3,z40,z5,z6]),(0,[z0,z31,z2,z152,z4,z5,z6]),(0,[z0,z2,z3,z4,z28,z5,z59])],[(0,[z0,z559,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z22,z5,z6,z27])],[(0,[z560,z0,z2,z3,z4,z5,z6]),(0,[z0,z36,z2,z3,z4,z146,z6]),(0,[z0,z2,z561,z3,z4,z5,z6])],[],[(0,[z562,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z563,z3,z4,z5,z6]),(0,[z0,z2,z3,z153,z156,z5,z6])],[(0,[z118,z2,z3,z45,z4,z5,z6]),(1,[z0,z2,z3,z149,z5,z6])],[(0,[z0,z2,z564,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z48,z6,z27])],[(0,[z125,z0,z2,z3,z40,z5,z6]),(0,[z0,z17,z3,z4,z5,z6,z13])],[(0,[z7,z0,z2,z54,z4,z5,z6]),(0,[z0,z2,z565,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z332])]]

def bk0_23 : List (List (ℕ × List W)) :=
  [[(0,[z115,z0,z262,z3,z4,z5,z6]),(0,[z0,z370,z3,z4,z5,z59,z6]),(0,[z0,z2,z3,z4,z566,z5,z6])],[(0,[z0,z2,z567,z3,z4,z5,z6]),(0,[z0,z2,z3,z568,z4,z5,z6]),(1,[z0,z2,z3,z54,z5,z6])],[(0,[z0,z2,z3,z283,z54,z5,z6])],[(0,[z0,z2,z3,z4,z5,z326,z6]),(0,[z0,z2,z3,z4,z5,z569,z6])],[(0,[z0,z2,z157,z3,z40,z5,z6])],[(0,[z570,z0,z2,z3,z4,z5,z6]),(1,[z0,z141,z3,z5,z48,z6]),(1,[z0,z2,z3,z4,z5,z311])],[(0,[z0,z2,z571,z3,z4,z5,z6]),(0,[z0,z2,z3,z381,z4,z5,z6]),(0,[z0,z2,z3,z4,z572,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z573])],[(0,[z0,z3,z4,z369,z5,z48,z6])],[(0,[z574,z0,z2,z3,z4,z5,z6]),(0,[z99,z0,z2,z3,z15,z5,z6]),(0,[z0,z119,z31,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z575])],[(0,[z576,z0,z2,z3,z4,z5,z6])],[],[(0,[z0,z69,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z3,z54,z5,z6])],[(0,[z0,z73,z2,z3,z4,z5,z6]),(0,[z0,z21,z3,z4,z5,z48,z6]),(0,[z0,z3,z4,z43,z5,z48,z6])],[(0,[z0,z17,z3,z4,z142,z5,z6]),(0,[z0,z248,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z54,z15,z5,z6]),(0,[z0,z2,z3,z577,z4,z5,z6]),(0,[z0,z2,z3,z4,z163,z6,z72])],[],[]]

def bk0_24 : List (List (ℕ × List W)) :=
  [[(0,[z98,z0,z2,z45,z4,z5,z6]),(0,[z0,z578,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z579,z5,z6]),(0,[z0,z2,z3,z4,z71,z5,z6])],[(0,[z99,z0,z2,z3,z117,z5,z6]),(0,[z0,z2,z3,z4,z5,z345,z6]),(0,[z0,z2,z3,z4,z5,z6,z324]),(0,[z0,z2,z3,z4,z97,z48,z6]),(0,[z0,z3,z4,z5,z297,z48,z6])],[(0,[z580,z0,z2,z3,z4,z5,z6])],[(0,[z47,z0,z2,z3,z54,z5,z6]),(0,[z447,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z254,z3,z4,z5,z6])],[(0,[z0,z17,z3,z201,z4,z5,z6])],[(0,[z115,z0,z68,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z48,z101,z6])],[(0,[z0,z2,z3,z54,z117,z5,z6]),(0,[z0,z2,z3,z4,z5,z581,z6])],[(0,[z53,z0,z17,z3,z4,z5,z6]),(0,[z0,z2,z3,z397,z4,z5,z6]),(0,[z0,z3,z4,z156,z5,z319,z6])],[(0,[z582,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z368,z5,z6]),(1,[z0,z3,z57,z4,z48,z6])],[(0,[z98,z0,z2,z3,z4,z317,z6]),(0,[z583,z0,z2,z3,z4,z5,z6]),(0,[z0,z31,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z3,z40,z5,z6]),(0,[z0,z2,z3,z154,z54,z5,z6]),(0,[z0,z2,z3,z54,z5,z6,z13]),(0,[z0,z2,z3,z153,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z584,z6]),(0,[z0,z254,z3,z4,z5,z48,z6])],[(0,[z0,z585,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z45,z54,z5,z6])],[(0,[z454,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z586,z4,z5,z6]),(0,[z0,z2,z3,z40,z491,z5,z6])],[(0,[z99,z0,z2,z3,z4,z5,z6]),(0,[z0,z587,z2,z3,z4,z5,z6]),(0,[z0,z2,z110,z3,z40,z5,z6]),(0,[z0,z2,z3,z4,z588,z5,z6]),(0,[z0,z2,z3,z4,z5,z589,z6]),(0,[z0,z2,z3,z4,z5,z6,z590]),(0,[z0,z2,z3,z4,z5,z6,z591])],[],[(0,[z0,z2,z3,z4,z5,z367,z6])],[(0,[z47,z0,z2,z3,z4,z142,z6]),(0,[z592,z0,z2,z3,z4,z5,z6]),(0,[z0,z90,z2,z3,z54,z5,z6]),(0,[z0,z2,z3,z55,z40,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z223]),(1,[z0,z2,z3,z381,z5,z6]),(1,[z0,z2,z3,z4,z5,z409])]]

def bk0_25 : List (List (ℕ × List W)) :=
  [[(0,[z99,z2,z3,z117,z4,z5,z6]),(0,[z0,z593,z2,z3,z4,z5,z6]),(0,[z0,z2,z66,z3,z40,z5,z6]),(0,[z0,z2,z3,z594,z4,z5,z6])],[(0,[z595,z0,z2,z3,z4,z5,z6]),(0,[z47,z0,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z54,z4,z5,z6])],[(0,[z0,z2,z3,z4,z146,z163,z6])],[(0,[z0,z31,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z4,z83,z5,z6])],[(0,[z82,z0,z2,z110,z4,z5,z6])],[(0,[z26,z0,z3,z4,z5,z48,z6]),(0,[z2,z148,z3,z45,z4,z5,z6])],[(0,[z596,z0,z2,z3,z4,z5,z6]),(0,[z47,z118,z2,z3,z4,z5,z6]),(0,[z294,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z597,z4,z5,z6])],[(0,[z598,z0,z2,z3,z4,z5,z6]),(0,[z0,z17,z3,z4,z5,z228,z6])],[(0,[z0,z16,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z45,z40,z5,z6]),(0,[z0,z2,z3,z54,z142,z5,z6])],[(0,[z98,z0,z17,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z27,z58])],[(0,[z0,z2,z3,z599,z4,z5,z6])],[(0,[z0,z17,z3,z4,z156,z5,z6]),(0,[z0,z69,z2,z3,z4,z326,z6]),(0,[z0,z141,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z146,z71,z6])],[(0,[z30,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z600,z3,z4,z5,z6])],[(0,[z124,z0,z3,z4,z5,z48,z6]),(0,[z0,z2,z601,z3,z4,z5,z6])],[(0,[z0,z602,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z154,z4,z28,z5])],[(0,[z0,z2,z3,z304,z4,z5,z6]),(0,[z0,z2,z3,z603,z4,z5,z6]),(0,[z0,z2,z3,z4,z146,z101,z6]),(0,[z0,z2,z3,z4,z5,z604,z6]),(0,[z0,z2,z3,z4,z5,z605,z6]),(0,[z0,z2,z3,z40,z146,z5,z6])]]

def bk0_26 : List (List (ℕ × List W)) :=
  [[(0,[z125,z53,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z606,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z607]),(0,[z0,z2,z3,z4,z48,z101,z6])],[(0,[z608,z0,z2,z3,z4,z5,z6]),(0,[z0,z73,z2,z3,z156,z5,z6])],[(0,[z609,z0,z2,z3,z4,z5,z6]),(0,[z0,z610,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z27])],[(0,[z0,z2,z3,z40,z40,z5,z6])],[(0,[z352,z0,z2,z3,z54,z5,z6]),(0,[z0,z2,z611,z3,z4,z5,z6])],[(0,[z612,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z62]),(1,[z50,z21,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z535,z6])],[(0,[z613,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z153,z4,z146,z6]),(0,[z0,z2,z54,z4,z40,z5,z6]),(1,[z0,z17,z3,z40,z5,z6])],[(0,[z0,z2,z3,z413,z4,z5,z6])],[(0,[z0,z614,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z615,z5,z6]),(0,[z0,z3,z54,z4,z5,z48,z6])],[(0,[z0,z2,z3,z4,z5,z616,z6])],[(0,[z617,z0,z2,z3,z4,z5,z6]),(0,[z0,z230,z3,z4,z163,z5,z6]),(0,[z0,z2,z3,z4,z513,z5,z6]),(1,[z0,z2,z3,z513,z5,z6])],[(0,[z98,z0,z2,z3,z4,z367,z6]),(0,[z0,z618,z2,z3,z4,z5,z6]),(0,[z0,z619,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z95,z28,z5,z6]),(0,[z0,z3,z4,z5,z48,z6,z72])],[(0,[z164,z0,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z620,z4,z5,z6])],[(0,[z14,z0,z2,z3,z54,z5,z6]),(0,[z0,z17,z157,z3,z4,z5,z6]),(0,[z0,z2,z621,z3,z4,z5,z6])],[(0,[z115,z0,z2,z157,z4,z5,z6])]]

def bk0_27 : List (List (ℕ × List W)) :=
  [[(0,[z0,z350,z2,z3,z40,z5,z6]),(0,[z0,z89,z401,z3,z4,z5,z6])],[(0,[z99,z0,z2,z3,z156,z5,z6]),(0,[z0,z622,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z623]),(0,[z0,z2,z3,z4,z5,z6,z624]),(0,[z2,z66,z3,z45,z4,z5,z6])],[(0,[z14,z0,z2,z3,z4,z5,z311]),(0,[z0,z625,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z626,z6]),(0,[z0,z2,z3,z4,z5,z6,z627])],[(0,[z115,z275,z2,z3,z4,z5,z6]),(0,[z0,z2,z628,z3,z4,z5,z6]),(0,[z0,z2,z3,z57,z4,z6,z72])],[],[(1,[z0,z2,z3,z425,z5,z6])],[(0,[z115,z0,z2,z3,z4,z5,z6]),(0,[z0,z89,z2,z3,z4,z163,z6]),(0,[z0,z2,z3,z54,z156,z5,z6])],[(0,[z118,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z401,z3,z4,z5,z6]),(0,[z0,z2,z3,z629,z4,z5,z6])],[(0,[z0,z2,z630,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z631]),(1,[z0,z3,z4,z5,z319,z6])],[(0,[z82,z12,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z632,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z6])],[(0,[z0,z2,z3,z4,z5,z101,z6])],[(0,[z0,z305,z2,z3,z4,z5,z6])],[(0,[z14,z0,z2,z3,z40,z5,z6]),(0,[z0,z437,z2,z3,z4,z5,z6])],[(0,[z633,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z254,z3,z4,z5,z60]),(0,[z0,z2,z3,z154,z5,z6,z62])],[(0,[z0,z2,z3,z4,z5,z59,z62]),(0,[z0,z3,z438,z4,z5,z48,z6]),(0,[z0,z3,z4,z5,z48,z6,z13])],[(0,[z634,z0,z2,z3,z4,z5,z6]),(0,[z0,z89,z2,z3,z4,z71,z6])]]

def bk0_28 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z635,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z107,z58])],[(0,[z98,z0,z2,z3,z4,z5,z393]),(0,[z0,z389,z2,z3,z54,z5,z6]),(0,[z0,z2,z110,z3,z54,z5,z6])],[(0,[z0,z636,z2,z3,z4,z5,z6]),(0,[z0,z637,z2,z3,z4,z5,z6])],[(0,[z0,z89,z2,z3,z4,z101,z6]),(0,[z0,z638,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z639,z4,z5,z6]),(0,[z0,z2,z3,z40,z551,z5,z6])],[(0,[z0,z2,z254,z3,z277,z5,z6]),(0,[z0,z2,z3,z379,z40,z5,z6])],[(0,[z0,z181,z2,z3,z4,z5,z6]),(0,[z0,z2,z66,z3,z54,z5,z6]),(0,[z0,z2,z3,z4,z640,z5,z6]),(0,[z0,z2,z3,z156,z5,z6,z62])],[(0,[z641,z0,z2,z3,z4,z5,z6]),(0,[z0,z17,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z463,z40,z5,z6]),(0,[z0,z3,z4,z5,z642,z48,z6])],[(0,[z0,z89,z2,z3,z4,z5,z72]),(0,[z0,z2,z3,z4,z46,z5,z6])],[(0,[z552,z0,z17,z3,z4,z5,z6]),(0,[z643,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z156,z5,z48,z6])],[(0,[z82,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z644,z6]),(0,[z0,z66,z3,z152,z4,z5,z6])],[(0,[z12,z0,z119,z3,z4,z5,z6]),(0,[z0,z2,z645,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z646,z5,z6])],[(0,[z0,z200,z2,z3,z4,z5,z6])],[(0,[z647,z0,z2,z3,z4,z5,z6]),(0,[z82,z0,z31,z3,z4,z5,z6]),(0,[z648,z0,z2,z3,z4,z5,z6]),(0,[z0,z17,z69,z3,z4,z5,z6]),(0,[z0,z69,z2,z3,z43,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z649])],[(0,[z0,z650,z2,z3,z4,z5,z6]),(0,[z0,z200,z36,z3,z4,z5,z6]),(0,[z0,z2,z651,z3,z4,z5,z6]),(0,[z0,z2,z3,z652,z4,z5,z6]),(0,[z0,z2,z3,z4,z142,z48,z6])],[(0,[z0,z17,z3,z4,z5,z107,z6]),(0,[z0,z2,z3,z653,z4,z5,z6]),(1,[z454,z0,z3,z4,z5,z6])],[(0,[z0,z2,z8,z3,z4,z5,z6]),(0,[z0,z2,z254,z4,z5,z60,z6]),(0,[z0,z2,z3,z4,z111,z5,z6]),(1,[z0,z2,z3,z111,z5,z6])]]

def bk0_29 : List (List (ℕ × List W)) :=
  [[(0,[z218,z0,z17,z3,z4,z5,z6]),(0,[z0,z17,z3,z4,z5,z48,z6]),(0,[z0,z654,z2,z3,z4,z5,z6]),(0,[z0,z31,z66,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z655,z5,z6])],[(0,[z656,z0,z2,z3,z4,z5,z6]),(0,[z12,z50,z2,z3,z4,z5,z6]),(0,[z0,z17,z3,z154,z4,z5,z6]),(0,[z0,z2,z3,z386,z4,z5,z6])],[(0,[z0,z17,z3,z45,z4,z5,z6]),(0,[z0,z2,z3,z57,z54,z5,z6]),(0,[z0,z2,z3,z4,z5,z59,z6])],[(0,[z0,z657,z2,z3,z4,z5,z6])],[(0,[z658,z0,z2,z3,z4,z5,z6]),(0,[z0,z659,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z660,z4,z5,z6]),(0,[z0,z2,z3,z4,z661,z5,z6]),(0,[z0,z2,z3,z4,z5,z642,z6])],[(0,[z0,z2,z3,z4,z5,z662,z6])],[(0,[z0,z398,z2,z3,z4,z5,z6])],[(0,[z0,z17,z73,z3,z4,z5,z6]),(0,[z0,z663,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z152,z4,z5,z6]),(0,[z0,z2,z3,z149,z4,z5,z6]),(0,[z0,z2,z3,z664,z4,z5,z6])],[(0,[z0,z36,z73,z2,z3,z5,z6]),(0,[z0,z2,z3,z385,z5,z48,z6])],[(0,[z53,z2,z3,z4,z5,z6,z27]),(0,[z0,z251,z3,z4,z142,z5,z6])],[(0,[z665,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z535,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z556])],[(0,[z0,z666,z2,z3,z4,z5,z6]),(0,[z0,z2,z254,z3,z314,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z667])],[(0,[z193,z0,z2,z3,z4,z5,z6]),(0,[z0,z408,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z4,z505,z5,z6]),(0,[z0,z2,z3,z4,z668,z5,z6]),(0,[z0,z3,z4,z5,z48,z6,z37]),(1,[z0,z17,z3,z54,z5,z6])],[(0,[z12,z0,z2,z3,z54,z5,z6])],[(0,[z0,z2,z3,z44,z4,z5,z6]),(1,[z292,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z669]),(1,[z0,z272,z3,z4,z5,z6])]]

def bk0_30 : List (List (ℕ × List W)) :=
  [[(0,[z50,z0,z21,z3,z4,z5,z6]),(0,[z0,z17,z2,z3,z4,z48,z6]),(0,[z0,z2,z670,z3,z4,z5,z6]),(0,[z0,z2,z3,z57,z40,z5,z6]),(0,[z0,z2,z3,z4,z5,z671,z6])],[(0,[z7,z0,z3,z4,z5,z48,z6]),(0,[z0,z17,z3,z4,z338,z5,z6]),(0,[z0,z17,z3,z4,z5,z97,z6]),(0,[z0,z2,z3,z4,z5,z6,z72])],[(0,[z0,z2,z3,z436,z54,z5,z6])],[(0,[z0,z672,z2,z3,z4,z5,z6]),(0,[z0,z2,z673,z3,z4,z5,z6]),(0,[z0,z2,z3,z674,z4,z5,z6]),(0,[z0,z2,z3,z4,z675,z5,z6]),(0,[z0,z2,z3,z4,z5,z676,z6]),(1,[z0,z305,z3,z4,z5,z6])],[(0,[z207,z0,z2,z3,z4,z5,z6]),(0,[z0,z17,z3,z4,z163,z5,z6]),(0,[z0,z90,z2,z3,z4,z48,z6]),(0,[z0,z2,z3,z4,z5,z6,z677])],[(0,[z678,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z679,z5,z6])],[(0,[z0,z31,z2,z110,z4,z5,z6])],[(0,[z0,z2,z680,z3,z4,z5,z6]),(0,[z0,z2,z3,z117,z40,z5,z6]),(0,[z0,z2,z3,z40,z71,z5,z6])],[(0,[z125,z0,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z4,z5,z6,z135])],[(0,[z124,z0,z2,z3,z4,z190,z6]),(0,[z427,z0,z2,z3,z40,z5,z6]),(0,[z0,z119,z3,z152,z4,z5,z6]),(0,[z0,z2,z3,z54,z5,z107,z6]),(0,[z0,z2,z3,z681,z4,z5,z6])],[],[(0,[z12,z0,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z54,z5,z48,z6])],[(0,[z0,z2,z3,z4,z682,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z683])],[(0,[z0,z2,z684,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z685])],[],[(0,[z686,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z393,z6])]]

def bk0_31 : List (List (ℕ × List W)) :=
  [[(0,[z0,z415,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z687,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z688,z6]),(0,[z0,z2,z3,z4,z5,z6,z689])],[(0,[z690,z0,z2,z3,z4,z5,z6]),(0,[z0,z691,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z146,z142,z6])],[(0,[z0,z119,z2,z3,z4,z5,z13]),(0,[z0,z2,z692,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z693,z5,z6])],[(0,[z694,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z695,z4,z5,z6])],[(0,[z696,z0,z2,z3,z4,z5,z6]),(0,[z108,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z697,z4,z5,z6])],[(0,[z0,z141,z2,z3,z5,z48,z6])],[(0,[z0,z2,z3,z4,z5,z698,z6])],[(0,[z99,z0,z17,z3,z4,z5,z6])],[(0,[z0,z2,z699,z3,z4,z5,z6]),(0,[z0,z2,z3,z184,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z700,z6]),(1,[z0,z262,z3,z4,z5,z6])],[(0,[z0,z2,z148,z3,z517,z5,z6]),(0,[z0,z3,z4,z5,z48,z252,z6]),(1,[z0,z3,z4,z5,z48,z6])],[(0,[z701,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z158,z5,z6])],[(0,[z124,z0,z224,z3,z4,z5,z6]),(0,[z0,z17,z423,z3,z4,z5,z6]),(0,[z0,z119,z2,z3,z4,z5,z107]),(0,[z0,z702,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z54,z5,z97,z6])],[(0,[z0,z240,z2,z3,z4,z5,z6]),(0,[z0,z2,z148,z3,z40,z5,z6]),(0,[z0,z2,z3,z703,z4,z5,z6]),(0,[z0,z2,z3,z4,z704,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z705]),(1,[z0,z2,z3,z22,z5,z6])],[(0,[z0,z2,z3,z430,z4,z5,z6])],[(0,[z0,z2,z3,z54,z163,z5,z6]),(0,[z0,z2,z3,z706,z4,z5,z6])]]

def bk0 : List (List (List (ℕ × List W))) :=
  [bk0_0, bk0_1, bk0_2, bk0_3, bk0_4, bk0_5, bk0_6, bk0_7, bk0_8, bk0_9, bk0_10, bk0_11, bk0_12, bk0_13, bk0_14, bk0_15, bk0_16, bk0_17, bk0_18, bk0_19, bk0_20, bk0_21, bk0_22, bk0_23, bk0_24, bk0_25, bk0_26, bk0_27, bk0_28, bk0_29, bk0_30, bk0_31]

def bk1_0 : List (List (ℕ × List W)) :=
  [[(0,[z108,z2,z3,z40,z5,z6]),(0,[z0,z69,z3,z707,z5,z6]),(0,[z0,z708,z3,z4,z5,z6]),(0,[z0,z2,z3,z709,z5,z6]),(0,[z0,z2,z3,z710,z5,z6]),(0,[z0,z3,z4,z391,z48,z6])],[(0,[z711,z2,z3,z4,z5,z6])],[(0,[z0,z119,z3,z4,z179,z6]),(0,[z0,z31,z565,z4,z5,z6]),(0,[z0,z3,z4,z166,z48,z6])],[(0,[z0,z2,z3,z237,z5,z6])],[(0,[z0,z2,z3,z4,z712,z5]),(0,[z0,z2,z3,z4,z5,z713]),(0,[z0,z3,z714,z5,z48,z6])],[(0,[z0,z715,z3,z4,z5,z6]),(0,[z0,z716,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z717,z6])],[(0,[z0,z718,z3,z4,z5,z6])],[(0,[z0,z17,z3,z4,z632,z6]),(0,[z719,z2,z3,z4,z5,z6])],[(0,[z720,z2,z3,z4,z5,z6]),(0,[z0,z251,z3,z4,z287,z6]),(0,[z0,z2,z3,z4,z721,z6]),(0,[z0,z2,z3,z28,z5,z649]),(0,[z0,z2,z722,z4,z5,z6]),(0,[z0,z3,z4,z274,z48,z6]),(0,[z275,z2,z3,z4,z71,z6])],[(0,[z108,z2,z3,z368,z5,z6]),(0,[z114,z2,z3,z4,z83,z6]),(0,[z0,z119,z3,z40,z5,z107]),(0,[z0,z2,z3,z723,z5,z6])],[(0,[z12,z0,z3,z4,z34,z6]),(0,[z0,z36,z141,z3,z48,z6]),(0,[z0,z2,z3,z4,z724,z6]),(0,[z0,z725,z3,z4,z5,z6]),(0,[z0,z3,z4,z179,z6,z13])],[(0,[z0,z119,z3,z4,z5,z228]),(0,[z0,z2,z3,z296,z5,z6]),(0,[z0,z726,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z727,z6])],[(0,[z225,z2,z3,z15,z5,z6]),(0,[z0,z728,z3,z4,z5,z6]),(0,[z0,z729,z3,z40,z5,z6]),(0,[z0,z3,z282,z4,z48,z6]),(0,[z275,z2,z3,z4,z101,z6])],[(0,[z0,z2,z3,z730,z179,z6]),(0,[z0,z3,z4,z287,z48,z6])],[(0,[z731,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z732,z345,z6]),(0,[z0,z3,z733,z4,z5,z6]),(1,[z0,z3,z4,z734,z6])],[(0,[z0,z262,z3,z54,z5,z6]),(0,[z0,z2,z3,z735,z5,z6]),(0,[z0,z2,z3,z736,z5,z6]),(0,[z0,z737,z3,z4,z5,z6])]]

def bk1_1 : List (List (ℕ × List W)) :=
  [[(0,[z738,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z256]),(0,[z739,z2,z3,z4,z5,z6])],[(0,[z454,z292,z3,z4,z5,z6]),(0,[z0,z17,z3,z277,z5,z6]),(0,[z0,z3,z153,z40,z48,z6]),(0,[z0,z3,z4,z295,z48,z6])],[(0,[z0,z17,z3,z215,z5,z6]),(0,[z0,z2,z40,z5,z392,z6])],[],[(0,[z0,z2,z3,z397,z5,z6])],[(0,[z0,z2,z3,z740,z5,z6]),(0,[z0,z2,z3,z54,z179,z6]),(0,[z0,z2,z3,z4,z5,z741]),(0,[z0,z2,z3,z385,z326,z6]),(0,[z0,z70,z3,z184,z5,z6]),(0,[z0,z3,z381,z5,z48,z6])],[(0,[z742,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z743,z5,z6]),(0,[z0,z3,z4,z198,z48,z6]),(0,[z0,z3,z4,z299,z48,z6])],[(0,[z0,z2,z40,z5,z403,z6])],[(0,[z0,z744,z3,z4,z5,z6])],[(0,[z447,z3,z4,z5,z642,z6]),(0,[z159,z2,z3,z296,z5,z6]),(0,[z0,z2,z3,z745,z4,z6]),(0,[z0,z3,z4,z243,z48,z6])],[(0,[z50,z3,z511,z4,z5,z6]),(0,[z0,z366,z3,z4,z48,z6]),(0,[z0,z3,z4,z190,z746,z6]),(0,[z144,z2,z3,z397,z5,z6])],[(0,[z0,z747,z3,z4,z5,z6]),(0,[z0,z2,z3,z397,z190,z6]),(0,[z0,z748,z3,z4,z5,z6])],[(0,[z0,z17,z3,z4,z83,z6])],[(0,[z0,z749,z2,z3,z5,z6]),(0,[z0,z750,z3,z4,z5,z6]),(0,[z0,z3,z111,z5,z48,z6]),(0,[z0,z3,z385,z5,z48,z6])],[(0,[z0,z3,z4,z5,z6,z751])],[(0,[z0,z3,z385,z5,z319,z6])]]

def bk1_2 : List (List (ℕ × List W)) :=
  [[(0,[z26,z2,z3,z4,z5,z752]),(0,[z0,z17,z3,z4,z5,z393]),(0,[z0,z2,z3,z54,z5,z41]),(0,[z0,z2,z3,z4,z753,z6]),(0,[z0,z203,z3,z54,z5,z6])],[(0,[z159,z17,z3,z4,z5,z6]),(0,[z0,z754,z3,z54,z5,z6]),(0,[z0,z2,z3,z755,z5,z6]),(0,[z0,z3,z4,z5,z107,z756]),(0,[z0,z3,z4,z23,z48,z6])],[(0,[z0,z17,z3,z4,z5,z757]),(0,[z0,z2,z3,z758,z5,z6]),(0,[z0,z3,z4,z5,z759,z6])],[(0,[z760,z2,z3,z40,z5,z6]),(0,[z0,z31,z110,z54,z5,z6]),(0,[z0,z2,z3,z40,z179,z6]),(0,[z0,z3,z44,z4,z5,z6])],[(0,[z0,z36,z3,z4,z761,z6]),(0,[z0,z762,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z763,z6]),(0,[z0,z68,z3,z54,z5,z6]),(0,[z0,z3,z4,z5,z6,z764])],[(0,[z454,z0,z3,z4,z765,z6]),(0,[z0,z2,z3,z766,z5,z6]),(0,[z2,z3,z4,z5,z767,z6])],[(0,[z0,z262,z3,z368,z5,z6]),(0,[z0,z3,z397,z5,z48,z6])],[(0,[z0,z3,z4,z5,z768,z6])],[(0,[z114,z17,z3,z4,z5,z6]),(0,[z0,z17,z3,z4,z5,z769]),(0,[z0,z17,z3,z314,z5,z6]),(0,[z0,z2,z3,z770,z5,z6]),(0,[z0,z2,z3,z4,z5,z771])],[(0,[z0,z772,z3,z4,z5,z6]),(0,[z0,z773,z3,z4,z5,z6]),(0,[z0,z2,z3,z22,z28,z5]),(0,[z0,z3,z4,z142,z75,z6])],[(0,[z0,z17,z3,z264,z5,z6]),(0,[z0,z2,z3,z4,z5,z752])],[],[(0,[z0,z203,z3,z4,z142,z6])],[(0,[z0,z262,z3,z4,z5,z409]),(0,[z0,z2,z3,z154,z5,z112]),(0,[z0,z224,z3,z397,z5,z6]),(0,[z0,z3,z40,z97,z48,z6]),(0,[z0,z3,z103,z5,z48,z6])],[(0,[z0,z203,z3,z40,z5,z6]),(0,[z0,z3,z4,z5,z48,z409]),(0,[z0,z3,z4,z581,z48,z6])],[(0,[z0,z2,z3,z774,z5,z6]),(0,[z0,z775,z3,z54,z5,z6]),(0,[z0,z3,z4,z34,z48,z6]),(0,[z292,z2,z3,z513,z5,z6])]]

def bk1_3 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z54,z5,z776]),(0,[z0,z2,z3,z777,z5,z6]),(0,[z0,z3,z54,z5,z48,z6])],[(0,[z487,z21,z3,z4,z5,z6]),(0,[z0,z31,z110,z40,z5,z6]),(0,[z0,z3,z778,z5,z48,z6])],[(0,[z0,z2,z3,z4,z779,z6]),(0,[z0,z68,z3,z40,z5,z6])],[(0,[z0,z17,z3,z4,z326,z6]),(0,[z0,z2,z3,z780,z5,z6]),(0,[z0,z2,z3,z4,z367,z393]),(0,[z0,z3,z337,z4,z48,z6]),(0,[z0,z3,z4,z5,z6,z781])],[(0,[z0,z2,z3,z4,z782,z6])],[(0,[z0,z131,z3,z4,z48,z6]),(0,[z0,z370,z3,z4,z5,z6])],[(0,[z108,z2,z3,z425,z5,z6]),(0,[z0,z2,z3,z783,z5,z6]),(0,[z0,z3,z4,z163,z48,z6]),(0,[z0,z3,z4,z535,z784,z6]),(0,[z0,z3,z40,z142,z48,z6]),(0,[z21,z785,z3,z4,z5,z6])],[(0,[z0,z786,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z787,z6]),(0,[z0,z2,z3,z4,z788,z6]),(0,[z0,z3,z4,z424,z48,z6])],[(0,[z0,z789,z2,z3,z179,z6]),(0,[z0,z241,z3,z57,z4,z48]),(0,[z0,z2,z790,z4,z5,z6]),(0,[z0,z3,z57,z46,z48,z6])],[(0,[z0,z2,z3,z4,z791,z5]),(0,[z0,z2,z3,z40,z5,z223]),(0,[z0,z224,z3,z40,z5,z6]),(0,[z0,z3,z4,z48,z212,z6]),(0,[z144,z437,z3,z4,z5,z6])],[(0,[z0,z241,z3,z204,z4,z5]),(0,[z0,z437,z3,z4,z190,z6]),(0,[z0,z2,z3,z792,z5,z6]),(0,[z0,z2,z3,z4,z71,z135]),(0,[z292,z3,z4,z5,z48,z6])],[(0,[z0,z793,z3,z5,z48,z6]),(0,[z0,z68,z3,z368,z5,z6])],[(0,[z794,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z54,z243,z6])],[(0,[z0,z406,z3,z4,z5,z107])],[(0,[z50,z785,z3,z4,z5,z6])],[(0,[z0,z2,z3,z795,z5,z6]),(0,[z0,z2,z3,z796,z5,z6]),(0,[z0,z2,z3,z797,z5,z6])]]

def bk1_4 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z798,z5,z6])],[(0,[z0,z2,z3,z799,z5,z6]),(0,[z0,z2,z3,z800,z5,z6])],[(0,[z26,z2,z3,z40,z5,z27]),(0,[z0,z17,z3,z4,z287,z6]),(0,[z0,z17,z3,z4,z5,z135]),(0,[z0,z36,z3,z153,z48,z6]),(0,[z0,z2,z3,z801,z5,z6]),(0,[z0,z68,z3,z4,z5,z409]),(0,[z70,z3,z45,z4,z5,z6])],[],[(0,[z0,z802,z3,z4,z5,z6]),(0,[z0,z2,z3,z803,z5,z6])],[],[(0,[z50,z3,z4,z5,z6,z483]),(0,[z0,z2,z3,z804,z40,z5]),(0,[z0,z2,z3,z4,z5,z805]),(0,[z806,z2,z3,z4,z5,z6])],[(0,[z0,z807,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z83,z61]),(0,[z0,z2,z3,z4,z808,z6]),(0,[z0,z2,z271,z54,z5,z6]),(0,[z0,z3,z54,z5,z75,z6]),(0,[z0,z3,z4,z48,z228,z6]),(0,[z0,z3,z513,z5,z48,z6])],[(0,[z0,z17,z3,z54,z48,z6]),(0,[z0,z2,z3,z809,z5,z6])],[(0,[z0,z127,z3,z55,z5,z6])],[(0,[z0,z810,z3,z4,z163,z6]),(0,[z0,z2,z3,z4,z811,z6]),(0,[z0,z2,z3,z40,z243,z6]),(0,[z0,z3,z152,z4,z345,z6]),(0,[z0,z3,z57,z4,z369,z48]),(0,[z0,z3,z385,z71,z48,z6])],[(0,[z0,z749,z2,z3,z345,z6]),(0,[z0,z2,z3,z4,z5,z812]),(0,[z0,z3,z4,z761,z5,z6]),(0,[z0,z3,z4,z5,z813,z6])],[(0,[z0,z2,z3,z444,z5,z62]),(0,[z0,z2,z3,z814,z5,z6]),(0,[z0,z2,z3,z815,z5,z6]),(0,[z0,z3,z40,z48,z101,z6])],[(0,[z0,z2,z3,z730,z5,z6]),(0,[z3,z45,z4,z97,z48,z6])],[(0,[z0,z17,z3,z4,z367,z6]),(0,[z0,z816,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z817,z6])],[(0,[z0,z818,z3,z4,z5,z6]),(0,[z0,z305,z3,z4,z5,z41]),(0,[z0,z2,z3,z237,z83,z6]),(0,[z0,z2,z3,z4,z5,z819])]]

def bk1_5 : List (List (ℕ × List W)) :=
  [[(0,[z0,z36,z2,z3,z385,z6]),(0,[z0,z2,z3,z149,z5,z6]),(0,[z0,z2,z3,z4,z123,z6]),(0,[z0,z3,z380,z4,z48,z6])],[(0,[z0,z2,z3,z820,z5,z6]),(0,[z0,z3,z381,z57,z48,z6]),(0,[z0,z3,z4,z734,z59,z6])],[(0,[z0,z3,z4,z5,z821,z6]),(0,[z275,z2,z3,z54,z5,z6])],[(0,[z108,z2,z3,z4,z5,z409]),(0,[z114,z2,z3,z4,z5,z61]),(0,[z0,z262,z3,z425,z5,z6]),(0,[z0,z2,z3,z4,z822,z6]),(0,[z0,z70,z3,z4,z5,z6]),(0,[z0,z3,z33,z5,z48,z6])],[(0,[z0,z2,z3,z823,z5,z6]),(0,[z0,z3,z4,z5,z6,z824])],[(0,[z0,z825,z3,z4,z5,z6]),(0,[z0,z2,z3,z826,z5,z6]),(0,[z0,z2,z3,z54,z5,z6]),(0,[z0,z2,z3,z827,z5,z6])],[(0,[z0,z17,z3,z40,z48,z6]),(0,[z0,z2,z3,z828,z5,z6]),(0,[z0,z2,z3,z237,z5,z61]),(0,[z0,z401,z3,z4,z163,z6])],[(0,[z0,z69,z3,z55,z123,z6]),(0,[z0,z230,z3,z40,z5,z6]),(0,[z0,z2,z3,z4,z5,z829]),(0,[z0,z2,z54,z351,z5,z6]),(0,[z0,z70,z3,z182,z5,z6]),(0,[z0,z3,z4,z5,z830,z6])],[(0,[z0,z831,z2,z3,z5,z6]),(0,[z0,z2,z3,z832,z5,z6]),(0,[z0,z2,z3,z264,z5,z59])],[(0,[z14,z0,z36,z3,z48,z6]),(0,[z50,z0,z3,z4,z345,z6]),(0,[z0,z452,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z833,z6]),(0,[z0,z2,z3,z4,z5,z311]),(0,[z0,z2,z3,z4,z5,z834])],[(0,[z0,z3,z302,z4,z48,z6]),(0,[z835,z2,z3,z4,z5,z6])],[(0,[z114,z2,z3,z237,z5,z6]),(0,[z0,z2,z3,z836,z5,z6]),(0,[z0,z110,z79,z4,z5,z6]),(0,[z144,z2,z3,z54,z5,z6])],[(0,[z0,z200,z3,z4,z123,z6]),(0,[z0,z2,z3,z54,z190,z6]),(0,[z0,z2,z3,z837,z5,z6]),(0,[z0,z2,z3,z4,z83,z256])],[(0,[z0,z838,z3,z4,z142,z6]),(0,[z0,z2,z3,z4,z5,z839]),(0,[z0,z2,z3,z4,z34,z6]),(0,[z0,z3,z840,z5,z48,z6]),(0,[z0,z3,z54,z71,z48,z6])],[(0,[z0,z841,z3,z4,z5,z6]),(0,[z2,z3,z842,z4,z5,z6])],[(0,[z0,z2,z3,z517,z5,z6]),(0,[z0,z401,z3,z4,z71,z6]),(0,[z0,z3,z165,z5,z48,z6])]]

def bk1_6 : List (List (ℕ × List W)) :=
  [[(0,[z53,z2,z3,z4,z5,z41]),(0,[z0,z17,z3,z385,z5,z6]),(0,[z0,z31,z3,z4,z34,z6]),(0,[z0,z843,z3,z4,z5,z6]),(0,[z0,z2,z3,z844,z5,z6]),(0,[z0,z2,z3,z4,z5,z845]),(0,[z275,z2,z3,z40,z5,z6])],[(0,[z14,z160,z2,z3,z5,z6]),(0,[z0,z200,z3,z54,z5,z6]),(0,[z0,z418,z3,z4,z48,z6]),(0,[z0,z846,z3,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z847,z6]),(0,[z0,z2,z3,z40,z5,z6]),(0,[z0,z401,z3,z4,z101,z6]),(0,[z0,z3,z4,z48,z168,z6])],[(0,[z848,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z849,z5,z6])],[(0,[z49,z2,z3,z4,z5,z27]),(0,[z159,z2,z3,z397,z5,z6]),(0,[z0,z17,z3,z323,z5,z6]),(0,[z0,z2,z3,z850,z5,z6]),(0,[z0,z3,z4,z5,z734,z6]),(0,[z0,z3,z4,z5,z851,z6])],[(0,[z852,z2,z3,z4,z5,z6]),(0,[z0,z17,z3,z4,z5,z61]),(0,[z0,z2,z3,z4,z853,z6]),(0,[z0,z3,z4,z485,z48,z6])],[(0,[z0,z240,z208,z4,z5,z6]),(0,[z0,z2,z3,z854,z4,z5]),(0,[z0,z2,z3,z4,z5,z855])],[(0,[z114,z2,z3,z4,z5,z256]),(0,[z0,z2,z3,z4,z5,z856]),(0,[z0,z2,z857,z4,z5,z6]),(0,[z0,z68,z3,z425,z5,z6]),(0,[z2,z3,z858,z4,z5,z6])],[(0,[z0,z2,z3,z859,z5,z6]),(0,[z0,z2,z306,z40,z5,z6]),(0,[z0,z3,z412,z4,z48,z6]),(0,[z144,z2,z3,z40,z5,z6]),(0,[z275,z2,z3,z368,z5,z6])],[(0,[z294,z2,z3,z242,z5,z6]),(0,[z0,z2,z3,z40,z190,z6])],[(0,[z115,z0,z2,z40,z101,z6]),(0,[z0,z2,z3,z237,z5,z256]),(0,[z0,z70,z3,z4,z317,z6])],[(0,[z860,z0,z3,z4,z5,z6]),(0,[z0,z36,z73,z3,z48,z6]),(0,[z0,z2,z3,z4,z861,z6]),(0,[z0,z2,z3,z862,z5,z6]),(0,[z0,z2,z3,z368,z5,z6])],[(0,[z0,z17,z366,z3,z5,z6]),(0,[z0,z2,z3,z54,z317,z6]),(0,[z0,z3,z4,z345,z107,z6])],[(0,[z0,z17,z3,z237,z5,z6]),(0,[z0,z2,z3,z54,z5,z223]),(0,[z0,z2,z3,z863,z5,z6]),(0,[z0,z224,z3,z54,z5,z6]),(0,[z0,z3,z54,z153,z48,z6]),(0,[z0,z3,z4,z5,z864,z6])],[(0,[z0,z200,z3,z40,z5,z6]),(0,[z0,z3,z152,z4,z5,z61]),(0,[z2,z3,z639,z4,z5,z27])]]

def bk1_7 : List (List (ℕ × List W)) :=
  [[(0,[z865,z2,z3,z4,z5,z6])],[(0,[z159,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z866,z5,z6])],[(0,[z0,z2,z3,z4,z5,z867]),(0,[z0,z2,z3,z4,z868,z6]),(0,[z0,z2,z3,z4,z869,z6])],[(0,[z0,z17,z141,z3,z48,z6]),(0,[z0,z2,z3,z381,z5,z6]),(0,[z0,z2,z3,z4,z870,z6])],[(0,[z0,z871,z3,z4,z5,z6])],[(0,[z280,z3,z4,z97,z48,z6]),(0,[z0,z872,z3,z40,z5,z6]),(0,[z0,z2,z3,z4,z734,z6]),(0,[z0,z3,z4,z263,z48,z6])],[(0,[z0,z17,z3,z296,z5,z6]),(0,[z0,z437,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z873,z6]),(0,[z0,z2,z3,z874,z5,z6]),(0,[z0,z3,z149,z5,z48,z6])],[(0,[z193,z423,z3,z4,z5,z6]),(0,[z26,z2,z3,z54,z5,z27]),(0,[z0,z452,z3,z4,z146,z6]),(0,[z0,z2,z3,z875,z5,z6])],[(0,[z0,z789,z2,z3,z5,z6]),(0,[z0,z876,z2,z3,z5,z6]),(0,[z0,z3,z340,z4,z48,z6])],[(0,[z877,z2,z3,z4,z5,z6]),(0,[z878,z2,z3,z4,z5,z6])],[(0,[z108,z3,z4,z5,z48,z6]),(0,[z0,z3,z4,z5,z6,z879])],[(0,[z0,z17,z3,z4,z5,z256]),(0,[z0,z2,z3,z40,z317,z6])],[(0,[z0,z2,z880,z4,z5,z6]),(0,[z881,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z882]),(0,[z0,z2,z3,z883,z5,z6]),(0,[z0,z3,z4,z439,z48,z6])],[(0,[z0,z884,z3,z4,z5,z6])],[(0,[z0,z17,z3,z397,z5,z6]),(0,[z0,z31,z880,z4,z5,z6]),(0,[z0,z2,z3,z4,z885,z6])]]

def bk1_8 : List (List (ℕ × List W)) :=
  [[(0,[z0,z886,z3,z4,z5,z6]),(0,[z0,z2,z3,z887,z5,z6])],[(0,[z0,z2,z3,z4,z101,z135]),(0,[z888,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z889,z5,z6]),(0,[z0,z890,z3,z4,z5,z6]),(0,[z0,z3,z4,z700,z48,z6]),(0,[z0,z3,z883,z5,z48,z6])],[(0,[z0,z2,z3,z54,z345,z6]),(0,[z0,z2,z3,z891,z5,z6]),(0,[z0,z2,z3,z4,z892,z6]),(0,[z0,z2,z3,z4,z893,z6]),(0,[z0,z3,z4,z355,z48,z6])],[(0,[z894,z2,z3,z4,z5,z6]),(0,[z159,z437,z3,z4,z5,z6]),(0,[z0,z2,z3,z40,z5,z895]),(0,[z0,z3,z4,z5,z48,z896])],[(0,[z0,z3,z360,z4,z48,z6])],[(0,[z0,z897,z3,z4,z5,z6]),(0,[z0,z251,z3,z54,z5,z6]),(0,[z0,z2,z3,z4,z898,z6]),(0,[z0,z2,z3,z899,z5,z6]),(0,[z0,z3,z4,z48,z322,z6])],[(0,[z0,z2,z3,z900,z5,z6])],[(0,[z0,z2,z3,z901,z5,z6]),(0,[z0,z3,z385,z326,z48,z6])],[(0,[z50,z21,z3,z4,z5,z6])],[(0,[z0,z2,z3,z745,z40,z6]),(0,[z0,z2,z3,z4,z535,z6]),(0,[z0,z2,z3,z4,z5,z902]),(0,[z0,z2,z3,z903,z5,z6]),(0,[z0,z2,z40,z5,z6,z533])],[(0,[z904,z3,z4,z5,z48,z6]),(0,[z0,z905,z3,z4,z71,z6]),(0,[z0,z2,z3,z4,z5,z906]),(0,[z0,z3,z40,z5,z6,z764])],[(0,[z0,z230,z3,z54,z5,z6]),(0,[z0,z2,z3,z707,z5,z6]),(0,[z0,z2,z3,z4,z907,z6]),(0,[z0,z3,z264,z5,z48,z6])],[(0,[z0,z2,z3,z908,z5,z6])],[(0,[z0,z70,z3,z4,z367,z6])],[(0,[z0,z909,z2,z3,z4,z6]),(0,[z0,z141,z3,z385,z5,z6]),(0,[z0,z363,z3,z54,z5,z6]),(0,[z0,z910,z3,z4,z5,z6]),(0,[z0,z2,z3,z911,z5,z6])]]

def bk1_9 : List (List (ℕ × List W)) :=
  [[(0,[z0,z423,z3,z4,z48,z6]),(0,[z0,z269,z3,z4,z48,z6]),(0,[z0,z2,z3,z912,z5,z6]),(0,[z0,z3,z913,z40,z5,z6]),(0,[z144,z2,z3,z4,z535,z6])],[(0,[z0,z914,z3,z4,z5,z6]),(0,[z0,z2,z3,z381,z146,z6]),(0,[z0,z2,z3,z4,z5,z915]),(0,[z0,z2,z3,z40,z345,z6]),(0,[z0,z2,z3,z916,z5,z6])],[],[(0,[z0,z17,z3,z4,z5,z771]),(0,[z0,z141,z3,z43,z5,z6]),(0,[z0,z110,z3,z4,z179,z6])],[(0,[z0,z251,z3,z40,z5,z6]),(0,[z0,z3,z4,z917,z5,z6]),(0,[z0,z3,z4,z5,z918,z6])],[(0,[z0,z3,z463,z4,z48,z6]),(0,[z144,z2,z3,z4,z5,z58])],[(0,[z0,z36,z3,z95,z48,z6]),(0,[z0,z2,z3,z4,z190,z58]),(0,[z0,z3,z4,z464,z48,z6]),(0,[z275,z2,z3,z425,z5,z6])],[(0,[z0,z139,z3,z40,z5,z6]),(0,[z0,z141,z3,z153,z48,z6]),(0,[z0,z2,z3,z919,z5,z6]),(0,[z0,z3,z184,z5,z48,z6])],[(0,[z0,z2,z3,z920,z5,z6])],[(0,[z0,z2,z3,z425,z5,z6]),(0,[z0,z2,z3,z921,z5,z6])],[(0,[z0,z2,z3,z4,z922,z6]),(0,[z0,z2,z3,z923,z5,z6]),(0,[z0,z3,z4,z5,z924,z6])],[(0,[z0,z4,z297,z48,z101,z6]),(0,[z2,z3,z925,z4,z5,z6])],[(0,[z0,z141,z3,z5,z48,z6]),(0,[z0,z926,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z319,z6])],[(0,[z0,z363,z3,z40,z5,z6]),(0,[z0,z3,z40,z163,z48,z6])],[(0,[z927,z2,z3,z4,z5,z6]),(0,[z0,z928,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z929,z6])],[(0,[z0,z2,z3,z54,z930,z6]),(0,[z0,z3,z4,z394,z48,z6]),(0,[z0,z3,z4,z5,z931,z6])]]

def bk1_10 : List (List (ℕ × List W)) :=
  [[(0,[z0,z3,z4,z5,z932,z6])],[(0,[z0,z2,z3,z54,z83,z6]),(0,[z0,z3,z4,z163,z48,z72])],[(0,[z933,z2,z3,z4,z5,z6]),(0,[z2,z3,z934,z4,z5,z6])],[(0,[z0,z17,z3,z4,z676,z6]),(0,[z0,z119,z3,z4,z5,z531]),(0,[z0,z70,z3,z4,z5,z393]),(0,[z0,z224,z3,z4,z535,z6]),(0,[z0,z3,z22,z5,z48,z6])],[(0,[z0,z2,z3,z4,z935,z6]),(0,[z0,z3,z54,z936,z5,z6])],[(0,[z0,z452,z3,z4,z83,z6]),(0,[z0,z937,z3,z4,z5,z6]),(0,[z0,z2,z3,z54,z5,z393])],[(0,[z159,z2,z3,z54,z5,z6]),(0,[z0,z938,z3,z4,z5,z6]),(0,[z0,z2,z3,z939,z5,z6])],[],[(0,[z0,z2,z3,z940,z5,z6]),(0,[z0,z224,z3,z4,z5,z58]),(0,[z0,z3,z4,z5,z941,z6]),(0,[z0,z3,z4,z5,z48,z41])],[(0,[z0,z31,z635,z4,z5,z6]),(0,[z0,z2,z3,z4,z942,z6]),(0,[z0,z2,z3,z5,z6,z943]),(0,[z0,z401,z3,z54,z5,z6])],[],[(0,[z0,z2,z3,z4,z5,z944])],[(0,[z0,z3,z936,z4,z5,z6])],[(0,[z114,z2,z3,z54,z5,z6]),(0,[z0,z2,z3,z154,z5,z223]),(0,[z0,z2,z3,z4,z5,z945]),(0,[z0,z2,z3,z4,z946,z6])],[],[(0,[z0,z947,z3,z4,z190,z6]),(0,[z0,z17,z3,z803,z5,z6]),(0,[z0,z2,z3,z948,z5,z6]),(0,[z0,z2,z3,z949,z5,z6]),(0,[z0,z2,z3,z40,z83,z6]),(0,[z0,z3,z57,z4,z48,z6]),(0,[z0,z3,z4,z179,z48,z6])]]

def bk1_11 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z950,z5,z6]),(0,[z0,z2,z3,z4,z951,z6]),(0,[z0,z2,z3,z4,z34,z61])],[(0,[z0,z3,z4,z5,z952,z6])],[(0,[z454,z0,z3,z4,z5,z6]),(0,[z0,z953,z2,z3,z5,z6]),(0,[z0,z2,z3,z954,z5,z6]),(0,[z0,z3,z4,z345,z48,z6])],[(0,[z0,z2,z3,z40,z5,z393]),(0,[z0,z955,z3,z4,z5,z6]),(0,[z275,z2,z3,z4,z5,z409])],[(0,[z12,z292,z3,z4,z5,z6]),(0,[z0,z36,z3,z48,z6,z62]),(0,[z0,z415,z3,z54,z5,z6]),(0,[z0,z3,z4,z499,z48,z6]),(0,[z0,z3,z4,z123,z48,z6])],[(0,[z956,z3,z4,z5,z48,z6]),(0,[z114,z2,z3,z4,z34,z6]),(0,[z0,z786,z3,z4,z367,z6]),(0,[z0,z2,z3,z4,z5,z957])],[(0,[z0,z2,z3,z4,z5,z409]),(0,[z0,z2,z3,z40,z5,z61])],[(0,[z0,z2,z3,z4,z958,z6]),(0,[z0,z401,z3,z40,z5,z6]),(0,[z0,z3,z959,z5,z48,z6])],[(0,[z0,z2,z3,z54,z326,z6]),(0,[z0,z2,z3,z237,z34,z6]),(0,[z0,z2,z3,z960,z5,z6])],[],[(0,[z961,z0,z3,z4,z5,z6]),(0,[z50,z3,z4,z5,z642,z6]),(0,[z0,z3,z54,z5,z143,z6])],[(0,[z114,z2,z3,z40,z5,z6]),(0,[z0,z17,z3,z4,z123,z6]),(0,[z0,z962,z2,z3,z5,z6]),(0,[z0,z3,z430,z54,z48,z6]),(0,[z0,z3,z4,z48,z396,z6])],[(0,[z108,z262,z3,z4,z5,z6]),(0,[z0,z963,z3,z40,z5,z6]),(0,[z0,z964,z2,z3,z5,z6]),(0,[z0,z2,z3,z965,z5,z6])],[(0,[z0,z2,z3,z966,z5,z6]),(0,[z0,z2,z3,z967,z5,z6]),(0,[z0,z3,z4,z5,z968,z6]),(0,[z0,z3,z4,z48,z400,z6])],[(0,[z0,z3,z4,z5,z969,z6])],[(0,[z0,z3,z4,z5,z970,z6])]]

def bk1_12 : List (List (ℕ × List W)) :=
  [[(0,[z0,z17,z3,z54,z5,z6]),(0,[z0,z2,z3,z971,z5,z6])],[(0,[z50,z0,z3,z4,z5,z61]),(0,[z0,z2,z3,z4,z972,z6]),(0,[z0,z2,z3,z4,z5,z973]),(0,[z0,z2,z3,z974,z5,z6])],[(0,[z0,z415,z3,z40,z5,z6]),(0,[z292,z2,z3,z4,z5,z6])],[(0,[z0,z272,z3,z4,z5,z6])],[(0,[z0,z17,z3,z4,z5,z311]),(0,[z0,z31,z110,z111,z5,z6])],[(0,[z0,z2,z3,z975,z5,z6]),(0,[z0,z2,z3,z4,z34,z256])],[(0,[z0,z2,z3,z40,z326,z6]),(0,[z3,z4,z142,z97,z48,z6])],[(0,[z0,z305,z3,z4,z5,z6]),(0,[z0,z2,z3,z54,z287,z6]),(0,[z0,z2,z3,z54,z5,z135]),(0,[z0,z2,z3,z976,z5,z6]),(0,[z0,z977,z3,z4,z5,z6])],[(0,[z0,z17,z3,z4,z34,z6]),(0,[z0,z2,z3,z978,z5,z6])],[(0,[z0,z141,z3,z71,z48,z6]),(0,[z0,z2,z3,z979,z5,z6]),(0,[z0,z203,z3,z4,z97,z6]),(0,[z980,z2,z3,z4,z5,z6])],[(0,[z0,z17,z3,z517,z5,z6]),(0,[z0,z3,z4,z525,z48,z6])],[(0,[z0,z305,z3,z182,z5,z6]),(0,[z0,z2,z3,z981,z4,z5]),(0,[z0,z2,z3,z40,z5,z256])],[(0,[z0,z139,z3,z54,z5,z6]),(0,[z0,z305,z3,z184,z5,z6])],[],[(0,[z0,z17,z3,z40,z5,z6]),(0,[z0,z2,z3,z4,z5,z982])],[(0,[z848,z17,z3,z4,z5,z6]),(0,[z0,z2,z3,z983,z5,z6])]]

def bk1_13 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z984,z5,z6]),(0,[z0,z3,z4,z367,z48,z6])],[(0,[z108,z68,z3,z4,z5,z6]),(0,[z0,z36,z2,z3,z5,z223]),(0,[z0,z110,z4,z5,z297,z6]),(0,[z0,z3,z152,z4,z34,z6]),(0,[z0,z3,z4,z317,z48,z6])],[(0,[z118,z3,z4,z142,z48,z6]),(0,[z0,z17,z3,z4,z5,z855]),(0,[z0,z2,z3,z4,z5,z985]),(0,[z0,z2,z3,z513,z5,z6]),(0,[z0,z2,z986,z4,z5,z6])],[(0,[z0,z2,z3,z54,z367,z6]),(0,[z0,z3,z987,z4,z5,z6]),(0,[z0,z3,z988,z4,z5,z6]),(0,[z0,z3,z4,z458,z48,z6])],[(0,[z0,z989,z3,z4,z5,z6]),(0,[z0,z3,z875,z5,z48,z6]),(0,[z0,z3,z4,z39,z48,z6])],[(0,[z0,z990,z3,z4,z5,z6]),(0,[z0,z2,z3,z40,z287,z6]),(0,[z0,z2,z3,z40,z5,z135])],[(0,[z0,z3,z54,z5,z6,z324])],[(0,[z0,z17,z3,z368,z5,z6]),(0,[z0,z991,z3,z4,z5,z6]),(0,[z0,z2,z3,z778,z5,z6])],[(0,[z0,z213,z3,z4,z48,z6]),(0,[z0,z141,z3,z57,z48,z6]),(0,[z0,z2,z3,z4,z765,z6])],[(0,[z0,z992,z2,z3,z4,z6]),(0,[z0,z437,z3,z296,z5,z6]),(0,[z0,z2,z3,z993,z5,z6]),(0,[z0,z2,z3,z4,z994,z6]),(0,[z0,z3,z4,z465,z48,z6]),(0,[z0,z3,z4,z5,z995,z6])],[(0,[z0,z66,z3,z4,z179,z6]),(0,[z0,z4,z71,z48,z101,z6]),(0,[z275,z3,z4,z5,z48,z6])],[(0,[z159,z2,z3,z4,z535,z6]),(0,[z0,z996,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z997,z6])],[(0,[z0,z2,z3,z304,z5,z112]),(0,[z0,z2,z3,z4,z998,z6]),(0,[z0,z999,z3,z4,z5,z6]),(0,[z0,z3,z1000,z5,z75,z6])],[(0,[z0,z3,z4,z5,z48,z6])],[(0,[z0,z17,z3,z381,z5,z6]),(0,[z0,z17,z3,z54,z146,z6]),(0,[z0,z127,z3,z436,z5,z6]),(0,[z0,z2,z3,z1001,z5,z6]),(0,[z0,z2,z3,z368,z5,z135])],[(0,[z0,z305,z3,z4,z317,z6]),(0,[z0,z3,z472,z4,z48,z6])]]

def bk1_14 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1002,z3,z4,z5,z6]),(0,[z0,z3,z4,z146,z1003,z6])],[(0,[z0,z230,z3,z4,z48,z6]),(0,[z0,z2,z3,z4,z5,z1004]),(0,[z0,z2,z3,z40,z367,z6]),(0,[z0,z3,z4,z5,z1005,z6])],[],[(0,[z0,z2,z3,z1006,z5,z6]),(0,[z0,z3,z4,z5,z1007,z6]),(0,[z144,z3,z4,z5,z48,z6])],[(0,[z0,z1008,z3,z54,z5,z6]),(0,[z0,z3,z4,z5,z1009,z6]),(0,[z0,z3,z4,z5,z60,z324])],[(0,[z0,z2,z3,z4,z1010,z6]),(0,[z0,z2,z3,z4,z5,z1011]),(0,[z0,z2,z3,z1012,z5,z6]),(0,[z2,z3,z45,z4,z5,z41])],[(0,[z0,z69,z36,z3,z48,z6]),(0,[z0,z1013,z3,z4,z5,z6]),(0,[z0,z3,z54,z5,z247,z6])],[(0,[z0,z1014,z3,z4,z5,z6]),(0,[z0,z1015,z3,z4,z5,z6]),(0,[z0,z2,z3,z1016,z5,z6]),(0,[z0,z2,z3,z1017,z5,z6]),(0,[z881,z17,z3,z4,z5,z6])],[],[(0,[z0,z838,z3,z4,z48,z6]),(0,[z0,z2,z3,z40,z1018,z6]),(0,[z0,z1019,z3,z4,z5,z6]),(0,[z0,z3,z57,z4,z48,z60])],[(0,[z0,z2,z3,z1020,z5,z6]),(0,[z0,z2,z471,z40,z5,z6])],[(0,[z0,z947,z3,z4,z5,z6]),(0,[z0,z17,z141,z3,z5,z6]),(0,[z0,z2,z3,z54,z5,z61])],[(0,[z0,z17,z3,z40,z146,z6]),(0,[z0,z366,z3,z5,z48,z6]),(0,[z0,z3,z484,z4,z48,z6]),(0,[z0,z3,z4,z48,z453,z6])],[(0,[z0,z990,z3,z4,z317,z6]),(0,[z0,z350,z3,z4,z48,z6]),(0,[z0,z3,z707,z4,z5,z6]),(0,[z0,z3,z4,z48,z455,z6])],[(0,[z0,z141,z272,z3,z5,z6]),(0,[z0,z2,z3,z54,z5,z1021]),(0,[z0,z2,z3,z4,z5,z756]),(0,[z0,z2,z3,z4,z1022,z6]),(0,[z0,z2,z3,z46,z5,z6]),(0,[z1023,z2,z3,z4,z5,z6])],[(0,[z0,z36,z3,z4,z48,z6]),(0,[z0,z793,z2,z3,z5,z6])]]

def bk1_15 : List (List (ℕ × List W)) :=
  [[(0,[z0,z3,z57,z4,z163,z48])],[(0,[z0,z36,z3,z4,z319,z6]),(0,[z0,z2,z3,z1024,z5,z6]),(0,[z0,z2,z3,z1025,z5,z6]),(0,[z0,z2,z3,z182,z5,z41]),(0,[z0,z2,z3,z1026,z5,z6]),(0,[z0,z3,z903,z5,z48,z6])],[(0,[z0,z119,z3,z4,z243,z107]),(0,[z0,z2,z3,z184,z5,z41]),(0,[z0,z2,z3,z1027,z5,z6])],[(0,[z0,z2,z3,z1028,z4,z5]),(0,[z0,z3,z215,z5,z48,z6])],[(0,[z0,z2,z498,z54,z5,z6])],[(0,[z0,z17,z3,z4,z535,z6]),(0,[z0,z17,z3,z4,z266,z6]),(0,[z0,z2,z3,z4,z1029,z6]),(0,[z0,z157,z4,z71,z48,z6])],[(0,[z53,z3,z4,z97,z48,z6]),(0,[z0,z2,z3,z4,z5,z1030]),(0,[z0,z2,z3,z111,z5,z6]),(0,[z0,z2,z3,z40,z1031,z6]),(0,[z0,z1032,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z48,z223])],[(0,[z0,z374,z3,z4,z48,z6])],[(0,[z0,z1033,z3,z4,z5,z6])],[(0,[z0,z200,z3,z4,z48,z6]),(0,[z0,z2,z563,z40,z5,z6]),(0,[z0,z2,z3,z1034,z5,z6])],[(0,[z0,z2,z3,z22,z5,z223]),(0,[z0,z3,z4,z566,z48,z6])],[(0,[z0,z2,z1035,z4,z5,z6]),(0,[z0,z3,z568,z4,z48,z6]),(0,[z0,z3,z4,z5,z1036,z6])],[(0,[z0,z1037,z3,z4,z5,z6]),(0,[z0,z3,z57,z385,z48,z6])],[(0,[z0,z69,z3,z386,z5,z6]),(0,[z0,z1038,z2,z3,z5,z6]),(0,[z0,z73,z3,z5,z319,z6]),(0,[z0,z3,z4,z5,z1039,z6])],[(0,[z82,z0,z3,z4,z179,z6]),(0,[z14,z2,z3,z242,z5,z6]),(0,[z0,z17,z3,z149,z5,z6]),(0,[z0,z2,z3,z1040,z5,z6])],[(0,[z576,z0,z3,z4,z48,z6]),(0,[z26,z3,z4,z5,z48,z27]),(0,[z0,z1041,z3,z4,z535,z6]),(0,[z0,z614,z3,z4,z48,z6]),(0,[z0,z3,z4,z5,z1042,z6])]]

def bk1_16 : List (List (ℕ × List W)) :=
  [[(0,[z0,z909,z2,z3,z40,z6]),(0,[z0,z2,z3,z54,z5,z256]),(0,[z0,z3,z381,z4,z48,z6]),(0,[z0,z3,z509,z4,z48,z6]),(0,[z0,z3,z4,z572,z48,z6]),(0,[z0,z3,z4,z5,z1043,z6])],[(0,[z1044,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z48,z403,z6])],[(0,[z108,z2,z3,z4,z5,z6]),(0,[z0,z370,z3,z4,z734,z6]),(0,[z0,z288,z4,z5,z297,z6])],[(0,[z26,z2,z3,z22,z5,z27]),(0,[z0,z17,z3,z4,z554,z6]),(0,[z0,z1045,z2,z3,z5,z6]),(0,[z0,z2,z502,z40,z5,z6])],[(0,[z1046,z2,z3,z4,z5,z6]),(0,[z0,z17,z3,z425,z5,z6]),(0,[z0,z73,z3,z4,z326,z6])],[(0,[z0,z3,z4,z5,z6,z1047])],[(0,[z225,z2,z3,z491,z5,z6]),(0,[z0,z3,z385,z97,z48,z6])],[(0,[z0,z2,z3,z4,z5,z1048]),(0,[z0,z3,z577,z4,z48,z6])],[(0,[z0,z2,z3,z1049,z5,z6]),(0,[z0,z3,z1050,z4,z5,z6]),(0,[z292,z31,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z752,z6])],[],[(0,[z0,z2,z3,z1051,z5,z6]),(0,[z0,z3,z4,z71,z48,z6])],[(0,[z0,z119,z3,z4,z5,z107]),(0,[z0,z2,z3,z425,z5,z135]),(0,[z0,z2,z3,z4,z1003,z6]),(0,[z0,z2,z3,z40,z123,z6]),(0,[z0,z3,z517,z5,z48,z6])],[(0,[z0,z73,z3,z338,z5,z6]),(0,[z0,z1052,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z896]),(0,[z0,z2,z3,z4,z5,z1053])],[(0,[z0,z2,z3,z4,z5,z1054]),(0,[z0,z2,z3,z1055,z5,z6]),(0,[z0,z2,z3,z1056,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1057]),(0,[z0,z70,z3,z40,z5,z6]),(0,[z0,z729,z3,z4,z5,z6])],[(0,[z0,z3,z385,z142,z48,z6])]]

def bk1_17 : List (List (ℕ × List W)) :=
  [[(0,[z0,z131,z3,z4,z326,z6]),(0,[z0,z2,z516,z40,z5,z6])],[(0,[z0,z240,z3,z4,z34,z6])],[],[(0,[z904,z2,z3,z4,z5,z6]),(0,[z53,z2,z3,z4,z367,z6]),(0,[z0,z3,z44,z54,z5,z6]),(0,[z0,z3,z153,z4,z48,z6])],[(0,[z0,z452,z3,z40,z5,z6]),(0,[z0,z2,z3,z1058,z5,z6]),(0,[z0,z2,z3,z1059,z5,z6]),(0,[z0,z3,z4,z5,z1060,z6])],[(0,[z0,z2,z3,z4,z1061,z6]),(0,[z0,z3,z153,z4,z319,z6])],[(0,[z12,z423,z3,z4,z5,z6]),(0,[z349,z16,z3,z4,z5,z6]),(0,[z0,z2,z3,z1062,z5,z6]),(0,[z0,z3,z4,z588,z48,z6]),(0,[z0,z3,z182,z5,z48,z6])],[(0,[z0,z1063,z3,z4,z5,z6]),(0,[z0,z305,z3,z4,z5,z393]),(0,[z0,z2,z3,z4,z5,z1064]),(0,[z0,z2,z3,z1065,z5,z6]),(0,[z0,z3,z314,z5,z48,z6])],[(0,[z0,z131,z3,z338,z5,z6]),(0,[z0,z1066,z3,z4,z5,z6]),(0,[z0,z2,z3,z40,z34,z6])],[(0,[z0,z3,z54,z97,z48,z6])],[(0,[z1067,z2,z3,z4,z5,z6]),(0,[z0,z1068,z3,z4,z5,z6]),(0,[z0,z370,z3,z4,z811,z6]),(0,[z0,z3,z594,z4,z48,z6])],[(0,[z0,z36,z2,z3,z326,z6])],[(0,[z0,z2,z3,z4,z1069,z6]),(0,[z0,z2,z3,z959,z5,z6]),(0,[z1070,z2,z3,z4,z5,z6]),(0,[z275,z262,z3,z4,z5,z6])],[(0,[z0,z1071,z3,z4,z5,z6]),(0,[z0,z3,z4,z83,z48,z6])],[(0,[z0,z251,z3,z4,z48,z6]),(0,[z0,z2,z3,z513,z83,z6]),(0,[z0,z3,z4,z5,z1072,z6])],[(0,[z0,z262,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z48,z1073])]]

def bk1_18 : List (List (ℕ × List W)) :=
  [[(0,[z0,z36,z3,z48,z6,z37]),(0,[z0,z1074,z3,z4,z5,z6]),(0,[z0,z3,z1075,z4,z5,z6]),(0,[z0,z3,z4,z1003,z5,z6])],[(0,[z0,z17,z3,z4,z5,z409]),(0,[z0,z2,z3,z158,z5,z6]),(0,[z0,z3,z44,z40,z5,z6])],[(0,[z280,z3,z4,z5,z252,z6]),(0,[z0,z1076,z3,z4,z5,z6]),(0,[z0,z3,z54,z142,z48,z6])],[(0,[z50,z0,z3,z4,z34,z6]),(0,[z0,z2,z3,z4,z1077,z6]),(0,[z0,z2,z3,z5,z1078,z6]),(0,[z0,z3,z4,z369,z5,z556]),(0,[z0,z3,z5,z48,z1079,z6])],[(0,[z0,z1080,z3,z4,z5,z6]),(0,[z0,z2,z3,z22,z5,z6]),(0,[z0,z2,z3,z4,z5,z1081]),(0,[z0,z3,z4,z1082,z5,z48])],[(0,[z760,z2,z3,z4,z5,z6]),(0,[z0,z374,z3,z4,z5,z332]),(0,[z0,z370,z3,z54,z5,z6]),(0,[z0,z437,z3,z397,z5,z6]),(0,[z0,z2,z3,z4,z179,z6]),(0,[z0,z2,z3,z513,z5,z61]),(0,[z0,z3,z385,z48,z101,z6])],[(0,[z0,z141,z3,z5,z6,z429]),(0,[z0,z2,z3,z379,z5,z62]),(0,[z0,z2,z3,z1083,z5,z6]),(0,[z0,z3,z40,z5,z970,z6])],[(0,[z50,z619,z3,z4,z5,z6]),(0,[z0,z2,z3,z54,z787,z6]),(0,[z0,z2,z3,z15,z5,z223])],[(0,[z349,z21,z3,z4,z5,z6]),(0,[z0,z366,z2,z3,z48,z6]),(0,[z0,z2,z3,z1084,z5,z6])],[(0,[z0,z1085,z3,z4,z5,z6]),(0,[z0,z2,z3,z54,z791,z5]),(0,[z0,z3,z4,z5,z324,z58])],[(0,[z114,z2,z3,z513,z5,z6]),(0,[z0,z17,z3,z4,z244,z6]),(0,[z0,z3,z277,z5,z48,z6]),(0,[z0,z3,z4,z5,z1086,z6])],[(0,[z0,z2,z3,z4,z1087,z6])],[(0,[z0,z2,z3,z4,z1088,z6])],[(0,[z454,z0,z3,z4,z1089,z6]),(0,[z0,z3,z4,z5,z48,z393]),(0,[z292,z17,z3,z4,z5,z6])],[(0,[z159,z3,z4,z5,z48,z6]),(0,[z0,z3,z1090,z4,z5,z6])],[(0,[z0,z1091,z3,z5,z75,z6]),(0,[z0,z2,z3,z1092,z5,z6]),(0,[z0,z2,z3,z33,z5,z6])]]

def bk1_19 : List (List (ℕ × List W)) :=
  [[(0,[z1093,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z714,z5,z6]),(0,[z0,z2,z3,z4,z5,z41]),(0,[z0,z2,z3,z296,z535,z6]),(0,[z0,z203,z3,z4,z5,z6]),(0,[z0,z1094,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z48,z1095])],[(0,[z0,z181,z3,z4,z5,z332]),(0,[z0,z73,z3,z385,z5,z6]),(0,[z0,z754,z3,z4,z5,z6]),(0,[z0,z437,z3,z40,z5,z6]),(0,[z0,z2,z40,z5,z6,z689]),(0,[z275,z68,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1096])],[(0,[z30,z0,z3,z413,z5,z6]),(0,[z0,z1097,z3,z4,z5,z6])],[(0,[z0,z17,z3,z978,z5,z6]),(0,[z0,z370,z3,z40,z5,z6]),(0,[z0,z31,z110,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1098])],[(0,[z0,z68,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z752,z27])],[(0,[z454,z50,z3,z4,z5,z6]),(0,[z114,z3,z4,z5,z48,z6]),(0,[z0,z69,z3,z5,z319,z6])],[(0,[z0,z1099,z2,z3,z5,z6])],[(0,[z0,z807,z3,z54,z5,z6]),(0,[z0,z2,z3,z1100,z5,z6]),(0,[z0,z2,z3,z1101,z5,z6]),(0,[z0,z3,z4,z5,z75,z6])],[(0,[z0,z2,z3,z4,z5,z1102]),(0,[z0,z2,z1103,z4,z5,z6]),(0,[z0,z2,z925,z4,z5,z6]),(0,[z0,z3,z54,z48,z101,z6]),(0,[z0,z3,z153,z156,z48,z6])],[(0,[z0,z119,z3,z4,z345,z107]),(0,[z0,z2,z3,z397,z535,z6]),(0,[z0,z2,z3,z1104,z5,z6]),(0,[z0,z3,z55,z4,z326,z6])],[(0,[z0,z2,z4,z5,z869,z6])],[(0,[z0,z2,z3,z1105,z5,z6]),(0,[z0,z3,z1106,z5,z48,z6])],[(0,[z99,z2,z3,z138,z5,z6]),(0,[z0,z1107,z3,z4,z5,z6]),(0,[z0,z3,z33,z97,z48,z6])],[(0,[z956,z2,z3,z4,z5,z6]),(0,[z0,z17,z3,z513,z5,z6])],[(0,[z0,z3,z323,z5,z48,z6])],[(0,[z0,z775,z3,z4,z5,z6])]]

def bk1_20 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z54,z123,z6]),(0,[z0,z2,z3,z4,z5,z776])],[(0,[z99,z0,z36,z3,z48,z6]),(0,[z144,z224,z3,z4,z5,z6])],[(0,[z0,z141,z3,z97,z48,z6]),(0,[z0,z2,z3,z1108,z5,z6]),(0,[z0,z224,z3,z4,z190,z6])],[(0,[z0,z2,z3,z4,z1109,z6]),(0,[z0,z2,z3,z4,z1110,z6]),(0,[z0,z70,z3,z54,z5,z6])],[(0,[z0,z2,z3,z103,z5,z6]),(0,[z0,z3,z4,z5,z6,z756]),(0,[z0,z3,z40,z5,z48,z6])],[(0,[z0,z305,z3,z4,z367,z6]),(0,[z0,z2,z54,z472,z5,z6])],[(0,[z0,z1111,z3,z4,z5,z6]),(0,[z0,z2,z3,z934,z5,z6]),(0,[z0,z2,z3,z1112,z5,z6]),(0,[z0,z3,z40,z5,z319,z6])],[(0,[z0,z2,z621,z54,z5,z6]),(0,[z0,z2,z3,z4,z1113,z6])],[(0,[z0,z1114,z3,z4,z5,z6]),(0,[z0,z2,z3,z1115,z4,z5]),(0,[z0,z2,z3,z4,z317,z41]),(0,[z0,z3,z4,z326,z48,z6])],[(0,[z0,z452,z3,z54,z5,z6]),(0,[z0,z1116,z2,z3,z5,z6]),(0,[z0,z2,z3,z54,z5,z311]),(0,[z0,z1117,z3,z4,z5,z6])],[(0,[z451,z2,z3,z4,z5,z27]),(0,[z0,z2,z3,z5,z1079,z6])],[(0,[z1118,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1119]),(0,[z0,z2,z3,z1120,z5,z6])],[(0,[z0,z2,z3,z4,z243,z6]),(0,[z0,z2,z3,z4,z1121,z6]),(0,[z0,z2,z3,z4,z1122,z6])],[(0,[z1123,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z54,z5,z839]),(0,[z0,z2,z3,z54,z34,z6]),(0,[z0,z3,z296,z5,z48,z6]),(0,[z3,z4,z5,z48,z1124,z6])],[(0,[z1125,z0,z3,z4,z5,z6]),(0,[z0,z262,z3,z4,z5,z135]),(0,[z0,z2,z3,z1126,z5,z6]),(0,[z0,z2,z3,z1127,z5,z6])],[(0,[z0,z2,z3,z1128,z5,z6]),(0,[z0,z3,z4,z5,z48,z135])]]

def bk1_21 : List (List (ℕ × List W)) :=
  [[(0,[z0,z131,z141,z3,z48,z6]),(0,[z0,z141,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z1129]),(0,[z0,z1130,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1131,z6]),(0,[z0,z2,z3,z1132,z5,z6]),(0,[z292,z2,z3,z4,z83,z6])],[(0,[z0,z2,z3,z1133,z5,z6]),(0,[z0,z2,z3,z1134,z5,z6])],[(0,[z0,z2,z3,z986,z5,z6]),(0,[z0,z2,z40,z5,z77,z6])],[(0,[z0,z1135,z3,z4,z5,z6]),(0,[z0,z3,z4,z367,z1072,z6])],[(0,[z0,z2,z3,z1136,z5,z6]),(0,[z0,z2,z3,z4,z1137,z6]),(0,[z0,z2,z3,z4,z1138,z6])],[(0,[z0,z1139,z3,z4,z5,z6])],[(0,[z0,z2,z3,z40,z5,z311]),(0,[z0,z3,z1026,z5,z48,z6])],[(0,[z0,z17,z3,z4,z48,z6]),(0,[z292,z2,z3,z4,z5,z61])],[(0,[z0,z17,z3,z46,z5,z6]),(0,[z0,z2,z3,z840,z5,z6]),(0,[z0,z2,z3,z1140,z4,z6]),(0,[z0,z2,z54,z597,z5,z6])],[(0,[z0,z2,z3,z4,z1082,z5]),(0,[z0,z785,z3,z4,z5,z6]),(0,[z0,z3,z45,z4,z1089,z6])],[(0,[z0,z1141,z3,z4,z5,z6]),(0,[z0,z3,z4,z190,z48,z6]),(0,[z0,z3,z736,z5,z48,z6])],[(0,[z0,z2,z3,z165,z5,z6])],[(0,[z0,z17,z3,z1027,z5,z6]),(0,[z0,z1142,z2,z3,z5,z6])],[(0,[z0,z16,z3,z4,z48,z6]),(0,[z0,z69,z3,z413,z5,z6]),(0,[z0,z2,z3,z1143,z5,z6]),(0,[z0,z2,z3,z4,z1144,z6]),(0,[z0,z2,z54,z29,z5,z6]),(0,[z1145,z2,z3,z4,z5,z6])],[]]

def bk1_22 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z156,z5,z223]),(0,[z0,z3,z4,z48,z6,z575]),(0,[z292,z2,z3,z237,z5,z6])],[(0,[z0,z17,z3,z111,z5,z6]),(0,[z0,z838,z3,z4,z5,z6]),(0,[z0,z141,z3,z48,z101,z6]),(0,[z0,z2,z3,z4,z5,z1146])],[(0,[z0,z2,z1147,z4,z5,z6]),(0,[z275,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1148,z5,z6]),(0,[z0,z2,z586,z40,z5,z6])],[(0,[z0,z17,z3,z1034,z5,z6]),(0,[z0,z2,z3,z1028,z40,z5]),(0,[z0,z2,z3,z1149,z5,z6]),(0,[z0,z2,z599,z54,z5,z6]),(0,[z1150,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z1151,z3,z4,z5,z6]),(0,[z1152,z2,z3,z4,z5,z6])],[(0,[z26,z2,z3,z103,z5,z27]),(0,[z1153,z2,z3,z4,z5,z6]),(0,[z0,z181,z3,z4,z345,z6]),(0,[z0,z437,z3,z54,z5,z6]),(0,[z0,z2,z3,z1154,z5,z6]),(0,[z0,z3,z55,z385,z5,z6]),(0,[z0,z3,z4,z668,z48,z6]),(1,[z0,z366,z3,z48,z6])],[(0,[z0,z2,z3,z1155,z5,z6]),(0,[z0,z2,z3,z1156,z5,z6]),(0,[z0,z3,z1157,z4,z5,z6]),(0,[z0,z3,z4,z5,z143,z6]),(0,[z0,z3,z4,z48,z520,z6])],[(0,[z1158,z2,z3,z4,z5,z6]),(0,[z1159,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1160,z5,z6]),(0,[z0,z2,z3,z182,z5,z6]),(0,[z0,z2,z3,z1161,z5,z6]),(0,[z0,z2,z54,z40,z5,z6]),(0,[z0,z1162,z3,z4,z5,z6])],[(0,[z0,z2,z3,z184,z5,z6]),(0,[z0,z3,z57,z40,z48,z6]),(0,[z0,z3,z1163,z5,z48,z6])],[(0,[z115,z0,z4,z48,z101,z6]),(0,[z0,z2,z3,z4,z367,z41]),(0,[z0,z3,z4,z5,z1164,z6]),(0,[z144,z2,z3,z4,z5,z6])],[(0,[z0,z69,z3,z55,z5,z6]),(0,[z0,z2,z3,z4,z190,z6])],[(0,[z108,z17,z3,z4,z5,z6]),(0,[z0,z905,z3,z4,z48,z6]),(0,[z292,z2,z3,z4,z5,z256])],[(0,[z0,z2,z3,z1165,z5,z6])],[(0,[z0,z3,z4,z679,z48,z6])]]

def bk1_23 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z1166,z5,z6]),(0,[z0,z2,z3,z1167,z5,z6])],[(0,[z0,z200,z3,z4,z5,z6]),(0,[z0,z2,z3,z40,z5,z409]),(0,[z0,z3,z4,z5,z1168,z6]),(0,[z0,z3,z40,z71,z48,z6]),(0,[z3,z4,z97,z642,z48,z6])],[(0,[z416,z2,z3,z4,z5,z27]),(0,[z144,z2,z3,z4,z190,z6])],[(0,[z0,z1169,z3,z4,z5,z6]),(0,[z0,z31,z208,z4,z5,z6]),(0,[z0,z2,z3,z1170,z5,z6]),(0,[z0,z2,z3,z117,z5,z223]),(0,[z0,z3,z4,z5,z48,z61])],[(0,[z108,z2,z3,z4,z5,z135])],[(0,[z0,z2,z3,z1106,z5,z6]),(0,[z0,z1171,z3,z4,z5,z6]),(0,[z0,z3,z413,z4,z48,z6])],[(0,[z0,z17,z3,z4,z1003,z6])],[(0,[z0,z872,z3,z4,z5,z6])],[(0,[z0,z17,z3,z1055,z5,z6]),(0,[z0,z810,z3,z4,z48,z6]),(0,[z0,z3,z425,z5,z48,z6])],[(0,[z50,z21,z3,z54,z5,z6]),(0,[z711,z3,z4,z5,z48,z6]),(0,[z292,z3,z152,z4,z5,z6])],[(0,[z159,z2,z3,z4,z190,z6]),(0,[z0,z2,z3,z54,z535,z6]),(0,[z0,z3,z620,z4,z48,z6])],[(0,[z0,z2,z3,z1172,z5,z6])],[(0,[z0,z17,z3,z4,z640,z6]),(0,[z0,z2,z3,z1000,z5,z6])],[(0,[z0,z2,z3,z4,z317,z6]),(0,[z0,z2,z3,z513,z5,z256])],[(0,[z0,z2,z3,z1173,z4,z5]),(0,[z0,z2,z3,z4,z5,z223]),(0,[z0,z224,z3,z4,z5,z6])],[(0,[z0,z36,z3,z385,z48,z6]),(0,[z0,z1174,z3,z4,z5,z6]),(0,[z0,z3,z4,z369,z5,z13])]]

def bk1_24 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z1175,z5,z6]),(0,[z0,z3,z46,z5,z48,z6])],[(0,[z0,z2,z3,z182,z317,z6])],[(0,[z0,z2,z3,z184,z317,z6])],[(0,[z12,z0,z3,z4,z345,z6]),(0,[z53,z70,z3,z4,z5,z6]),(0,[z0,z1176,z3,z4,z5,z6]),(0,[z0,z230,z3,z4,z243,z6]),(0,[z0,z3,z4,z5,z1177,z6]),(0,[z0,z3,z4,z5,z6,z324])],[(0,[z0,z2,z3,z1178,z5,z6]),(0,[z0,z3,z629,z4,z48,z6])],[(0,[z0,z2,z1179,z4,z5,z6]),(0,[z0,z3,z438,z385,z5,z6])],[(0,[z280,z66,z3,z4,z5,z6]),(0,[z0,z1180,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z895])],[(0,[z26,z2,z3,z4,z5,z27]),(0,[z50,z21,z3,z40,z5,z6]),(0,[z0,z2,z3,z1181,z5,z6]),(0,[z0,z2,z3,z513,z34,z6]),(0,[z0,z2,z3,z1182,z5,z6]),(0,[z0,z3,z4,z704,z48,z6])],[(0,[z0,z2,z3,z1183,z5,z6]),(0,[z0,z2,z3,z40,z535,z6]),(0,[z0,z3,z4,z5,z48,z256])],[(0,[z0,z2,z3,z1184,z5,z6]),(0,[z0,z2,z3,z1185,z5,z6]),(0,[z0,z3,z54,z163,z48,z6]),(0,[z0,z3,z706,z4,z48,z6])],[(0,[z50,z292,z3,z4,z5,z6])],[],[(0,[z159,z224,z3,z4,z5,z6]),(0,[z0,z17,z3,z158,z5,z6])],[(0,[z0,z2,z3,z4,z1186,z6]),(0,[z0,z3,z20,z4,z48,z6])],[(0,[z0,z141,z3,z142,z48,z6]),(0,[z0,z1187,z3,z4,z5,z6]),(0,[z0,z2,z3,z1188,z5,z6])],[(0,[z0,z17,z3,z22,z5,z6]),(0,[z0,z17,z3,z4,z5,z1081]),(0,[z0,z1189,z3,z4,z5,z6]),(0,[z0,z200,z3,z4,z146,z6]),(0,[z0,z2,z3,z4,z5,z1190])]]

def bk1_25 : List (List (ℕ × List W)) :=
  [[(0,[z1191,z2,z3,z4,z5,z6]),(0,[z0,z17,z3,z4,z179,z6]),(0,[z0,z2,z3,z4,z5,z1192])],[(0,[z0,z17,z3,z1083,z5,z6])],[(0,[z0,z2,z3,z1193,z5,z6]),(0,[z0,z3,z913,z4,z5,z6]),(0,[z0,z3,z163,z385,z48,z6])],[(0,[z0,z2,z3,z1194,z5,z6]),(0,[z0,z2,z3,z4,z345,z6]),(0,[z0,z3,z463,z40,z48,z6]),(0,[z0,z3,z4,z5,z247,z6])],[(0,[z0,z2,z684,z40,z5,z6]),(0,[z0,z2,z3,z1163,z5,z6]),(0,[z0,z2,z3,z4,z1195,z6]),(0,[z0,z3,z4,z71,z143,z6])],[(0,[z180,z2,z3,z4,z5,z27]),(0,[z0,z1196,z3,z4,z5,z6]),(0,[z0,z3,z158,z5,z48,z6]),(0,[z2,z785,z3,z4,z5,z6])],[(0,[z552,z0,z3,z4,z5,z228]),(0,[z0,z16,z3,z4,z179,z6]),(0,[z0,z251,z3,z4,z5,z6]),(0,[z0,z31,z3,z4,z345,z6]),(0,[z0,z2,z3,z4,z1197,z6])],[(0,[z0,z68,z3,z4,z71,z6]),(0,[z0,z3,z4,z646,z48,z6])],[(0,[z0,z17,z3,z4,z404,z6]),(0,[z2,z3,z45,z4,z367,z6]),(0,[z2,z3,z40,z5,z6,z1096])],[(0,[z0,z2,z3,z1198,z5,z6]),(0,[z0,z2,z3,z4,z5,z1199])],[(0,[z0,z17,z3,z33,z5,z6]),(0,[z0,z2,z3,z1200,z5,z6]),(0,[z0,z1201,z3,z4,z5,z6])],[(0,[z0,z17,z3,z4,z5,z41]),(0,[z0,z437,z3,z4,z535,z6])],[(0,[z0,z230,z3,z4,z5,z6]),(0,[z0,z928,z3,z40,z5,z6]),(0,[z0,z3,z4,z5,z746,z6])],[(0,[z0,z374,z3,z4,z345,z6]),(0,[z0,z2,z3,z4,z5,z1202]),(0,[z0,z1203,z3,z4,z5,z6]),(0,[z0,z1204,z3,z4,z5,z6])],[(0,[z0,z452,z3,z4,z48,z6]),(0,[z0,z2,z3,z4,z5,z1205]),(0,[z0,z3,z4,z317,z1206,z6]),(0,[z0,z3,z40,z5,z75,z6])],[(0,[z0,z363,z3,z4,z5,z6]),(0,[z0,z3,z57,z54,z48,z6])]]

def bk1_26 : List (List (ℕ × List W)) :=
  [[(0,[z0,z366,z2,z3,z5,z6])],[(0,[z0,z1207,z3,z4,z5,z6])],[(0,[z454,z0,z3,z54,z5,z6]),(0,[z0,z17,z3,z4,z443,z6]),(0,[z0,z17,z3,z1101,z5,z6]),(0,[z0,z241,z3,z4,z5,z107]),(0,[z0,z2,z3,z1208,z5,z6]),(0,[z0,z2,z3,z4,z1209,z6]),(0,[z1210,z2,z3,z4,z5,z6])],[(0,[z0,z937,z3,z40,z5,z6]),(0,[z0,z2,z3,z1211,z5,z6]),(0,[z0,z3,z153,z385,z48,z6]),(0,[z0,z3,z859,z5,z48,z6])],[(0,[z0,z3,z880,z4,z5,z6])],[(0,[z0,z17,z3,z385,z48,z6]),(0,[z144,z2,z3,z4,z5,z60])],[(0,[z0,z1212,z3,z4,z5,z6]),(0,[z0,z2,z3,z54,z5,z409]),(0,[z0,z2,z3,z277,z5,z6]),(0,[z0,z2,z3,z4,z1213,z6]),(0,[z0,z2,z3,z4,z190,z60]),(0,[z0,z68,z3,z4,z5,z135]),(0,[z0,z1214,z3,z4,z5,z6])],[(0,[z0,z1215,z3,z4,z5,z6]),(0,[z0,z2,z3,z215,z5,z6]),(0,[z0,z2,z3,z4,z5,z1073]),(0,[z0,z1216,z3,z4,z5,z6]),(0,[z0,z3,z4,z535,z48,z6]),(0,[z0,z3,z4,z143,z101,z6])],[(0,[z0,z21,z3,z4,z179,z6]),(0,[z0,z3,z981,z4,z5,z48])],[(0,[z0,z2,z3,z4,z1217,z6])],[(0,[z0,z2,z3,z4,z1218,z6]),(0,[z0,z3,z4,z5,z1206,z6])],[(0,[z0,z2,z3,z1219,z5,z6]),(0,[z0,z2,z3,z40,z5,z945]),(0,[z1220,z2,z3,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z1221,z6]),(0,[z0,z2,z3,z5,z1222,z6])],[(0,[z0,z1223,z3,z4,z5,z6]),(0,[z0,z3,z1224,z4,z5,z6])],[(0,[z0,z17,z3,z103,z5,z6]),(0,[z0,z2,z3,z4,z930,z6]),(0,[z0,z3,z4,z5,z784,z6]),(0,[z0,z54,z40,z5,z48,z6])]]

def bk1_27 : List (List (ℕ × List W)) :=
  [[(0,[z454,z0,z3,z40,z5,z6]),(0,[z0,z2,z3,z4,z5,z1225]),(0,[z0,z1226,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z83,z6])],[(0,[z0,z1227,z3,z4,z5,z6]),(0,[z0,z1228,z3,z4,z5,z6]),(0,[z0,z3,z1229,z4,z5,z6]),(0,[z292,z2,z3,z54,z5,z6])],[(0,[z0,z272,z3,z54,z5,z6])],[(0,[z0,z251,z3,z4,z146,z6])],[(0,[z47,z3,z4,z97,z48,z6]),(0,[z0,z2,z321,z40,z5,z6]),(0,[z0,z2,z3,z4,z5,z393]),(0,[z0,z2,z3,z40,z958,z6]),(0,[z1230,z2,z3,z4,z5,z6])],[(0,[z159,z2,z3,z4,z5,z6]),(0,[z0,z1231,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1232]),(0,[z0,z3,z681,z4,z48,z6])],[(0,[z0,z17,z3,z4,z243,z6]),(0,[z0,z305,z3,z54,z5,z6]),(0,[z0,z2,z3,z4,z5,z757])],[(0,[z0,z2,z3,z4,z5,z1095]),(0,[z0,z224,z3,z4,z5,z60]),(0,[z0,z3,z54,z5,z941,z6])],[(0,[z0,z2,z3,z4,z5,z1233]),(0,[z0,z2,z3,z182,z5,z393]),(0,[z0,z1234,z3,z4,z5,z6]),(0,[z0,z401,z3,z4,z5,z6])],[(0,[z0,z230,z3,z4,z146,z6]),(0,[z0,z2,z3,z379,z5,z170]),(0,[z0,z2,z3,z184,z5,z393]),(0,[z292,z2,z3,z4,z34,z6])],[(0,[z0,z17,z3,z4,z5,z1129]),(0,[z0,z2,z3,z4,z1235,z6]),(0,[z0,z2,z3,z1236,z5,z6])],[(1,[z0,z3,z4,z1089,z6])],[(0,[z114,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z769]),(0,[z0,z2,z3,z368,z5,z409]),(0,[z0,z2,z3,z314,z5,z6])],[(0,[z0,z963,z3,z4,z5,z6]),(0,[z0,z366,z2,z3,z146,z6])],[(0,[z0,z2,z3,z264,z5,z6]),(0,[z0,z3,z4,z693,z48,z6])]]

def bk1_28 : List (List (ℕ × List W)) :=
  [[(0,[z292,z2,z3,z40,z5,z6])],[(0,[z0,z272,z3,z40,z5,z6])],[(0,[z0,z1237,z3,z4,z5,z6]),(0,[z0,z3,z368,z5,z48,z6]),(0,[z0,z3,z1056,z5,z48,z6])],[(0,[z0,z1238,z3,z4,z5,z6])],[(0,[z0,z415,z3,z4,z5,z6]),(0,[z0,z962,z3,z5,z48,z6]),(0,[z0,z876,z3,z5,z48,z6])],[(0,[z0,z305,z3,z40,z5,z6]),(0,[z0,z2,z3,z1239,z5,z6]),(0,[z2,z3,z4,z5,z1124,z6])],[(0,[z164,z0,z4,z48,z101,z6]),(0,[z0,z3,z4,z97,z48,z6])],[(0,[z0,z17,z3,z165,z5,z6])],[(0,[z0,z69,z272,z3,z5,z6]),(0,[z0,z213,z3,z54,z48,z6]),(0,[z0,z31,z110,z323,z5,z6]),(0,[z0,z2,z3,z4,z326,z6])],[(0,[z26,z2,z3,z215,z5,z27])],[(0,[z0,z2,z3,z1140,z40,z6]),(0,[z0,z2,z3,z4,z1240,z6])],[(0,[z0,z119,z3,z4,z5,z756]),(0,[z0,z2,z3,z1241,z5,z6]),(0,[z0,z2,z3,z28,z5,z223]),(0,[z0,z1242,z3,z4,z5,z6]),(0,[z0,z3,z430,z4,z48,z6])],[(0,[z0,z1091,z2,z3,z5,z6]),(0,[z0,z1243,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1244,z5,z6]),(0,[z0,z2,z3,z4,z317,z393]),(0,[z275,z17,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1245,z6]),(0,[z0,z1246,z3,z4,z5,z6]),(0,[z0,z3,z40,z5,z143,z6]),(0,[z144,z2,z3,z296,z5,z6])],[(0,[z0,z69,z3,z55,z326,z6]),(0,[z0,z2,z3,z296,z190,z6]),(0,[z0,z3,z10,z4,z48,z6]),(0,[z0,z3,z237,z5,z48,z6]),(0,[z0,z3,z4,z142,z48,z6]),(0,[z0,z3,z4,z5,z48,z829])]]

def bk1_29 : List (List (ℕ × List W)) :=
  [[(0,[z1247,z2,z3,z4,z5,z6]),(0,[z0,z17,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z1089,z6])],[(0,[z1248,z0,z2,z3,z5,z6]),(0,[z0,z3,z4,z5,z48,z311])],[(0,[z14,z2,z3,z521,z5,z6]),(0,[z0,z2,z3,z4,z5,z1249])],[(0,[z0,z119,z3,z4,z5,z662]),(0,[z0,z2,z176,z40,z5,z6]),(0,[z0,z3,z4,z761,z48,z6]),(0,[z0,z3,z4,z145,z48,z6])],[(0,[z0,z17,z3,z182,z5,z6]),(0,[z0,z17,z54,z40,z5,z6]),(0,[z275,z2,z3,z4,z5,z135])],[(0,[z0,z17,z3,z184,z5,z6]),(0,[z0,z366,z3,z97,z48,z6]),(0,[z0,z318,z3,z4,z48,z6]),(0,[z0,z2,z3,z1250,z5,z6]),(0,[z0,z2,z3,z804,z4,z5]),(0,[z0,z2,z3,z1251,z5,z6]),(0,[z0,z3,z4,z48,z6,z685])],[(0,[z0,z160,z3,z4,z48,z6]),(0,[z0,z3,z201,z4,z48,z6]),(0,[z0,z3,z4,z38,z48,z6]),(0,[z0,z3,z4,z5,z1252,z6]),(0,[z144,z17,z3,z4,z5,z6])],[(0,[z0,z17,z3,z4,z190,z6]),(0,[z0,z89,z3,z57,z4,z48]),(0,[z0,z2,z3,z1253,z5,z6]),(0,[z0,z2,z3,z4,z287,z6]),(0,[z0,z2,z3,z4,z5,z135]),(0,[z0,z2,z3,z4,z5,z1254]),(0,[z0,z2,z3,z4,z6,z943]),(1,[z0,z3,z381,z48,z6])],[(0,[z0,z2,z3,z4,z1255,z6]),(0,[z0,z2,z3,z4,z5,z1078]),(0,[z0,z3,z4,z5,z1256,z6])],[(0,[z0,z2,z3,z1257,z5,z6]),(0,[z0,z3,z57,z4,z48,z58]),(0,[z0,z3,z4,z5,z1258,z6])],[(0,[z0,z1041,z3,z4,z5,z6]),(0,[z0,z262,z3,z40,z5,z6])],[(0,[z0,z70,z3,z4,z5,z41]),(0,[z0,z3,z4,z211,z48,z6])],[(0,[z0,z139,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1259]),(0,[z0,z2,z3,z1260,z5,z6]),(0,[z1261,z2,z3,z4,z5,z6])],[(0,[z0,z408,z3,z386,z5,z6]),(0,[z0,z36,z2,z3,z266,z6]),(0,[z0,z2,z3,z1262,z4,z6]),(0,[z0,z3,z4,z97,z75,z6])],[(0,[z0,z2,z3,z1263,z5,z6]),(0,[z0,z2,z3,z1264,z5,z6]),(0,[z0,z68,z3,z4,z101,z6]),(0,[z0,z3,z4,z48,z698,z6])],[(0,[z0,z36,z3,z54,z48,z6]),(0,[z0,z2,z3,z1265,z5,z6]),(0,[z0,z2,z3,z1266,z5,z6])]]

def bk1_30 : List (List (ℕ × List W)) :=
  [[(0,[z1267,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1268]),(0,[z0,z2,z3,z4,z1089,z6]),(0,[z0,z2,z3,z1269,z5,z6]),(0,[z0,z2,z3,z732,z5,z6])],[(0,[z26,z2,z3,z264,z5,z27]),(0,[z0,z224,z3,z296,z5,z6]),(0,[z0,z3,z954,z5,z48,z6])],[(0,[z0,z2,z3,z4,z1270,z6]),(0,[z0,z3,z1120,z5,z48,z6]),(0,[z1271,z2,z3,z4,z5,z6])],[(0,[z0,z2,z540,z40,z5,z6]),(0,[z0,z2,z3,z4,z367,z6]),(0,[z0,z2,z3,z4,z1272,z6]),(0,[z0,z2,z3,z1273,z5,z6]),(0,[z0,z2,z3,z1274,z5,z6])],[(0,[z0,z240,z3,z4,z48,z6])],[(0,[z0,z905,z3,z4,z5,z6]),(0,[z0,z2,z3,z1275,z5,z6]),(0,[z0,z2,z3,z1276,z5,z6]),(0,[z0,z3,z4,z48,z101,z6])],[(0,[z0,z1277,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1278,z6]),(0,[z0,z2,z3,z182,z367,z6])],[(0,[z0,z17,z3,z4,z317,z6]),(0,[z0,z2,z3,z184,z367,z6]),(0,[z0,z2,z3,z1279,z5,z6]),(0,[z0,z2,z106,z54,z5,z6])],[(0,[z0,z17,z3,z4,z5,z223]),(0,[z0,z2,z3,z1280,z5,z6]),(0,[z0,z2,z3,z1281,z5,z6])],[(0,[z0,z2,z3,z425,z5,z409]),(0,[z0,z2,z3,z4,z1282,z6]),(0,[z0,z2,z3,z1283,z5,z6]),(0,[z0,z2,z3,z1284,z5,z6]),(0,[z0,z110,z880,z4,z5,z6]),(0,[z0,z3,z40,z5,z6,z324]),(0,[z3,z842,z4,z5,z48,z6])],[(0,[z12,z0,z3,z4,z5,z61]),(0,[z0,z350,z3,z40,z48,z6]),(0,[z0,z2,z3,z4,z1018,z6]),(0,[z0,z2,z3,z264,z5,z27]),(0,[z0,z2,z3,z40,z5,z41]),(0,[z0,z3,z106,z4,z48,z6])],[(0,[z0,z2,z3,z1285,z5,z6]),(0,[z0,z401,z3,z57,z4,z6])],[(0,[z0,z36,z3,z40,z48,z6]),(0,[z0,z1286,z3,z4,z5,z6]),(0,[z0,z2,z3,z156,z326,z6]),(0,[z0,z1287,z3,z4,z5,z6])],[(0,[z0,z17,z3,z4,z146,z6]),(0,[z0,z2,z3,z1288,z5,z6])],[(0,[z0,z17,z3,z1178,z5,z6]),(0,[z0,z1289,z3,z4,z5,z6]),(0,[z0,z2,z3,z1290,z5,z6]),(0,[z0,z3,z54,z5,z319,z6])]]

def bk1_31 : List (List (ℕ × List W)) :=
  [[(0,[z0,z810,z3,z4,z5,z6])],[(0,[z0,z2,z1291,z4,z5,z6]),(0,[z878,z3,z4,z5,z48,z6])],[(0,[z26,z17,z3,z4,z5,z27]),(0,[z108,z2,z3,z54,z5,z6]),(0,[z0,z120,z3,z4,z48,z6])],[(0,[z0,z1292,z3,z4,z5,z6]),(0,[z0,z2,z3,z1293,z5,z6]),(0,[z0,z2,z3,z1294,z5,z6]),(0,[z0,z3,z128,z4,z48,z6])],[(0,[z0,z69,z141,z3,z5,z6]),(0,[z0,z1008,z3,z4,z5,z6]),(0,[z0,z3,z134,z4,z48,z6])],[(0,[z0,z141,z3,z163,z48,z6]),(0,[z0,z2,z3,z1295,z5,z6]),(0,[z0,z2,z3,z4,z1296,z6]),(0,[z0,z2,z3,z385,z5,z6])],[],[(0,[z0,z1297,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1053]),(0,[z0,z3,z1161,z5,z48,z6])],[(0,[z0,z2,z3,z4,z1031,z6])],[(0,[z0,z1298,z3,z4,z5,z6])],[(0,[z0,z2,z3,z323,z5,z6]),(0,[z0,z2,z3,z4,z767,z6]),(0,[z0,z1299,z3,z4,z5,z6]),(0,[z0,z3,z40,z5,z247,z6])],[(0,[z0,z119,z3,z54,z5,z107]),(0,[z0,z2,z3,z381,z48,z6]),(0,[z0,z2,z3,z4,z1300,z6]),(0,[z0,z2,z3,z4,z5,z61])],[(0,[z0,z2,z3,z1173,z4,z6])],[(0,[z0,z2,z3,z4,z1301,z6]),(0,[z0,z2,z3,z4,z1302,z6]),(0,[z0,z2,z3,z5,z1303,z6]),(0,[z0,z3,z55,z707,z5,z6])],[(0,[z0,z17,z3,z4,z345,z6]),(0,[z0,z31,z3,z4,z5,z61]),(0,[z0,z2,z3,z4,z5,z1021])],[(0,[z0,z3,z4,z515,z48,z6])]]

def bk1 : List (List (List (ℕ × List W))) :=
  [bk1_0, bk1_1, bk1_2, bk1_3, bk1_4, bk1_5, bk1_6, bk1_7, bk1_8, bk1_9, bk1_10, bk1_11, bk1_12, bk1_13, bk1_14, bk1_15, bk1_16, bk1_17, bk1_18, bk1_19, bk1_20, bk1_21, bk1_22, bk1_23, bk1_24, bk1_25, bk1_26, bk1_27, bk1_28, bk1_29, bk1_30, bk1_31]

def bk2_0 : List (List (ℕ × List W)) :=
  [[(0,[z0,z831,z3,z48,z6]),(0,[z0,z3,z48,z6,z943])],[(0,[z0,z3,z413,z326,z6]),(0,[z0,z106,z54,z48,z6])],[(0,[z0,z789,z3,z48,z6]),(0,[z0,z953,z3,z48,z6]),(0,[z0,z3,z1083,z48,z6]),(0,[z0,z3,z4,z1304,z6]),(0,[z0,z3,z1305,z1089,z6])],[(0,[z0,z1045,z3,z48,z6]),(0,[z0,z1038,z3,z48,z6]),(0,[z275,z2,z40,z101,z6])]]

def bk2_1 : List (List (ℕ × List W)) :=
  [[(0,[z0,z3,z54,z1089,z6]),(0,[z0,z3,z40,z734,z6]),(0,[z0,z3,z1306,z734,z6]),(0,[z0,z722,z4,z48,z6]),(0,[z160,z2,z3,z5,z223])],[(0,[z0,z3,z4,z712,z48])],[(0,[z0,z964,z3,z48,z6]),(0,[z0,z3,z4,z243,z756]),(0,[z0,z3,z4,z734,z6])],[(0,[z0,z3,z54,z791,z48]),(0,[z3,z4,z767,z48,z6])]]

def bk2_2 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1142,z3,z48,z6]),(0,[z0,z3,z707,z123,z6])],[(0,[z0,z3,z1307,z5,z6]),(0,[z0,z3,z4,z48,z1129])],[(0,[z0,z3,z866,z48,z6])],[(0,[z0,z3,z4,z179,z757])]]

def bk2_3 : List (List (ℕ × List W)) :=
  [[(0,[z0,z3,z1293,z48,z6]),(0,[z0,z3,z1194,z48,z6]),(0,[z0,z3,z4,z179,z61]),(0,[z0,z3,z4,z1308,z6])],[(0,[z760,z2,z3,z379,z5]),(0,[z0,z1309,z3,z1089,z6]),(0,[z0,z749,z3,z48,z6]),(0,[z0,z3,z1310,z48,z6])],[(0,[z0,z141,z3,z761,z6]),(0,[z0,z3,z1250,z48,z6]),(0,[z0,z3,z4,z1311,z6])],[(0,[z0,z1312,z3,z48,z6]),(0,[z0,z3,z381,z48,z6]),(0,[z0,z3,z1170,z48,z6]),(0,[z0,z3,z40,z1089,z6])]]

def bk2_4 : List (List (ℕ × List W)) :=
  [[(0,[z26,z2,z3,z1219,z5]),(0,[z0,z3,z4,z345,z228]),(0,[z292,z3,z4,z1089,z6])],[(0,[z225,z2,z3,z804,z5]),(0,[z0,z1313,z3,z734,z6]),(0,[z0,z1099,z3,z48,z6]),(0,[z0,z3,z826,z48,z6]),(0,[z0,z3,z48,z6,z1314]),(0,[z0,z4,z48,z869,z6]),(0,[z0,z40,z48,z403,z6])],[(0,[z0,z3,z54,z1304,z6]),(0,[z0,z3,z1034,z48,z6])],[(0,[z0,z3,z1200,z48,z6]),(0,[z0,z3,z1315,z4,z5])]]

def bk2_5 : List (List (ℕ × List W)) :=
  [[(0,[z0,z141,z3,z326,z6]),(0,[z0,z3,z4,z1089,z6])],[(0,[z0,z3,z5,z6,z1316]),(0,[z292,z3,z4,z179,z6])],[(0,[z0,z3,z54,z734,z6])],[(0,[z0,z3,z4,z791,z48])]]

def bk2_6 : List (List (ℕ × List W)) :=
  [[(0,[z0,z141,z3,z48,z1081]),(0,[z0,z3,z4,z5,z1317])],[],[(0,[z0,z3,z1318,z48,z6]),(0,[z423,z3,z4,z179,z6])],[(0,[z14,z160,z3,z48,z6]),(0,[z1248,z0,z3,z48,z6])]]

def bk2_7 : List (List (ℕ × List W)) :=
  [[(0,[z0,z36,z3,z48,z223]),(0,[z1261,z3,z4,z48,z6])],[(0,[z0,z2,z40,z101,z135]),(0,[z0,z3,z4,z48,z1081]),(0,[z1319,z3,z4,z5,z6])],[(0,[z0,z366,z3,z48,z6]),(0,[z0,z3,z758,z48,z6]),(0,[z0,z54,z472,z48,z6]),(0,[z3,z4,z5,z1320,z6])],[(0,[z0,z3,z1173,z4,z48]),(0,[z0,z3,z4,z1321,z6])]]

def bk2 : List (List (List (ℕ × List W))) :=
  [bk2_0, bk2_1, bk2_2, bk2_3, bk2_4, bk2_5, bk2_6, bk2_7]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fin0 : chunkOK 4 ((bk2.flatten.drop 0).take 32).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem finend : (bk2.flatten.drop 32).isEmpty = true := by
  decide +kernel

theorem winF : windowsF 4 bk2.flatten 0 [32] = true :=
  windowsF_cons fin0 (windowsF_nil finend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t1w0 : chunkB (fun c => !inB2 4 32 bk2 c) 1 ((bk1.flatten.flatten.drop 0).take 400) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t1w1 : chunkB (fun c => !inB2 4 32 bk2 c) 1 ((bk1.flatten.flatten.drop 400).take 400) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t1w2 : chunkB (fun c => !inB2 4 32 bk2 c) 1 ((bk1.flatten.flatten.drop 800).take 400) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t1w3 : chunkB (fun c => !inB2 4 32 bk2 c) 1 ((bk1.flatten.flatten.drop 1200).take 321) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t1wend : (bk1.flatten.flatten.drop 1521).isEmpty = true := by
  decide +kernel

theorem win1 : windowsG (chunkB (fun c => !inB2 4 32 bk2 c) 1) bk1.flatten.flatten 0 [400, 400, 400, 321] = true :=
  windowsG_cons t1w0 (windowsG_cons t1w1 (windowsG_cons t1w2 (windowsG_cons t1w3 (windowsG_nil t1wend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t0w0 : chunkB (fun c => !inB2 16 512 bk1 c) 1 ((bk0.flatten.flatten.drop 0).take 400) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t0w1 : chunkB (fun c => !inB2 16 512 bk1 c) 1 ((bk0.flatten.flatten.drop 400).take 400) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t0w2 : chunkB (fun c => !inB2 16 512 bk1 c) 1 ((bk0.flatten.flatten.drop 800).take 400) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t0w3 : chunkB (fun c => !inB2 16 512 bk1 c) 1 ((bk0.flatten.flatten.drop 1200).take 196) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t0wend : (bk0.flatten.flatten.drop 1396).isEmpty = true := by
  decide +kernel

theorem win0 : windowsG (chunkB (fun c => !inB2 16 512 bk1 c) 1) bk0.flatten.flatten 0 [400, 400, 400, 196] = true :=
  windowsG_cons t0w0 (windowsG_cons t0w1 (windowsG_cons t0w2 (windowsG_cons t0w3 (windowsG_nil t0wend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pw0 : chunkB (fun c => !inB2 16 512 bk0 c) 2 (((level0 8 rows).drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pwend : ((level0 8 rows).drop 1).isEmpty = true := by
  decide +kernel

theorem winP : windowsG (chunkB (fun c => !inB2 16 512 bk0 c) 2) (level0 8 rows) 0 [1] = true :=
  windowsG_cons pw0 (windowsG_nil pwend)

theorem reject : search 8 rows = false := by
  have h2 : FalseAt 4 bk2.flatten.flatten := finalF winF
  have h1 : FalseAt 5 bk1.flatten.flatten := tierB (by norm_num) (memS h2) win1
  have h0 : FalseAt 6 bk0.flatten.flatten := tierB (by norm_num) (memS h1) win0
  have hP : FalseAt 8 (level0 8 rows) := tierB (by norm_num) (memS h0) winP
  exact search_of_false hP

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

end PEqualNP.Outside.L_meta_37577

theorem PEqualNP.Outside.L_meta_37577 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276791464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276791464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37577.solve
