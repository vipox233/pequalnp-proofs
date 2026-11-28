import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38591

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
  Nat.testBit (4276677352 * 2 ^ 32 + 4008225448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x100045021404284a#64 ++ 0x080022810a021425#64 ++ 0xef00cf1e3c8c7fff#64 ++ 0xf780678f1e463fff#64 : BitVec 256),
   (0x60031268c9319525#64 ++ 0xb00189346498ca92#64 ++ 0xdf8733e9cf739d27#64 ++ 0xefc399f4e7b9ce93#64 : BitVec 256),
   (0x403828b16382c631#64 ++ 0x201c1458b1c16318#64 ++ 0xbb783cf1f383e639#64 ++ 0xddbc1e78f9c1f31c#64 : BitVec 256),
   (0x805d80fc03d80781#64 ++ 0xc02ec07e01ec03c0#64 ++ 0x7cffc0fe03fc07c1#64 ++ 0xbe7fe07f01fe03e0#64 : BitVec 256),
   (0x01eeff0002ef7800#64 ++ 0x00f77f800177bc00#64 ++ 0xfdffff0003fff801#64 ++ 0x7effff8001fffc00#64 : BitVec 256),
   (0x02f7ffdfbc000000#64 ++ 0x017bffefde000000#64 ++ 0xfafffffffc000000#64 ++ 0xfd7ffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [9, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000214000000 0x000000010a000000 0x0200001e3c000000 0x8100000f1e000000

def z1 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xfdffff0003fff801 0x7effff8001fffc00

def z2 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfafffffffc000000 0xfd7ffffffe000000

def z3 : W := mkw 0x100045021404284a 0x080022810a021425 0xef00cf1e3c8c7fff 0xf780678f1e463fff

def z4 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xbb783cf1f383e639 0xddbc1e78f9c1f31c

def z5 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xdf8733e9cf739d27 0xefc399f4e7b9ce93

def z6 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x7cffc0fe03fc07c1 0xbe7fe07f01fe03e0

def z7 : W := mkw 0x0028280002824000 0x0014140001412000 0xb9783c000383e001 0x5cbc1e0001c1f000

def z8 : W := mkw 0x801100fc01100781 0xc008807e008803c0 0x000000fe000007c0 0x8000007f000003e0

def z9 : W := mkw 0x0030289120000000 0x0018144890000000 0xba783cf1f0000000 0xdd3c1e78f8000000

def z10 : W := mkw 0x807da8fd23d80781 0xc03ed47e91ec03c0 0xfefffcfff3fc07c1 0xff7ffe7ff9fe03e0

def z11 : W := mkw 0x100045021404284a 0x080022810a021425 0x2000cc16308c62d8 0x1000660b1846316c

def z12 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x108730e1c3738000 0x08439870e1b9c000

def z13 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200001030000638 0x810000081800031c

def z14 : W := mkw 0x400800204382c631 0x2004001021c16318 0x0000000003038000 0x000000000181c000

def z15 : W := mkw 0x1003574a9c04284a 0x0801aba54e021425 0xff87fffffc8c7fff 0xffc3fffffe463fff

def z16 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x30783cf1f383e218 0x183c1e78f9c1f10c

def z17 : W := mkw 0x001800b003800601 0x000c005801c00300 0x387800f003800601 0x9c3c007801c00300

def z18 : W := mkw 0xc07da8fd63dac7b1 0xe03ed47eb1ed63d8 0xfffffcfff3ffe7f9 0xfffffe7ff9fff3fc

def z19 : W := mkw 0x021100dfbc000000 0x0108806fde000000 0x020000fffc000000 0x8100007ffe000000

def z20 : W := mkw 0x02f4ed9734000000 0x017a76cb9a000000 0x2078cc1630000000 0x103c660b18000000

def z21 : W := mkw 0x11eced0216ce684a 0x08f676810b673425 0xef78cf1e3c8c7fff 0xf7bc678f1e463fff

def z22 : W := mkw 0x005580dc00000000 0x002ac06e00000000 0x78ffc0fe00000000 0xbc7fe07f00000000

def z23 : W := mkw 0x8008002003d80781 0xc004001001ec03c0 0x0400000003fc07c1 0x0200000001fe03e0

def z24 : W := mkw 0x004c800002c80000 0x0026400001640000 0x7cffc00003fc0001 0x3e7fe00001fe0000

def z25 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfefffffffc0c19c6 0xff7ffffffe060ce3

def z26 : W := mkw 0x603b3af9ebb3d735 0xb01d9d7cf5d9eb9a 0xdfff33e9cf739d27 0xefff99f4e7b9ce93

def z27 : W := mkw 0x6008002043b3d735 0xb004001021d9eb9a 0x0500000003f3ff3f 0x0280000001f9ff9f

def z28 : W := mkw 0x01a27f0000277800 0x00d13f800013bc00 0x81003f000003f800 0x40801f800001fc00

def z29 : W := mkw 0x005580dc00000000 0x002ac06e00000000 0x10ff00e000000000 0x087f807000000000

def z30 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x10ff30e1c0000000 0x087f9870e0000000

def z31 : W := mkw 0x003828b123824611 0x001c145891c12308 0x38780cf033806619 0x9c3c067819c0330c

def z32 : W := mkw 0x11a27f021427784a 0x08d13f810a13bc25 0xef00ff1e3c8fffff 0xf7807f8f1e47ffff

def z33 : W := mkw 0x41eeff2043effe31 0x20f77f9021f7ff18 0xfdffff0003fffe39 0x7effff8001ffff1c

def z34 : W := mkw 0x400800204382c631 0x2004001021c16318 0x9b0030e1c383e639 0xcd801870e1c1f31c

def z35 : W := mkw 0x2003124888311104 0x9001892444188882 0x448703080c701906 0x2243818406380c83

def z36 : W := mkw 0x22f7ffdfbc311104 0x917bffefde188882 0xfefffffffc701906 0xff7ffffffe380c83

def z37 : W := mkw 0x0000450214000000 0x000022810a000000 0xea00cf1e3c000000 0xf500678f1e000000

def z38 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xffffff1e3fffffff 0xffffff8f1fffffff

def z39 : W := mkw 0x0028280002824000 0x0014140001412000 0x20780c0000806000 0x103c060000403000

def z40 : W := mkw 0x0000450214000000 0x000022810a000000 0xee00cf1e3c8c07c1 0xf700678f1e4603e0

def z41 : W := mkw 0x0000000000000000 0x0000000000000000 0xcf0003080c001d27 0xe780018406000e93

def z42 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0xffffc3fe0ffc1fe7 0xffffe1ff07fe0ff3

def z43 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x10ff300003738000 0x087f980001b9c000

def z44 : W := mkw 0x41febab163ebd631 0x20ff5d58b1f5eb18 0xbbff3cf1f3f3e639 0xddff9e78f9f9f31c

def z45 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfffffffffc8c7fff 0xfffffffffe463fff

def z46 : W := mkw 0x01eced0002ef7800 0x00f676800177bc00 0x2578cc0003fff801 0x12bc660001fffc00

def z47 : W := mkw 0x805c80b403c80681 0x402e405a01e40340 0x3878c0f6038c06c1 0x9c3c607b01c60360

def z48 : W := mkw 0x0001006801100501 0x8000803400880280 0x000000e800000500 0x8000007400000280

def z49 : W := mkw 0x0038289122824210 0x001c144891412108 0x20780c1030806218 0x103c06081840310c

def z50 : W := mkw 0x60e7ff68c9319525 0xb073ffb46498ca92 0xffffffe9cf739d27 0xfffffff4e7b9ce93

def z51 : W := mkw 0x0038289122824210 0x001c144891412108 0xb9783c103383e219 0x5cbc1e0819c1f10c

def z52 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000001e000007c0 0x8000000f000003e0

def z53 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xffffff003ffff83f 0x7fffff801ffffc1f

def z54 : W := mkw 0x3003574a9c35394e 0x9801aba54e1a9ca7 0xef87cf1e3cfc7fff 0xf7c3e78f1e7e3fff

def z55 : W := mkw 0x401800b043808621 0x200c005821c04310 0xbb7830f1c3838621 0xddbc1878e1c1c310

def z56 : W := mkw 0x82c7d74e9c580180 0xc163eba74e2c00c0 0x4487c30e0c7c01c0 0x2243e187063e00e0

def z57 : W := mkw 0x00333ad9a8000000 0x00199d6cd4000000 0xfaff3ff9fc000000 0xfd7f9ffcfe000000

def z58 : W := mkw 0x603b3af9ebb3d735 0xb01d9d7cf5d9eb9a 0xffff3ff9fff3ff3f 0xffff9ffcfff9ff9f

def z59 : W := mkw 0x400800204382c631 0x2004001021c16318 0x010000000383e639 0x0080000001c1f31c

def z60 : W := mkw 0x61efff68cbfffd25 0xb0f7ffb465fffe92 0xffffffe9cffffd27 0xfffffff4e7fffe93

def z61 : W := mkw 0x02e6ff03bc000000 0x01737f81de000000 0xfaffff01fc000000 0x7d7fff80fe000000

def z62 : W := mkw 0x100045021404284a 0x080022810a021425 0x0000c006000c00c0 0x0000600300060060

def z63 : W := mkw 0x00e6ff0000000000 0x00737f8000000000 0xf8ffff0000000000 0x7c7fff8000000000

def z64 : W := mkw 0x13ffffdfbeef784a 0x09ffffefdf77bc25 0xffffffffffffffff 0xffffffffffffffff

def z65 : W := mkw 0x0020280000024000 0x0010140000012000 0x81003c000003e000 0x40801e000001f000

def z66 : W := mkw 0x100000000004284a 0x0800000000021425 0x05000000008c7fff 0x0280000000463fff

def z67 : W := mkw 0x401000b161008631 0x20080058b0804318 0x020000f1f0000638 0x81000078f800031c

def z68 : W := mkw 0x0001006801100501 0x8000803400880280 0x5c8700e803700501 0xae43807401b80280

def z69 : W := mkw 0x60021200c8219024 0x300109006410c812 0x83003301cc039826 0x41801980e601cc13

def z70 : W := mkw 0x801100fc01100781 0xc008807e008803c0 0x6c00c0fe008c07c1 0xb600607f004603e0

def z71 : W := mkw 0x60010068c9108525 0xb000803464884292 0x020000e9cc000526 0x81000074e6000293

def z72 : W := mkw 0x4000002041008421 0x2000001020804210 0x0100000003038421 0x008000000181c210

def z73 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x10ff00e003700000 0x087f807001b80000

def z74 : W := mkw 0x621100fffd108525 0xb108807ffe884292 0x020000fffc000526 0x8100007ffe000293

def z75 : W := mkw 0x010a120002ef7800 0x008509000177bc00 0xdd87330003fff801 0x6ec3998001fffc00

def z76 : W := mkw 0x0000000000042800 0x0000000000021400 0x05000000008c7801 0x0280000000463c00

def z77 : W := mkw 0x7003576add35bd6f 0xb801abb56e9adeb7 0xff87ffffffffffff 0xffc3ffffffffffff

def z78 : W := mkw 0x4000000040008020 0x2000000020004010 0x83003001c0038020 0x41801800e001c010

def z79 : W := mkw 0x02ffffffbf800601 0x017fffffdfc00300 0xfaffffffff800601 0xfd7fffffffc00300

def z80 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x107830e1c3038000 0x083c1870e181c000

def z81 : W := mkw 0x02f4ed9734000000 0x017a76cb9a000000 0xba78fcf7f0000000 0xdd3c7e7bf8000000

def z82 : W := mkw 0x021100dda8000000 0x0108806ed4000000 0x000000e1c0000000 0x00000070e0000000

def z83 : W := mkw 0x11c6d702146d384a 0x08e36b810a369c25 0x4487c30e0c7c19c6 0x2243e187063e0ce3

def z84 : W := mkw 0x0010009000000000 0x0008004800000000 0x387800f000000000 0x9c3c007800000000

def z85 : W := mkw 0x0000000000000000 0x0000000000000000 0xab000c1030806639 0xd58006081840331c

def z86 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x54ffc0ee037c01c0 0x2a7fe07701be00e0

def z87 : W := mkw 0x0000450000042800 0x0000228000021400 0x2000cc00008c6000 0x1000660000463000

def z88 : W := mkw 0x12a27f03bc04284a 0x09513f81de021425 0xef00ff1ffc8c7fff 0xf7807f8ffe463fff

def z89 : W := mkw 0x0038289122824000 0x001c144891412000 0xbb783cf1f383e001 0xddbc1e78f9c1f000

def z90 : W := mkw 0x0000450000042800 0x0000228000021400 0xed00cf00008c7801 0x7680678000463c00

def z91 : W := mkw 0x402028016002c030 0x20101400b0016018 0x83003c01f003e038 0x41801e00f801f01c

def z92 : W := mkw 0x8045804c00580180 0xc022c026002c00c0 0x4487c00e007c01c0 0x2243e007003e00e0

def z93 : W := mkw 0x0044800000000000 0x0022400000000000 0x78ffc00000000000 0x3c7fe00000000000

def z94 : W := mkw 0x01eeff0216ef7800 0x00f77f810b77bc00 0xffffff1e3ffff801 0xffffff8f1ffffc00

def z95 : W := mkw 0x100045021404284a 0x080022810a021425 0x4400c30e0c0c19c6 0x2200618706060ce3

def z96 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xfdffff0e0ffff9c7 0x7effff8707fffce3

def z97 : W := mkw 0xe05f92fccbf997a5 0xf02fc97e65fccbd2 0xfffff3ffcfff9fe7 0xfffff9ffe7ffcff3

def z98 : W := mkw 0x0108000002ef7800 0x008400000177bc00 0x0500000003fff801 0x0280000001fffc00

def z99 : W := mkw 0x0002120000211000 0x0001090000108800 0xdf8733080f739d27 0xefc3998407b9ce93

def z100 : W := mkw 0x905dc5fe17dc2fcb 0xc82ee2ff0bee17e5 0xffffcffe3ffc7fff 0xffffe7ff1ffe3fff

def z101 : W := mkw 0x121100dfbc00004a 0x0908806fde000025 0x020000fffc0007fe 0x8100007ffe0003ff

def z102 : W := mkw 0x402028016002c030 0x20101400b0016018 0x00003001c0038000 0x00001800e001c000

def z103 : W := mkw 0x500800204386ee7b 0x2804001021c3773d 0x05000000038fffff 0x0280000001c7ffff

def z104 : W := mkw 0x50386db37786ee7b 0x281c36d9bbc3773d 0xff78ffffff8fffff 0xffbc7fffffc7ffff

def z105 : W := mkw 0x0000000000211000 0x0000000000108800 0x0500000003739801 0x0280000001b9cc00

def z106 : W := mkw 0x10286d021686684a 0x081436810b433425 0xff78ff1e3f8fffff 0xffbc7f8f1fc7ffff

def z107 : W := mkw 0x0038289122824210 0x001c144891412108 0x0078000000000000 0x003c000000000000

def z108 : W := mkw 0x603b3af9ebb3d735 0xb01d9d7cf5d9eb9a 0xbbff3cf1f3f3e639 0xddff9e78f9f9f31c

def z109 : W := mkw 0x42ffffffff82c631 0x217fffffffc16318 0xfbffffffff83e639 0xfdffffffffc1f31c

def z110 : W := mkw 0x82ffffffbfd80781 0xc17fffffdfec03c0 0xfefffffffffc07c1 0xff7ffffffffe03e0

def z111 : W := mkw 0x004c800002c80000 0x0026400001640000 0x10ff000003700000 0x087f800001b80000

def z112 : W := mkw 0x423928ffff82c631 0x211c947fffc16318 0xbb783cffff83e639 0xddbc1e7fffc1f31c

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0x020000080c000526 0x8100000406000293

def z114 : W := mkw 0x00e6ff0000042800 0x00737f8000021400 0xfdffff00008c7801 0x7effff8000463c00

def z115 : W := mkw 0x0108000002eb5000 0x008400000175a800 0x0000000003738000 0x0000000001b9c000

def z116 : W := mkw 0x0001004888000000 0x0000802444000000 0x020000e9cc000000 0x81000074e6000000

def z117 : W := mkw 0x00e7ff4888000000 0x0073ffa444000000 0xfaffffe9cc000000 0xfd7ffff4e6000000

def z118 : W := mkw 0x402828216382c631 0x20141410b1c16318 0x83003c01f383e639 0x41801e00f9c1f31c

def z119 : W := mkw 0x02c7d74e9c000000 0x0163eba74e000000 0x4087c30e0c000000 0x2043e18706000000

def z120 : W := mkw 0x805580dc00580180 0xc02ac06e002c00c0 0x7cffc0fe007c01c0 0xbe7fe07f003e00e0

def z121 : W := mkw 0x10386d9336866a5a 0x081c36c99b43352d 0xef78cf1e3c8c7fff 0xf7bc678f1e463fff

def z122 : W := mkw 0x0000000000000000 0x0000000000000000 0x6c00c01e008c07c1 0xb600600f004603e0

def z123 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0x92ff3fe1fc000000 0x497f9ff0fe000000

def z124 : W := mkw 0x4001006841108521 0xa000803420884290 0xdf8730e9c3738521 0xefc39874e1b9c290

def z125 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xffffff1033fffe39 0xffffff8819ffff1c

def z126 : W := mkw 0x51feffb377effe7b 0x28ff7fd9bbf7ff3d 0xffffffffffffffff 0xffffffffffffffff

def z127 : W := mkw 0x700045225535bd6f 0xb80022912a9adeb7 0xef00cf1e3fffffff 0xf780678f1fffffff

def z128 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x468703e9cc701d26 0xa34381f4e6380e93

def z129 : W := mkw 0xc03828b163dac7b1 0xe01c1458b1ed63d8 0xbf783cf1f3ffe7f9 0xdfbc1e78f9fff3fc

def z130 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0x50fff3efcc000000 0x287ff9f7e6000000

def z131 : W := mkw 0x02b27f93bc000000 0x01593fc9de000000 0xba783ff1fc000000 0xdd3c1ff8fe000000

def z132 : W := mkw 0x41feffb163effe31 0x20ff7fd8b1f7ff18 0xfffffff1f3fffe39 0xfffffff8f9ffff1c

def z133 : W := mkw 0x02f7ffdfbc211000 0x017bffefde108800 0xffffffffff739801 0xffffffffffb9cc00

def z134 : W := mkw 0x03eeff03beef7800 0x01f77f81df77bc00 0xffffff01fffff801 0x7fffff80fffffc00

def z135 : W := mkw 0x021145dfbc000000 0x0108a2efde000000 0xea00cffffc000000 0xf50067fffe000000

def z136 : W := mkw 0x03f7ffdfbc277800 0x01fbffefde13bc00 0xfbfffffffc03f800 0xfdfffffffe01fc00

def z137 : W := mkw 0x0020280000000000 0x0010140000000000 0xb8783c0000000000 0x5c3c1e0000000000

def z138 : W := mkw 0xc008002043dac7b1 0xe004001021ed63d8 0x0500000003ffe7f9 0x0280000001fff3fc

def z139 : W := mkw 0x100045021404284a 0x080022810a021425 0xee00cf1e3c0c19c6 0xf700678f1e060ce3

def z140 : W := mkw 0x02a06d0334000000 0x015036819a000000 0x00000c0030000000 0x0000060018000000

def z141 : W := mkw 0x401000b161008631 0x20080058b0804318 0xab000cf1f0806639 0xd5800678f840331c

def z142 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfffffffffc001d27 0xfffffffffe000e93

def z143 : W := mkw 0x4108002043effe31 0x2084001021f7ff18 0x0500000003fffe39 0x0280000001ffff1c

def z144 : W := mkw 0x61c7d768c97dbd25 0xb0e3ebb464bede92 0xdf87f3e9cf7f9d27 0xefc3f9f4e7bfce93

def z145 : W := mkw 0x0001004800000000 0x0000802400000000 0x588700e800000000 0xac43807400000000

def z146 : W := mkw 0x9008002003dc2fcb 0xc804001001ee17e5 0x0500000003fc7fff 0x0280000001fe3fff

def z147 : W := mkw 0x100000021400004a 0x080000010a000025 0x0200001e3c0007fe 0x8100000f1e0003ff

def z148 : W := mkw 0x8001004c00100180 0xc0008026000800c0 0x0000000e000001c0 0x00000007000000e0

def z149 : W := mkw 0x01c6d700006d3800 0x00e36b8000369c00 0x4487c300007c1800 0x2243e180003e0c00

def z150 : W := mkw 0x0030289120000000 0x0018144890000000 0xbb783cf1f0806639 0xddbc1e78f840331c

def z151 : W := mkw 0x82ffbafdabd80781 0xc17fdd7ed5ec03c0 0x7cfff0ffc3fc07c1 0xbe7ff87fe1fe03e0

def z152 : W := mkw 0x100045021404284a 0x080022810a021425 0x00000c0030006018 0x000006001800300c

def z153 : W := mkw 0xe008002043f997a5 0xf004001021fccbd2 0x0500000003ff9fe7 0x0280000001ffcff3

def z154 : W := mkw 0x02e7ff4e9c000000 0x0173ffa74e000000 0xf8ffff0e0c000000 0x7c7fff8706000000

def z155 : W := mkw 0x804d804c02d80180 0xc026c026016c00c0 0x7cffc00e03fc01c1 0x3e7fe00701fe00e0

def z156 : W := mkw 0x0002120000211000 0x0001090000108800 0x4487030000701800 0x2243818000380c00

def z157 : W := mkw 0x0000450214000000 0x000022810a000000 0xeb00cf1e3c806639 0xf580678f1e40331c

def z158 : W := mkw 0x0003124888000000 0x0001892444000000 0xda8733e9cc000000 0xed4399f4e6000000

def z159 : W := mkw 0x62f7fffffd319525 0xb17bfffffe98ca92 0xffffffffff739d27 0xffffffffffb9ce93

def z160 : W := mkw 0x825d80ffbfd80781 0xc12ec07fdfec03c0 0x7effc0fffffc07c1 0xbf7fe07ffffe03e0

def z161 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0x30fffcf7f0000000 0x187ffe7bf8000000

def z162 : W := mkw 0x413828b163effe31 0x209c1458b1f7ff18 0xbf783cf1f3fffe39 0xdfbc1e78f9ffff1c

def z163 : W := mkw 0x91fffffe17ff7fcb 0xc8ffffff0bffbfe5 0xfffffffe3fffffff 0xffffffff1fffffff

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0x9a0030e1c0000000 0xcd001870e0000000

def z165 : W := mkw 0x0002120000211000 0x0001090000108800 0xdd87330003739801 0x6ec3998001b9cc00

def z166 : W := mkw 0x4000002041008421 0x2000001020804210 0x9b0030e1c3038421 0xcd801870e181c210

def z167 : W := mkw 0xc01100fd611087b1 0xe008807eb08843d8 0x020000fff00007f8 0x8100007ff80003fc

def z168 : W := mkw 0x03ffffdfbeef7800 0x01ffffefdf77bc00 0xfffffffffffff801 0xfffffffffffffc00

def z169 : W := mkw 0x42a27f03fc02c030 0x21513f81fe016018 0x83003f01fc03e038 0x41801f80fe01f01c

def z170 : W := mkw 0x01eeba0002ef7800 0x00f75d000177bc00 0x15ff300003fff801 0x0aff980001fffc00

def z171 : W := mkw 0xa047924c88791184 0xd023c926443c88c2 0x4487c30e0c7c19c6 0x2243e187063e0ce3

def z172 : W := mkw 0x0001006801100501 0x8000803400880280 0x108700e003700000 0x0843807001b80000

def z173 : W := mkw 0x81feff9402ef7a80 0x40ff7fca0177bd40 0xfdffff1603fffac1 0x7effff8b01fffd60

def z174 : W := mkw 0x602b3a68cbb3d525 0xb0159d3465d9ea92 0xffff3fe9cff3fd27 0xffff9ff4e7f9fe93

def z175 : W := mkw 0x0003126801311501 0x8001893400988a80 0xdd8733e803739d01 0xeec399f401b9ce80

def z176 : W := mkw 0x6000002041319525 0xb00000102098ca92 0x0500000003739d27 0x0280000001b9ce93

def z177 : W := mkw 0xe00b1268cbf997a5 0xf005893465fccbd2 0xdf8733e9cfff9fe7 0xefc399f4e7ffcff3

def z178 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xfdffff1633fffad9 0x7effff8b19fffd6c

def z179 : W := mkw 0x01ffffdc02ef7800 0x00ffffee0177bc00 0xfdfffffe03fff801 0xfeffffff01fffc00

def z180 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x9b7830e1c3038421 0xcdbc1870e181c210

def z181 : W := mkw 0x0010009120000210 0x0008004890000108 0x0000001030000218 0x000000081800010c

def z182 : W := mkw 0x100000000004284a 0x0800000000021425 0xcf0003080c8c7fff 0xe780018406463fff

def z183 : W := mkw 0x403928f96392c731 0xa01c947cb1c96398 0xffff3cf9f3f3e739 0xffff9e7cf9f9f39c

def z184 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x127830f1f3038638 0x893c1878f981c31c

def z185 : W := mkw 0x61fffff9ebffff35 0xb0fffffcf5ffff9a 0xfffffff9ffffff3f 0xfffffffcffffff9f

def z186 : W := mkw 0x005c80b003c80601 0x002e405801e40300 0x7cffc0f003fc0601 0xbe7fe07801fe0300

def z187 : W := mkw 0x82ffbafdabd80781 0xc17fdd7ed5ec03c0 0x10ff30e1c3700000 0x087f9870e1b80000

def z188 : W := mkw 0x0002120000211000 0x0001090000108800 0x1087300003738000 0x0843980001b9c000

def z189 : W := mkw 0x6000002041319525 0xb00000102098ca92 0x9f0030e1c3739d27 0xcf801870e1b9ce93

def z190 : W := mkw 0x0100000000277800 0x008000000013bc00 0x010000000003f800 0x008000000001fc00

def z191 : W := mkw 0x02000003bc000000 0x01000001de000000 0x02000001fc000000 0x01000000fe000000

def z192 : W := mkw 0x500845225786ee7b 0x280422912bc3773d 0xef00cf1e3f8fffff 0xf780678f1fc7ffff

def z193 : W := mkw 0x100045021404284a 0x080022810a021425 0x2500cc16308c7fff 0x1280660b18463fff

def z194 : W := mkw 0x100000000004284a 0x0800000000021425 0x6d00c01e008c7fff 0xb680600f00463fff

def z195 : W := mkw 0x100045021404284a 0x080022810a021425 0xed00cf16308c7ad9 0x7680678b18463d6c

def z196 : W := mkw 0x81fffffc03ff7f81 0xc0fffffe01ffbfc0 0xfdfffffe03ffffc1 0xfeffffff01ffffe0

def z197 : W := mkw 0x0003124888000000 0x0001892444000000 0xdf8733e9cc001d27 0xefc399f4e6000e93

def z198 : W := mkw 0x02a23a01a8000000 0x01511d00d4000000 0x00003001c0000000 0x00001800e0000000

def z199 : W := mkw 0x0030289120000000 0x0018144890000000 0x20780c1030000000 0x103c060818000000

def z200 : W := mkw 0x03a27f03bc277800 0x01d13f81de13bc00 0x83003f01fc03f800 0x41801f80fe01fc00

def z201 : W := mkw 0x21efff488aff7904 0x90f7ffa4457fbc82 0xfdffff080ffff907 0x7effff8407fffc83

def z202 : W := mkw 0x01e6ff00006d3800 0x00f37f8000369c00 0xfcffff00007c1800 0x7e7fff80003e0c00

def z203 : W := mkw 0x00f7ffdc00000000 0x007bffee00000000 0xf8fffffe00000000 0xfc7fffff00000000

def z204 : W := mkw 0x0000450000042800 0x0000228000021400 0x81000f0000007800 0x4080078000003c00

def z205 : W := mkw 0x01a06d0000066800 0x00d0368000033400 0x00000c0000006000 0x0000060000003000

def z206 : W := mkw 0x905d80fc03dc2fcb 0xc82ec07e01ee17e5 0x7dffc0fe03fc7fff 0xbeffe07f01fe3fff

def z207 : W := mkw 0x401000b161008631 0x20080058b0804318 0x000000e1c0000000 0x00000070e0000000

def z208 : W := mkw 0xe05d80fc43f997a5 0xf02ec07e21fccbd2 0x7dffc0fe03ff9fe7 0xbeffe07f01ffcff3

def z209 : W := mkw 0x61eeff00caeff824 0x30f77f806577fc12 0xffffff01cffff827 0x7fffff80e7fffc13

def z210 : W := mkw 0x6000000040219024 0x300000002010c812 0x0100000000039826 0x008000000001cc13

def z211 : W := mkw 0x01feffb003ef7e01 0x00ff7fd801f7bf00 0xfdfffff003fffe01 0xfefffff801ffff00

def z212 : W := mkw 0x03ffffdfbece6800 0x01ffffefdf673400 0xfafffffffc8c6000 0xfd7ffffffe463000

def z213 : W := mkw 0x81fced9402ce6a80 0x40fe76ca01673540 0x2078cc16008c62c0 0x103c660b00463160

def z214 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x830033e9cc039d26 0xc18019f4e601ce93

def z215 : W := mkw 0x02c7d74e9c000000 0x0163eba74e000000 0xda87f3efcc000000 0xed43f9f7e6000000

def z216 : W := mkw 0x805c809402c80280 0x402e404a01640140 0x2078c016008c02c0 0x103c600b00460160

def z217 : W := mkw 0xc1fffffd63ffffb1 0xe0fffffeb1ffffd8 0xfffffffff3fffff9 0xfffffffff9fffffc

def z218 : W := mkw 0x42ffbafdeb82c631 0x217fdd7ef5c16318 0xbbff3cf1f383e639 0xddff9e78f9c1f31c

def z219 : W := mkw 0x0002570000253800 0x00012b8000129c00 0xfd87ff0003fff801 0x7ec3ff8001fffc00

def z220 : W := mkw 0x005d80fc03800601 0x002ec07e01c00300 0x78ffc0fe03800601 0xbc7fe07f01c00300

def z221 : W := mkw 0x22c7d74e9c311104 0x9163eba74e188882 0x4487c30e0c701906 0x2243e18706380c83

def z222 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0x54fff300037f9800 0x2a7ff98001bfcc00

def z223 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0xbaff3cf1f0000000 0xdd7f9e78f8000000

def z224 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x387830f1c3838601 0x9c3c1878e1c1c300

def z225 : W := mkw 0x60223a01e823d034 0x30111d00f411e81a 0x83003f01fc03f83e 0x41801f80fe01fc1f

def z226 : W := mkw 0x92ffffffbfdc2fcb 0xc97fffffdfee17e5 0xfffffffffffc7fff 0xfffffffffffe3fff

def z227 : W := mkw 0x100045021404284a 0x080022810a021425 0x83000f003c00783e 0x418007801e003c1f

def z228 : W := mkw 0xe2fffffffff997a5 0xf17ffffffffccbd2 0xffffffffffff9fe7 0xffffffffffffcff3

def z229 : W := mkw 0x03f7ffdfbc6d3800 0x01fbffefde369c00 0xfefffffffc7c1800 0xff7ffffffe3e0c00

def z230 : W := mkw 0x01feff9122ef7800 0x00ff7fc89177bc00 0xfffffff1f3fff801 0xfffffff8f9fffc00

def z231 : W := mkw 0x8045804c00580180 0xc022c026002c00c0 0x6c87c01e00fc07c1 0xb643e00f007e03e0

def z232 : W := mkw 0x601b12f8cbb19725 0xb00d897c65d8cb92 0xffff33f9cff39f27 0xffff99fce7f9cf93

def z233 : W := mkw 0x801100fc01100781 0xc008807e008803c0 0x000000e000000000 0x0000007000000000

def z234 : W := mkw 0x60233a69e933d535 0xb0119d34f499ea9a 0xdf873fe9ff73fd3f 0xefc39ff4ffb9fe9f

def z235 : W := mkw 0x805c809402c80280 0x402e404a01640140 0x7cffc01603fc02c1 0x3e7fe00b01fe0160

def z236 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfbfffffffc806639 0xfdfffffffe40331c

def z237 : W := mkw 0x0003124888211000 0x0001892444108800 0xdf8733e9cf739801 0xefc399f4e7b9cc00

def z238 : W := mkw 0x100045021404284a 0x080022810a021425 0xef00cf003c8c783f 0x778067801e463c1f

def z239 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0x64ffcf0000fc7800 0x327fe780007e3c00

def z240 : W := mkw 0x60031268c9108525 0xb001893464884292 0xda8733e9cc000526 0xed4399f4e6000293

def z241 : W := mkw 0x100045021404284a 0x080022810a021425 0xeb00cf1e3c00783e 0xf580678f1e003c1f

def z242 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0xffffccfe33fc67f9 0xffffe67f19fe33fc

def z243 : W := mkw 0x00306d9334000000 0x001836c99a000000 0xfa78fffffc000000 0xfd3c7ffffe000000

def z244 : W := mkw 0x805f92fc8bd80781 0xc02fc97e45ec03c0 0xfefff3ffcffc07c1 0xff7ff9ffe7fe03e0

def z245 : W := mkw 0x004c800002c80000 0x0026400001640000 0x7cffc01e03fc07c1 0xbe7fe00f01fe03e0

def z246 : W := mkw 0x805dc5fe17d80781 0xc02ee2ff0bec03c0 0xfeffcffe3ffc07c1 0xff7fe7ff1ffe03e0

def z247 : W := mkw 0x402028216102c431 0x20101410b0816218 0x9b003ce1f303e439 0xcd801e70f981f21c

def z248 : W := mkw 0x02f7ffdfbc042800 0x017bffefde021400 0xfffffffffc8c7801 0xfffffffffe463c00

def z249 : W := mkw 0x0030289120000000 0x0018144890000000 0x107830e1c0000000 0x083c1870e0000000

def z250 : W := mkw 0x11eced0216ce684a 0x08f676810b673425 0x2078cc16308c62d8 0x103c660b1846316c

def z251 : W := mkw 0x805f92fc03f91781 0xc02fc97e01fc8bc0 0xfdfff3fe03ff9fc1 0xfefff9ff01ffcfe0

def z252 : W := mkw 0x004e920002e91000 0x0027490001748800 0xfdfff30003ff9801 0x7efff98001ffcc00

def z253 : W := mkw 0x501045b37504ae7b 0x280822d9ba82573d 0xef00cffffc8c7fff 0xf78067fffe463fff

def z254 : W := mkw 0x01e6ff00006f7800 0x00f37f800037bc00 0xc587ff00007ff800 0x62c3ff80003ffc00

def z255 : W := mkw 0x0008000002824000 0x0004000001412000 0x010000000383e001 0x0080000001c1f000

def z256 : W := mkw 0x1108000002ef784a 0x088400000177bc25 0x0500000003ffffff 0x0280000001ffffff

def z257 : W := mkw 0x025580dfbc000000 0x012ac06fde000000 0x7affc0fffc000000 0xbd7fe07ffe000000

def z258 : W := mkw 0x905cc59616cc2aca 0x482e62cb0b661565 0x2078cc16308c62d8 0x103c660b1846316c

def z259 : W := mkw 0x40feffb16382c631 0x207f7fd8b1c16318 0xfbfffff1f383e639 0xfdfffff8f9c1f31c

def z260 : W := mkw 0x81ffbafc03fb5781 0xc0ffdd7e01fdabc0 0x10ff30e003738000 0x087f987001b9c000

def z261 : W := mkw 0x403028b161008421 0x20181458b0804210 0xbb783cf1f3038421 0xddbc1e78f981c210

def z262 : W := mkw 0x121145dfbc04284a 0x0908a2efde021425 0xef00cffffc8c7fff 0xf78067fffe463fff

def z263 : W := mkw 0x0020280120000000 0x0010140090000000 0x82003c01f0000000 0x41001e00f8000000

def z264 : W := mkw 0x02a27f03bc000000 0x01513f81de000000 0x82003f01fc000000 0x41001f80fe000000

def z265 : W := mkw 0x610b1268cbfffd25 0xb085893465fffe92 0xdf8733e9cffffd27 0xefc399f4e7fffe93

def z266 : W := mkw 0x100000021400004a 0x080000010a000025 0x6e00c01e3c8c07ff 0xb700600f1e4603ff

def z267 : W := mkw 0x100045021404284a 0x080022810a021425 0xab00cc16308c66f9 0xd580660b1846337c

def z268 : W := mkw 0x00eeff0002c80000 0x00777f8001640000 0xfcffff0003fc0001 0x7e7fff8001fe0000

def z269 : W := mkw 0x4000002041008421 0x2000001020804210 0xbb003cf1f383e639 0xdd801e78f9c1f31c

def z270 : W := mkw 0x10306d933404284a 0x081836c99a021425 0xff78fffffc8c7fff 0xffbc7ffffe463fff

def z271 : W := mkw 0x42ffbafdeb82c631 0x217fdd7ef5c16318 0x10ff30e1c3038000 0x087f9870e181c000

def z272 : W := mkw 0x004c800002c80000 0x0026400001640000 0x2078c000008c0000 0x103c600000460000

def z273 : W := mkw 0x9045c54e145c29ca 0xc822e2a70a2e14e5 0x4487c30e0c7c19c6 0x2243e187063e0ce3

def z274 : W := mkw 0x02f7ffffbd100501 0x817bffffde880280 0xfeffffffff700501 0xff7fffffffb80280

def z275 : W := mkw 0x0201004e9c000000 0x010080274e000000 0x0000000e0c000000 0x0000000706000000

def z276 : W := mkw 0xc05d80fd63d887b1 0xe02ec07eb1ec43d8 0x7effc0fff3fc07f9 0xbf7fe07ff9fe03fc

def z277 : W := mkw 0x02f4a89520000000 0x017a544a90000000 0x0078000000000000 0x003c000000000000

def z278 : W := mkw 0x00e6ff0214000000 0x00737f810a000000 0xfaffff1e3c000000 0xfd7fff8f1e000000

def z279 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x14ff00e003fc07c1 0x0a7f807001fe03e0

def z280 : W := mkw 0x02f7ffdda8000000 0x017bffeed4000000 0xf8ffffe1c0000000 0x7c7ffff0e0000000

def z281 : W := mkw 0x601312f9e9319735 0xb009897cf498cb9a 0xdf8733f9ff739f3f 0xefc399fcffb9cf9f

def z282 : W := mkw 0x807ca89522ca4290 0x403e544a91652148 0x2078cc16308c62d8 0x103c660b1846316c

def z283 : W := mkw 0x2003124888311104 0x9001892444188882 0xdd8733080f739907 0x6ec3998407b9cc83

def z284 : W := mkw 0x60000000c8008024 0x3000000064004012 0x02000001cc000026 0x01000000e6000013

def z285 : W := mkw 0x62f7ffdffc219024 0x317bffeffe10c812 0xfbfffffffc039826 0xfdfffffffe01cc13

def z286 : W := mkw 0x0000000000000000 0x0000000000000000 0x8b00000000000421 0xc580000000000210

def z287 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x548733e9cf739906 0x2a4399f4e7b9cc83

def z288 : W := mkw 0x005d80dc02c80000 0x002ec06e01640000 0x7cffc0fe03fc0001 0xbe7fe07f01fe0000

def z289 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xff78fcfff38fe7f9 0xffbc7e7ff9c7f3fc

def z290 : W := mkw 0x01eced0002ce6800 0x00f6768001673400 0x2078cc00008c6000 0x103c660000463000

def z291 : W := mkw 0x70025702dc25b86e 0x38012b816e12dc37 0x83003f01fc03f83e 0x41801f80fe01fc1f

def z292 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfafffffffc8c62d8 0xfd7ffffffe46316c

def z293 : W := mkw 0x01eced0002ce6800 0x00f6768001673400 0xb978fc00038fe001 0x5cbc7e0001c7f000

def z294 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfefffffffc8c07c1 0xff7ffffffe4603e0

def z295 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x938733e1cf739826 0x49c399f0e7b9cc13

def z296 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xffffff080ffffd27 0xffffff8407fffe93

def z297 : W := mkw 0x7003576add35bd6f 0xb801abb56e9adeb7 0xdf873fe9ff73fd3f 0xefc39ff4ffb9fe9f

def z298 : W := mkw 0x8008002003d80781 0xc004001001ec03c0 0x0000000003700000 0x0000000001b80000

def z299 : W := mkw 0x02b37fdfbc000000 0x0159bfefde000000 0x82003ffffc000000 0xc1001ffffe000000

def z300 : W := mkw 0x805d80dc02c80280 0x402ec06e01640140 0x78ffc0fe008c02c0 0xbc7fe07f00460160

def z301 : W := mkw 0x805c809402c80280 0x402e404a01640140 0x0078000000000000 0x003c000000000000

def z302 : W := mkw 0x403828916282c230 0x201c1448b1416118 0xa3783c11f083e238 0x51bc1e08f841f11c

def z303 : W := mkw 0x8010009400000280 0x4008004a00000140 0x00000016000002c0 0x0000000b00000160

def z304 : W := mkw 0x6000002041319525 0xb00000102098ca92 0xcf0003080f739d27 0xe780018407b9ce93

def z305 : W := mkw 0x100045021404284a 0x080022810a021425 0x87000f003c8c7fff 0x438007801e463fff

def z306 : W := mkw 0x100045021404284a 0x080022810a021425 0x83000f1e3c007ffe 0xc180078f1e003fff

def z307 : W := mkw 0xc05d80fc43dac7b1 0xe02ec07e21ed63d8 0x7dffc0fe03ffe7f9 0xbeffe07f01fff3fc

def z308 : W := mkw 0x01a27f0000277800 0x00d13f800013bc00 0xdd873f000373f801 0x6ec39f8001b9fc00

def z309 : W := mkw 0x100000000000004a 0x0800000000000025 0x00000000000007fe 0x00000000000003ff

def z310 : W := mkw 0x804d806c03d80781 0xc026c03601ec03c0 0x4487c00e03fc07c1 0x2243e00701fe03e0

def z311 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x5cff00e803700501 0xae7f807401b80280

def z312 : W := mkw 0x801100fc01100781 0xc008807e008803c0 0x5c8700fe037007c1 0xae43807f01b803e0

def z313 : W := mkw 0x0108450002ef7800 0x008422800177bc00 0xed00cf0003fff801 0x7680678001fffc00

def z314 : W := mkw 0xe05d80fccbd887a5 0xf02ec07e65ec43d2 0x7effc0ffcffc07e7 0xbf7fe07fe7fe03f3

def z315 : W := mkw 0x70031268c935bd6f 0xb8018934649adeb7 0xdf8733e9cfffffff 0xefc399f4e7ffffff

def z316 : W := mkw 0x03efff4e9eef7800 0x01f7ffa74f77bc00 0xfdffff0e0ffff801 0x7effff8707fffc00

def z317 : W := mkw 0x0008000002800000 0x0004000001400000 0x3878000003800001 0x1c3c000001c00000

def z318 : W := mkw 0x6000002041319525 0xb00000102098ca92 0x0000000003738000 0x0000000001b9c000

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000c016008c02c0 0x1000600b00460160

def z320 : W := mkw 0x10386d9336866a5a 0x081c36c99b43352d 0x2078cc16308c62d8 0x103c660b1846316c

def z321 : W := mkw 0x100000000004284a 0x0800000000021425 0x04000000000c19c6 0x0200000000060ce3

def z322 : W := mkw 0x601100f9e9108735 0xb008807cf488439a 0x020000f9fc00073e 0x8100007cfe00039f

def z323 : W := mkw 0x61efba68cbfbd525 0xb0f7dd3465fdea92 0xdfff33e9cf739d27 0xefff99f4e7b9ce93

def z324 : W := mkw 0x0000450214000000 0x000022810a000000 0x2000cc1630000000 0x1000660b18000000

def z325 : W := mkw 0x0000002001000401 0x0000001000800200 0x180000e003000401 0x8c00007001800200

def z326 : W := mkw 0x02f5eddfbc000000 0x017af6efde000000 0x2278ccfffc000000 0x913c667ffe000000

def z327 : W := mkw 0x12a27f03bc04284a 0x09513f81de021425 0x83003f01fc00783e 0x41801f80fe003c1f

def z328 : W := mkw 0x60010068c9108525 0xb000803464884292 0xcf0003e9cc001d27 0xe78001f4e6000e93

def z329 : W := mkw 0x62f7fffffd319525 0xb17bfffffe98ca92 0xfaffffffff738000 0xfd7fffffffb9c000

def z330 : W := mkw 0x60031248c8319124 0xb00189246418c892 0xc7873309cc739926 0x63c39984e639cc93

def z331 : W := mkw 0x0010009120000000 0x0008004890000000 0x020000f1f0000000 0x81000078f8000000

def z332 : W := mkw 0x01eeff0002ce6800 0x00f77f8001673400 0xf8ffff00008c6000 0x7c7fff8000463000

def z333 : W := mkw 0x01feff9122ef7a10 0x00ff7fc89177bd08 0xfdffff1033fffa19 0x7effff8819fffd0c

def z334 : W := mkw 0x01efff6803ff7d01 0x80f7ffb401ffbe80 0xfdffffe803fffd01 0xfefffff401fffe80

def z335 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z336 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x93783ce1f303e038 0x49bc1e70f981f01c

def z337 : W := mkw 0x0000000000000000 0x0000000000000000 0x9900300003038001 0x4c8018000181c000

def z338 : W := mkw 0x2003124888311104 0x9001892444188882 0x0087000000700000 0x0043800000380000

def z339 : W := mkw 0x500045225504ac6b 0x280022912a825635 0xff00ffffff8fffff 0xff807fffffc7ffff

def z340 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x158730e1c3739d27 0x0ac39870e1b9ce93

def z341 : W := mkw 0x01aa7f0002ef7800 0x00d53f800177bc00 0x85003f0003fff801 0x42801f8001fffc00

def z342 : W := mkw 0x4000002041008421 0x2000001020804210 0xdf0033e9cf039d27 0xef8019f4e781ce93

def z343 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0xb9ff3c0003f3e001 0x5cff9e0001f9f000

def z344 : W := mkw 0x0000000000000000 0x0000000000000000 0x830003000c001826 0x4180018006000c13

def z345 : W := mkw 0x11a27f021427784a 0x08d13f810a13bc25 0x83003f003c03f83e 0x41801f801e01fc1f

def z346 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0x91ff3f000373f800 0x48ff9f8001b9fc00

def z347 : W := mkw 0xc05d80fc43d887a1 0xe02ec07e21ec43d0 0xfffff0ffc3ff87e1 0xfffff87fe1ffc3f0

def z348 : W := mkw 0x401800b04382c631 0x200c005821c16318 0x397800f00383e639 0x9cbc007801c1f31c

def z349 : W := mkw 0x0000000000000000 0x0000000000000000 0xa9000c0000806001 0x5480060000403000

def z350 : W := mkw 0x0002120088000000 0x0001090044000000 0x82003301cc000000 0x41001980e6000000

def z351 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xff783ff9ff83ff3f 0xffbc1ffcffc1ff9f

def z352 : W := mkw 0x02ffffdfbe824000 0x017fffefdf412000 0xfbffffffff83e001 0xfdffffffffc1f000

def z353 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x128730e9cf738526 0x89439874e7b9c293

def z354 : W := mkw 0x9008452217dc2fcb 0xc80422910bee17e5 0xef00cf1e3ffc7fff 0xf780678f1ffe3fff

def z355 : W := mkw 0x00e4ed0000000000 0x0072768000000000 0x2078cc0000000000 0x103c660000000000

def z356 : W := mkw 0x01eca80002ca4000 0x00f6540001652000 0x0078000000000000 0x003c000000000000

def z357 : W := mkw 0x41febab163ebd631 0x20ff5d58b1f5eb18 0x10ff30e1c3738000 0x087f9870e1b9c000

def z358 : W := mkw 0x503828b37782c67b 0x281c1459bbc1633d 0xbb783cffff83e7ff 0xddbc1e7fffc1f3ff

def z359 : W := mkw 0x023128dfbc000000 0x0118946fde000000 0xba783cfffc000000 0xdd3c1e7ffe000000

def z360 : W := mkw 0x8108002003ff7f81 0xc084001001ffbfc0 0x0500000003ffffc1 0x0280000001ffffe0

def z361 : W := mkw 0x02c7924c88000000 0x0163c92644000000 0x0087000000000000 0x0043800000000000

def z362 : W := mkw 0x400000004002c030 0x2000000020016018 0x010000000003e038 0x008000000001f01c

def z363 : W := mkw 0x81eeff2003ff7f81 0xc0f77f9001ffbfc0 0xfdffff0003ffffc1 0x7effff8001ffffe0

def z364 : W := mkw 0x001800b003800601 0x000c005801c00300 0xbb780cf033806639 0xddbc067819c0331c

def z365 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x7cfff00003ff8001 0x3e7ff80001ffc000

def z366 : W := mkw 0x805d80dc02d80380 0xc02ec06e016c01c0 0x64ffc01e00fc03c0 0x327fe00f007e01e0

def z367 : W := mkw 0x901145fe15142fcb 0xc808a2ff0a8a17e5 0xef00cffe3c8c7fff 0xf78067ff1e463fff

def z368 : W := mkw 0x42fcedb77782c631 0x217e76dbbbc16318 0xbb78fcf7f383e639 0xddbc7e7bf9c1f31c

def z369 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0xddff330003739801 0x6eff998001b9cc00

def z370 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xfdffff1e03ffffc1 0xfeffff8f01ffffe0

def z371 : W := mkw 0x0002120000000000 0x0001090000000000 0xd887330000000000 0x6c43998000000000

def z372 : W := mkw 0x100000000004284a 0x0800000000021425 0xaf000c10308c7fff 0xd780060818463fff

def z373 : W := mkw 0x905cc59616cc2aca 0x482e62cb0b661565 0xef78cf1e3c8c7fff 0xf7bc678f1e463fff

def z374 : W := mkw 0x0000450214000000 0x000022810a000000 0x4000c30e0c000000 0x2000618706000000

def z375 : W := mkw 0x0000000000000000 0x0000000000000000 0x0500000000001d27 0x0280000000000e93

def z376 : W := mkw 0x804c802003d80781 0xc026401001ec03c0 0x7cffc00003fc07c1 0x3e7fe00001fe03e0

def z377 : W := mkw 0x82ffffffbfd80781 0xc17fffffdfec03c0 0xfaffffffff700000 0xfd7fffffffb80000

def z378 : W := mkw 0x407ca8b163cac631 0x203e5458b1e56318 0xfffffcf1f3ffe639 0xfffffe78f9fff31c

def z379 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xff873ff9fff3ff3f 0xffc39ffcfff9ff9f

def z380 : W := mkw 0x002a3a0002a35000 0x00151d000151a800 0xfdff3f0003f3f801 0x7eff9f8001f9fc00

def z381 : W := mkw 0x0000000000000000 0x0000000000000000 0xef00cc1e308c67f9 0xf780660f184633fc

def z382 : W := mkw 0x03ffffdfbeeb5000 0x01ffffefdf75a800 0xfaffffffff738000 0xfd7fffffffb9c000

def z383 : W := mkw 0x01c4c500004c2800 0x00e2628000261400 0x0000c000000c0000 0x0000600000060000

def z384 : W := mkw 0x8008002003d80781 0xc004001001ec03c0 0x6c00c01e03fc07c1 0xb600600f01fe03e0

def z385 : W := mkw 0x12f7ffdfbc00004a 0x097bffefde000025 0xfafffffffc0007fe 0xfd7ffffffe0003ff

def z386 : W := mkw 0x9045c54e145c29ca 0xc822e2a70a2e14e5 0xef87cf1e3cfc7fff 0xf7c3e78f1e7e3fff

def z387 : W := mkw 0x4000002041008421 0x2000001020804210 0x020000e1c0000420 0x81000070e0000210

def z388 : W := mkw 0x0000000000000000 0x0000000000000000 0x04000000008c07c1 0x02000000004603e0

def z389 : W := mkw 0x805580fc01100781 0xc02ac07e008803c0 0x78ffc0fe000007c0 0xbc7fe07f000003e0

def z390 : W := mkw 0x0000000000000000 0x0000000000000000 0x2800001000800601 0x9400000800400300

def z391 : W := mkw 0x72f7fffffd35bd6f 0xb97bfffffe9adeb7 0xffffffffffffffff 0xffffffffffffffff

def z392 : W := mkw 0x014c800002ef7800 0x00a640000177bc00 0x7dffc00003fff801 0x3effe00001fffc00

def z393 : W := mkw 0x6001006841319525 0xb00080342098ca92 0x5d8700e803739d27 0xaec3807401b9ce93

def z394 : W := mkw 0x02f6ff9734000000 0x017b7fcb9a000000 0xf8ffff1630000000 0x7c7fff8b18000000

def z395 : W := mkw 0x815d80fc03ff7f81 0xc0aec07e01ffbfc0 0x7dffc0fe03ffffc1 0xbeffe07f01ffffe0

def z396 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x21780c103383e639 0x10bc060819c1f31c

def z397 : W := mkw 0x42ba7fb3ff82c631 0x215d3fd9ffc16318 0xbb783ff1ff83e639 0xddbc1ff8ffc1f31c

def z398 : W := mkw 0x00e6ba0000000000 0x00735d0000000000 0x10ff300000000000 0x087f980000000000

def z399 : W := mkw 0x403028916002c030 0x20181448b0016018 0xbb783cf1f003e038 0xddbc1e78f801f01c

def z400 : W := mkw 0x01a23a0000235000 0x00d11d000011a800 0x0000300000038000 0x000018000001c000

def z401 : W := mkw 0x01ced70002ef7800 0x00e76b800177bc00 0x4587c30003fff801 0x22c3e18001fffc00

def z402 : W := mkw 0xe01100fcc91087a5 0xf008807e648843d2 0x020000ffcc0007e6 0x8100007fe60003f3

def z403 : W := mkw 0x12c7d74e9c04284a 0x0963eba74e021425 0xef87cf1e3c8c7fff 0xf7c3e78f1e463fff

def z404 : W := mkw 0x503828b16386ee7b 0x281c1458b1c3773d 0xbf783cf1f38fffff 0xdfbc1e78f9c7ffff

def z405 : W := mkw 0x0001004800100100 0x8000802400080080 0x4487000800700100 0x2243800400380080

def z406 : W := mkw 0x10e6ff021404284a 0x08737f810a021425 0xffffff1e3c8c7fff 0xffffff8f1e463fff

def z407 : W := mkw 0x82fdedff37d80781 0xc17ef6ff9bec03c0 0x7cffccfe33fc07c1 0xbe7fe67f19fe03e0

def z408 : W := mkw 0x006ca80002ca4000 0x0036540001652000 0xfdfffc0003ffe001 0x7efffe0001fff000

def z409 : W := mkw 0x81dfd7fc03fd3f81 0xc0efebfe01fe9fc0 0x7cffc3fe03fc1fc1 0xbe7fe1ff01fe0fe0

def z410 : W := mkw 0x83ffffffbfff7f81 0xc1ffffffdfffbfc0 0xffffffffffffffc1 0xffffffffffffffe0

def z411 : W := mkw 0x62f7bafde9319525 0xb17bdd7ef498ca92 0xdfff33e9cf739d27 0xefff99f4e7b9ce93

def z412 : W := mkw 0x100045021404284a 0x080022810a021425 0x6c00cc1e308c67d9 0xb600660f184633ec

def z413 : W := mkw 0xc2ffffffffdac7b1 0xe17fffffffed63d8 0xffffffffffffe7f9 0xfffffffffffff3fc

def z414 : W := mkw 0x60021200c8219024 0x300109006410c812 0x00003001c0038000 0x00001800e001c000

def z415 : W := mkw 0x52ffffffff86ee7b 0x297fffffffc3773d 0xffffffffff8fffff 0xffffffffffc7ffff

def z416 : W := mkw 0x1108450216ef784a 0x088422810b77bc25 0xef00cf1e3fffffff 0xf780678f1fffffff

def z417 : W := mkw 0x0003574a9c000000 0x0001aba54e000000 0xfa87fffffc000000 0xfd43fffffe000000

def z418 : W := mkw 0x003828b003824601 0x001c145801c12300 0xb9783cf00383e601 0xdcbc1e7801c1f300

def z419 : W := mkw 0x01a27f0000277800 0x00d13f800013bc00 0xed00ff00008ff801 0x76807f800047fc00

def z420 : W := mkw 0x801900fc03900781 0xc00c807e01c803c0 0x387800fe038007c1 0x9c3c007f01c003e0

def z421 : W := mkw 0x02e7ff4fbc000000 0x0173ffa7de000000 0xc287ff0ffc000000 0x6143ff87fe000000

def z422 : W := mkw 0x403a3ab163a3d631 0x201d1d58b1d1eb18 0xffff3ff1f3f3fe39 0xffff9ff8f9f9ff1c

def z423 : W := mkw 0x61efff68cbfffd25 0xb0f7ffb465fffe92 0xfdffffe1c3fff801 0x7efffff0e1fffc00

def z424 : W := mkw 0x60010068c9319525 0xb00080346498ca92 0x070000e9cf739d27 0x83800074e7b9ce93

def z425 : W := mkw 0x0003124888000000 0x0001892444000000 0x108730e1c0000000 0x08439870e0000000

def z426 : W := mkw 0x0003124888000000 0x0001892444000000 0x408703080c000000 0x2043818406000000

def z427 : W := mkw 0x8000000000580180 0xc0000000002c00c0 0x04000000007c01c0 0x02000000003e00e0

def z428 : W := mkw 0x421100fffd008631 0x2108807ffe804318 0x020000fffc000638 0x8100007ffe00031c

def z429 : W := mkw 0xe1fffffccbffffa5 0xf0fffffe65ffffd2 0xffffffffcfffffe7 0xffffffffe7fffff3

def z430 : W := mkw 0x805c80b403d80781 0xc02e405a01ec03c0 0x2478c01603fc07c1 0x123c600b01fe03e0

def z431 : W := mkw 0x605792fcc9319525 0xb02bc97e6498ca92 0xfffff3ffcf739d27 0xfffff9ffe7b9ce93

def z432 : W := mkw 0x00e6ff0000211000 0x00737f8000108800 0xfdffff0003739801 0x7effff8001b9cc00

def z433 : W := mkw 0x00f6ff9120000000 0x007b7fc890000000 0xfafffff1f0000000 0xfd7ffff8f8000000

def z434 : W := mkw 0x61eeff2043fffd25 0xb0f77f9021fffe92 0xfdffff0003fffd27 0x7effff8001fffe93

def z435 : W := mkw 0x001800b003800601 0x000c005801c00300 0x107800e003000000 0x083c007001800000

def z436 : W := mkw 0x3003574a9c35394e 0x9801aba54e1a9ca7 0x4487c30e0c7c19c6 0x2243e187063e0ce3

def z437 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x117830e1c383e639 0x08bc1870e1c1f31c

def z438 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0xdaff33e9cc000000 0xed7f99f4e6000000

def z439 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x10ff00fe037007c0 0x887f807f01b803e0

def z440 : W := mkw 0x01eeff0002eb5000 0x00f77f800175a800 0xf8ffff0003738000 0x7c7fff8001b9c000

def z441 : W := mkw 0x42f7fffffd008421 0x217bfffffe804210 0xfbffffffff038421 0xfdffffffff81c210

def z442 : W := mkw 0x02a37f4bbc000000 0x0151bfa5de000000 0xda873fe9fc000000 0xed439ff4fe000000

def z443 : W := mkw 0x4000002041008631 0x2000001020804318 0x0000000000000638 0x000000000000031c

def z444 : W := mkw 0x60010068c9108525 0xb000803464884292 0x5e8700e9cf700527 0xaf438074e7b80293

def z445 : W := mkw 0x6108002043fffd25 0xb084001021fffe92 0x0500000003fffd27 0x0280000001fffe93

def z446 : W := mkw 0x01ced70002ed3800 0x00e76b8001769c00 0x7cffc30003fc1801 0x3e7fe18001fe0c00

def z447 : W := mkw 0x0000450214000000 0x000022810a000000 0x82000f003c000000 0x410007801e000000

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0x4400c00e000c01c0 0x22006007000600e0

def z449 : W := mkw 0x401800b16382c631 0x200c0058b1c16318 0x030000f1f383e639 0x81800078f9c1f31c

def z450 : W := mkw 0x0000000000000000 0x0000000000000000 0x6800c01e00000000 0xb400600f00000000

def z451 : W := mkw 0x81ffbafc03fb5781 0xc0ffdd7e01fdabc0 0x7cfff0fe03ff87c1 0xbe7ff87f01ffc3e0

def z452 : W := mkw 0x01c6920000691000 0x00e3490000348800 0x0087000000700000 0x0043800000380000

def z453 : W := mkw 0x61a27f00c827f824 0x30d13f806413fc12 0x83003f01cc03f826 0x41801f80e601fc13

def z454 : W := mkw 0x01c6d700006d3800 0x00e36b8000369c00 0xdd87f300037f9801 0x6ec3f98001bfcc00

def z455 : W := mkw 0x80fffffc03d80781 0xc07ffffe01ec03c0 0xfcfffffe03fc07c1 0xfe7fffff01fe03e0

def z456 : W := mkw 0x100045021404284a 0x080022810a021425 0x000003000c001806 0x0000018006000c03

def z457 : W := mkw 0x603a3ab1eba3d635 0x301d1d58f5d1eb1a 0xbb783ff1ff83fe3f 0xddbc1ff8ffc1ff1f

def z458 : W := mkw 0x61a37f68c937fd25 0xb0d1bfb4649bfe92 0xdf873fe9cf73fd27 0xefc39ff4e7b9fe93

def z459 : W := mkw 0xf05fd7fedffdbfef 0xf82febff6ffedff7 0xffffffffffffffff 0xffffffffffffffff

def z460 : W := mkw 0x4000000160008030 0x20000000b0004018 0x02000001f0000038 0x01000000f800001c

def z461 : W := mkw 0x0210009734000000 0x0108004b9a000000 0x0000001630000000 0x0000000b18000000

def z462 : W := mkw 0x60031248c8219024 0x300189246410c812 0xdb8733e9cc039826 0xedc399f4e601cc13

def z463 : W := mkw 0x02d7d7de9c000000 0x016bebef4e000000 0x78ffc3fe0c000000 0xbc7fe1ff06000000

def z464 : W := mkw 0x02f7badfbc000000 0x017bdd6fde000000 0x12ff30fffc000000 0x897f987ffe000000

def z465 : W := mkw 0x403028b16102c631 0x20181458b0816318 0x83003cf1f003e638 0xc1801e78f801f31c

def z466 : W := mkw 0x100000000004284a 0x0800000000021425 0x00000000008c62d8 0x000000000046316c

def z467 : W := mkw 0x01c6d700006d3800 0x00e36b8000369c00 0xed87cf0000fc7801 0x76c3e780007e3c00

def z468 : W := mkw 0x02ffffdfbe824210 0x017fffefdf412108 0xfafffffffc806218 0xfd7ffffffe40310c

def z469 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0x30fffc0003ffe000 0x187ffe0001fff000

def z470 : W := mkw 0xe07fbafdebfbd7b5 0xf03fdd7ef5fdebda 0xffffffffffffffff 0xffffffffffffffff

def z471 : W := mkw 0x0028280002824000 0x0014140001412000 0x1078300003038000 0x083c18000181c000

def z472 : W := mkw 0x7003576add35bd6f 0xb801abb56e9adeb7 0xdf87f3efcf7f9de7 0xefc3f9f7e7bfcef3

def z473 : W := mkw 0x401000b161008631 0x20080058b0804318 0x9b0030f1f3038639 0xcd801878f981c31c

def z474 : W := mkw 0x11eeff0002ef784a 0x08f77f800177bc25 0xfdffff0003ffffff 0x7effff8001ffffff

def z475 : W := mkw 0x02f4ed9734000000 0x017a76cb9a000000 0xea78cf1e3c000000 0xf53c678f1e000000

def z476 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x78fff0ffc0000000 0xbc7ff87fe0000000

def z477 : W := mkw 0x60333af9e9319525 0xb0199d7cf498ca92 0xffff3ff9ff739d27 0xffff9ffcffb9ce93

def z478 : W := mkw 0x01e6ff0000277800 0x00f37f800013bc00 0xf9ffff000003f800 0x7cffff800001fc00

def z479 : W := mkw 0x62c7d76edd319525 0xb163ebb76e98ca92 0xdf87f3efcf739d27 0xefc3f9f7e7b9ce93

def z480 : W := mkw 0x0000000000000000 0x0000000000000000 0xef000f183c807f3f 0xf780078c1e403f9f

def z481 : W := mkw 0x805dc5fc03dc2f81 0xc02ee2fe01ee17c0 0xfdffcffe03fc7fc1 0xfeffe7ff01fe3fe0

def z482 : W := mkw 0x400800204382c631 0x2004001021c16318 0xab000c103383e639 0xd580060819c1f31c

def z483 : W := mkw 0x2002120088211004 0x1001090044108802 0x000003000c001806 0x0000018006000c03

def z484 : W := mkw 0x60010068c9108525 0xb000803464884292 0x9b0030e9cf038527 0xcd801874e781c293

def z485 : W := mkw 0x0018009002800200 0x000c004801400100 0x2078001000800200 0x103c000800400100

def z486 : W := mkw 0x603828b163b3d735 0xb01c1458b1d9eb9a 0xbf783cf1f3f3ff3f 0xdfbc1e78f9f9ff9f

def z487 : W := mkw 0x101845b217842e4b 0x080c22d90bc21725 0xff78cffe3f8c7fff 0xffbc67ff1fc63fff

def z488 : W := mkw 0x001000b001000601 0x0008005800800300 0x000000f000000600 0x8000007800000300

def z489 : W := mkw 0x00286d0002866800 0x0014368001433400 0xfd78ff00038ff801 0x7ebc7f8001c7fc00

def z490 : W := mkw 0x100045000004284a 0x0800228000021425 0xed00cf00008c7fff 0x7680678000463fff

def z491 : W := mkw 0x7001456add14ad6f 0xb800a2b56e8a56b7 0xef00cffffc8c7fff 0xf78067fffe463fff

def z492 : W := mkw 0x0000450214042800 0x000022810a021400 0xef00cf1e3c8c7801 0xf780678f1e463c00

def z493 : W := mkw 0x03ffffddaaef7800 0x01ffffeed577bc00 0xfdffffe1c3fff801 0x7efffff0e1fffc00

def z494 : W := mkw 0x703b7ffbffb7ff7f 0xb81dbffdffdbffbf 0xffffffffffffffff 0xffffffffffffffff

def z495 : W := mkw 0x0000450000042800 0x0000228000021400 0xef00cf10308c7e39 0xf780678818463f1c

def z496 : W := mkw 0x62a27f03fc219024 0x31513f81fe10c812 0x83003f01fc039826 0x41801f80fe01cc13

def z497 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xba783cf1f3038000 0xdd3c1e78f981c000

def z498 : W := mkw 0x62ffffffffb3d735 0xb17fffffffd9eb9a 0xfffffffffff3ff3f 0xfffffffffff9ff9f

def z499 : W := mkw 0x42f7ffdffc02c030 0x217bffeffe016018 0xfbfffffffc03e038 0xfdfffffffe01f01c

def z500 : W := mkw 0x03ffbaddaaeb5000 0x01ffdd6ed575a800 0x10ff30e1c3738000 0x087f9870e1b9c000

def z501 : W := mkw 0x005580dc00000000 0x002ac06e00000000 0x7cffc0fe008c07c1 0xbe7fe07f004603e0

def z502 : W := mkw 0x6002122041319525 0xb00109102098ca92 0xdd87330003739d27 0x6ec3998001b9ce93

def z503 : W := mkw 0x02a27f03bc000000 0x01513f81de000000 0xea00ff1ffc000000 0xf5007f8ffe000000

def z504 : W := mkw 0x0000450000042800 0x0000228000021400 0xed00cf1e008c7fc1 0xf680678f00463fe0

def z505 : W := mkw 0x1055c5de1404284a 0x082ae2ef0a021425 0xffffcffe3c8c7fff 0xffffe7ff1e463fff

def z506 : W := mkw 0x8008000002c80280 0x4004000001640140 0x00000000008c02c0 0x0000000000460160

def z507 : W := mkw 0x005792dc88000000 0x002bc96e44000000 0xfafff3ffcc000000 0xfd7ff9ffe6000000

def z508 : W := mkw 0x2003126889311505 0x9001893444988a82 0x5c8703e80f701d07 0xae4381f407b80e83

def z509 : W := mkw 0x603b3af9ebb3d735 0xb01d9d7cf5d9eb9a 0x10ff30e1c3738000 0x087f9870e1b9c000

def z510 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfbfffffffc00783e 0xfdfffffffe003c1f

def z511 : W := mkw 0x12f4ed973404284a 0x097a76cb9a021425 0x2078cc16308c62d8 0x103c660b1846316c

def z512 : W := mkw 0x2003124888311104 0x9001892444188882 0xde8733e9cc701906 0xef4399f4e6380c83

def z513 : W := mkw 0x8009006803d80781 0xc004803401ec03c0 0x5c8700e803fc07c1 0xae43807401fe03e0

def z514 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa000c1030000000 0xd500060818000000

def z515 : W := mkw 0xe05f92fccbf997a5 0xf02fc97e65fccbd2 0x10ff30e1c3738000 0x087f9870e1b9c000

def z516 : W := mkw 0x0000002001100501 0x8000001000880280 0x0400000003700501 0x0200000001b80280

def z517 : W := mkw 0x901100fe151007cb 0xc808807f0a8803e5 0x020000fe3c0007fe 0x8100007f1e0003ff

def z518 : W := mkw 0x00eeff0002824000 0x00777f8001412000 0xf9ffff000383e001 0x7cffff8001c1f000

def z519 : W := mkw 0x71efff6adffffd6f 0xb8f7ffb56ffffeb7 0xffffffffffffffff 0xffffffffffffffff

def z520 : W := mkw 0x6003576add319525 0xb001abb56e98ca92 0xff87ffffff739d27 0xffc3ffffffb9ce93

def z521 : W := mkw 0x03c7d74e9c6d3800 0x01e3eba74e369c00 0x4487c30e0c7c1800 0x2243e187063e0c00

def z522 : W := mkw 0x807da8fc03da4781 0xc03ed47e01ed23c0 0xfdfffcfe03ffe7c1 0xfefffe7f01fff3e0

def z523 : W := mkw 0x0054809400000000 0x002a404a00000000 0x2078c01600000000 0x103c600b00000000

def z524 : W := mkw 0x03fced9736ce6800 0x01fe76cb9b673400 0x2078cc16308c6000 0x103c660b18463000

def z525 : W := mkw 0x50206d037406e87a 0x28103681ba03743d 0x83003f01fc03f83e 0x41801f80fe01fc1f

def z526 : W := mkw 0x1001456a15142d4b 0x8800a2b50a8a16a5 0xff87cffe3ffc7fff 0xffc3e7ff1ffe3fff

def z527 : W := mkw 0x0028280002824000 0x0014140001412000 0xbb783c103383e639 0xddbc1e0819c1f31c

def z528 : W := mkw 0x401800b163808631 0x200c0058b1c04318 0x3a7800f1f3800639 0x9d3c0078f9c0031c

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100000000806639 0x008000000040331c

def z530 : W := mkw 0x003828b123800601 0x001c145891c00300 0xba783cf1f3800601 0xdd3c1e78f9c00300

def z531 : W := mkw 0x82f7ffdfbc580180 0xc17bffefde2c00c0 0xfefffffffc7c01c0 0xff7ffffffe3e00e0

def z532 : W := mkw 0x805580fc01580781 0xc02ac07e00ac03c0 0x4487c0fe007c07c0 0xa243e07f003e03e0

def z533 : W := mkw 0x004d806803d80501 0x8026c03401ec0280 0x7cffc0e803fc0501 0xbe7fe07401fe0280

def z534 : W := mkw 0x60021220c9319525 0xb00109106498ca92 0x87003301cf739d27 0x43801980e7b9ce93

def z535 : W := mkw 0x0044800000480000 0x0022400000240000 0x4487c000007c0000 0x2243e000003e0000

def z536 : W := mkw 0x0020280120024010 0x0010140090012008 0x00000c0030006018 0x000006001800300c

def z537 : W := mkw 0x0075a8dd20000000 0x003ad46e90000000 0xfafffcfff0000000 0xfd7ffe7ff8000000

def z538 : W := mkw 0x12f4ed973404284a 0x097a76cb9a021425 0xef78cf1e3c8c7fff 0xf7bc678f1e463fff

def z539 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xff87f3ffcfff9fe7 0xffc3f9ffe7ffcff3

def z540 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xda8733e9cf738000 0xed4399f4e7b9c000

def z541 : W := mkw 0x004cc50002cc2800 0x0026628001661400 0xfdffcf0003fc7801 0x7effe78001fe3c00

def z542 : W := mkw 0x0000450000042800 0x0000228000021400 0xef00cf080c8c7d27 0xf780678406463e93

def z543 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x5c8730e9c3738501 0xae439874e1b9c280

def z544 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0x60ffcf1e3c000000 0x307fe78f1e000000

def z545 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x9b8730e1c3738421 0xcdc39870e1b9c210

def z546 : W := mkw 0x100000021400004a 0x080000010a000025 0xcf00031e3c001fff 0xe780018f1e000fff

def z547 : W := mkw 0x402028016002c030 0x20101400b0016018 0xab003c11f083e639 0xd5801e08f841f31c

def z548 : W := mkw 0x403028b161008631 0x20181458b0804318 0xba783cf1f0000638 0xdd3c1e78f800031c

def z549 : W := mkw 0x40386db16386ee31 0x201c36d8b1c37718 0xff78fff1f38ffe39 0xffbc7ff8f9c7ff1c

def z550 : W := mkw 0x70025702dc25b86e 0x38012b816e12dc37 0xef00ff1ffc8fffff 0xf7807f8ffe47ffff

def z551 : W := mkw 0x100000021400004a 0x080000010a000025 0x0000000e0c0001c6 0x00000007060000e3

def z552 : W := mkw 0x82dfd7fe9fd80781 0xc16febff4fec03c0 0x7cffc3fe0ffc07c1 0xbe7fe1ff07fe03e0

def z553 : W := mkw 0x4000002041008421 0x2000001020804210 0x100030e1c3038000 0x08001870e181c000

def z554 : W := mkw 0x60010068c9108525 0xb000803464884292 0x000000e1c0000000 0x00000070e0000000

def z555 : W := mkw 0x100045021404284a 0x080022810a021425 0x4600c31e3c0c1ffe 0xa300618f1e060fff

def z556 : W := mkw 0x0000000000000000 0x0000000000000000 0xca0003080c000000 0xe500018406000000

def z557 : W := mkw 0xc03928fd6392c7b1 0xe01c947eb1c963d8 0xbb783cfff383e7f9 0xddbc1e7ff9c1f3fc

def z558 : W := mkw 0x42ffffffff82c631 0x217fffffffc16318 0xfaffffffff038000 0xfd7fffffff81c000

def z559 : W := mkw 0x02ffffdfbec80000 0x017fffefdf640000 0xfefffffffffc0001 0xff7ffffffffe0000

def z560 : W := mkw 0x0128280002ef7800 0x009414000177bc00 0xbd783c0003fff801 0x5ebc1e0001fffc00

def z561 : W := mkw 0x0000450000042800 0x0000228000021400 0x4400c300000c1800 0x2200618000060c00

def z562 : W := mkw 0x801900fc03d80781 0xc00c807e01ec03c0 0x040000fe03fc07c1 0x8200007f01fe03e0

def z563 : W := mkw 0x805c809402c80280 0x402e404a01640140 0x6c78c01e008c07c1 0xb63c600f004603e0

def z564 : W := mkw 0x4002122041219421 0x200109102090ca10 0xdf8733e1c3739c21 0xefc399f0e1b9ce10

def z565 : W := mkw 0x0001006801100501 0x8000803400880280 0x7c87c0fe03fc07c1 0xbe43e07f01fe03e0

def z566 : W := mkw 0x02d7d7dfbc000000 0x016bebefde000000 0x4287c3fffc000000 0xa143e1fffe000000

def z567 : W := mkw 0x100045021404284a 0x080022810a021425 0xab000f103c807e3f 0xd58007881e403f1f

def z568 : W := mkw 0x21c7d748887d3904 0x90e3eba4443e9c82 0x4487c3080c7c1906 0x2243e184063e0c83

def z569 : W := mkw 0x8000002001100781 0xc0000010008803c0 0x00000000000007c0 0x00000000000003e0

def z570 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xa178ff00008ff800 0x50bc7f800047fc00

def z571 : W := mkw 0x62a37f6bfd319525 0xb151bfb5fe98ca92 0xdf873fe9ff739d27 0xefc39ff4ffb9ce93

def z572 : W := mkw 0x501000b37500867b 0x28080059ba80433d 0x020000fffc0007fe 0x8100007ffe0003ff

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c00000800000501 0xa600000400000280

def z574 : W := mkw 0x01fced9122ce6a10 0x00fe76c891673508 0x2078cc10308c6218 0x103c66081846310c

def z575 : W := mkw 0x40031268c9008421 0x2001893464804210 0xdb8733e9cf038421 0xedc399f4e781c210

def z576 : W := mkw 0x43ffffffffeffe31 0x21fffffffff7ff18 0xfffffffffffffe39 0xffffffffffffff1c

def z577 : W := mkw 0x40386db37782c631 0x201c36d9bbc16318 0xfb78ffffff83e639 0xfdbc7fffffc1f31c

def z578 : W := mkw 0x0001006801100501 0x8000803400880280 0xdf8703e80f701d27 0xefc381f407b80e93

def z579 : W := mkw 0xc07da8fd63dac7b1 0xe03ed47eb1ed63d8 0x10ff30e1c3738000 0x087f9870e1b9c000

def z580 : W := mkw 0x00c6d70000000000 0x00636b8000000000 0x4087c30000000000 0x2043e18000000000

def z581 : W := mkw 0x02f5eddf34000000 0x017af6ef9a000000 0x78ffccfe30000000 0xbc7fe67f18000000

def z582 : W := mkw 0x41a27f016027f830 0x20d13f80b013fc18 0x83003f01f003f838 0x41801f80f801fc1c

def z583 : W := mkw 0x600b1268cbb3d735 0xb005893465d9eb9a 0xdf8733e9cff3ff3f 0xefc399f4e7f9ff9f

def z584 : W := mkw 0x0038289122824210 0x001c144891412108 0xba783cf1f0806218 0xdd3c1e78f840310c

def z585 : W := mkw 0x0003126889100501 0x8001893444880280 0xde8733e9cf700501 0xef4399f4e7b80280

def z586 : W := mkw 0xe05f92fccbf997a5 0xf02fc97e65fccbd2 0x7cfff0ffc3ff87c1 0xbe7ff87fe1ffc3e0

def z587 : W := mkw 0x021312dfbc000000 0x0109896fde000000 0xda8733fffc000000 0xed4399fffe000000

def z588 : W := mkw 0x41feffb163effe31 0x20ff7fd8b1f7ff18 0xfdffffe1c3fff801 0x7efffff0e1fffc00

def z589 : W := mkw 0xe05f92fccbf997a5 0xf02fc97e65fccbd2 0xdfff33e9cf739d27 0xefff99f4e7b9ce93

def z590 : W := mkw 0x100045021404284a 0x080022810a021425 0xa300cf163c8c7afe 0x5180678b1e463d7f

def z591 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x22780cf1f0806638 0x913c0678f840331c

def z592 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xdd8733e1c3739801 0x6ec399f0e1b9cc00

def z593 : W := mkw 0x100000021404284a 0x080000010a021425 0x0700001e3c8c7fff 0x8380000f1e463fff

def z594 : W := mkw 0x41eeff2043effc21 0x20f77f9021f7fe10 0xffffffe1c3fffc21 0xfffffff0e1fffe10

def z595 : W := mkw 0x603928f9eb92c735 0xb01c947cf5c9639a 0xbb783cf9ff83e73f 0xddbc1e7cffc1f39f

def z596 : W := mkw 0x0002120000211000 0x0001090000108800 0x8100330000039800 0x408019800001cc00

def z597 : W := mkw 0xd07dedff77deeffb 0xe83ef6ffbbef77fd 0xffffffffffffffff 0xffffffffffffffff

def z598 : W := mkw 0xe047926cc97995a5 0xf023c93664bccad2 0xdf87f3efcf7f9de7 0xefc3f9f7e7bfcef3

def z599 : W := mkw 0x604f9268cbf99525 0xb027c93465fcca92 0xfffff3e9cfff9d27 0xfffff9f4e7ffce93

def z600 : W := mkw 0x01aa7f0002a77800 0x00d53f800153bc00 0xb9783f000383f801 0x5cbc1f8001c1fc00

def z601 : W := mkw 0x801800b003d80781 0xc00c005801ec03c0 0x3c7800f003fc07c1 0x9e3c007801fe03e0

def z602 : W := mkw 0x11c6d702146d384a 0x08e36b810a369c25 0xef87cf1e3cfc7fff 0xf7c3e78f1e7e3fff

def z603 : W := mkw 0xa05f92fc8bf91785 0xd02fc97e45fc8bc2 0x7cffc3fe0ffc1fc7 0xbe7fe1ff07fe0fe3

def z604 : W := mkw 0x00a27f0000000000 0x00513f8000000000 0x80003f0000000000 0x40001f8000000000

def z605 : W := mkw 0x100045021400004a 0x080022810a000025 0xea00cf1e3c0007fe 0xf500678f1e0003ff

def z606 : W := mkw 0x01eced0002ce6800 0x00f6768001673400 0x7cffcc0003fc6001 0x3e7fe60001fe3000

def z607 : W := mkw 0x02c7d74e9c000000 0x0163eba74e000000 0xea87cf1e3c000000 0xf543e78f1e000000

def z608 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x2078c0fe008c07c0 0x903c607f004603e0

def z609 : W := mkw 0x028257029c000000 0x01412b814e000000 0x000003000c000000 0x0000018006000000

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0x440003080c001906 0x2200018406000c83

def z611 : W := mkw 0x0008002003800601 0x0004001001c00300 0x0000000003800601 0x0000000001c00300

def z612 : W := mkw 0x82fced9736c80280 0x417e76cb9b640140 0x2078cc16308c02c0 0x103c660b18460160

def z613 : W := mkw 0x700000204135bd6f 0xb8000010209adeb7 0x0500000003ffffff 0x0280000001ffffff

def z614 : W := mkw 0x01000000006d3800 0x0080000000369c00 0x04000000007c1800 0x02000000003e0c00

def z615 : W := mkw 0x62f7fffffd108525 0xb17bfffffe884292 0xfafffffffc000526 0xfd7ffffffe000293

def z616 : W := mkw 0x407da8fd6382c631 0x203ed47eb1c16318 0xfbfffcfff383e639 0xfdfffe7ff9c1f31c

def z617 : W := mkw 0x001100dc00000000 0x0008806e00000000 0x000000fe00000000 0x8000007f00000000

def z618 : W := mkw 0x0045804c00000000 0x0022c02600000000 0x4087c00e00000000 0x2043e00700000000

def z619 : W := mkw 0x81c7d74c007d3980 0xc0e3eba6003e9cc0 0x4487c30e007c19c0 0x2243e187003e0ce0

def z620 : W := mkw 0x50386db37786ee7b 0x281c36d9bbc3773d 0xbb78fcf7f38fe6f9 0xddbc7e7bf9c7f37c

def z621 : W := mkw 0x8045804c00580180 0xc022c026002c00c0 0x0087000000700000 0x0043800000380000

def z622 : W := mkw 0x100045021404284a 0x080022810a021425 0x6c00c31e0c8c1fc7 0xb600618f06460fe3

def z623 : W := mkw 0x100045021404284a 0x080022810a021425 0xcf00c30e0c0c1de7 0xe780618706060ef3

def z624 : W := mkw 0x81fdedfc03de6f81 0xc0fef6fe01ef37c0 0x7cffccfe03fc67c1 0xbe7fe67f01fe33e0

def z625 : W := mkw 0x82ffffdfbec80280 0x417fffefdf640140 0xfafffffffc8c02c0 0xfd7ffffffe460160

def z626 : W := mkw 0x81efff4c02ff7980 0xc0f7ffa6017fbcc0 0xfdffff0e03fff9c1 0x7effff8701fffce0

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0x5c87000003700001 0x2e43800001b80000

def z628 : W := mkw 0x60021200c8219024 0x300109006410c812 0xcf003309cc039d27 0xe7801984e601ce93

def z629 : W := mkw 0x403b3af9eb82c631 0x201d9d7cf5c16318 0xfbff3ff9ff83e639 0xfdff9ffcffc1f31c

def z630 : W := mkw 0x02fced9736824210 0x017e76cb9b412108 0x2078cc1630806218 0x103c660b1840310c

def z631 : W := mkw 0x0000000000000000 0x0000000000000000 0x83000c0030006038 0x418006001800301c

def z632 : W := mkw 0x50206d037406e87a 0x28103681ba03743d 0xef00ff1ffc8fffff 0xf7807f8ffe47ffff

def z633 : W := mkw 0x60021220c9219425 0x300109106490ca12 0x9b0033e1cf039c27 0xcd8019f0e781ce13

def z634 : W := mkw 0x12c7d74e9c04284a 0x0963eba74e021425 0x4487c30e0c0c19c6 0x2243e18706060ce3

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x6c00c000008c0001 0x3600600000460000

def z636 : W := mkw 0x0038289122824210 0x001c144891412108 0xab780c1030806639 0xd5bc06081840331c

def z637 : W := mkw 0x8044800400480080 0x4022400200240040 0x0000c006000c00c0 0x0000600300060060

def z638 : W := mkw 0x41eeff0162eff830 0x20f77f80b177fc18 0xffffff01f3fff839 0x7fffff80f9fffc1c

def z639 : W := mkw 0x42f7fffffd008631 0x217bfffffe804318 0xfafffffffc000638 0xfd7ffffffe00031c

def z640 : W := mkw 0x100000021400004a 0x080000010a000025 0xab000c1e3c8067ff 0xd580060f1e4033ff

def z641 : W := mkw 0x402828204382c421 0x2014141021c16210 0xbb783ce1c383e421 0xddbc1e70e1c1f210

def z642 : W := mkw 0x8045806c01580581 0xc022c03600ac02c0 0x5c87c0ee037c05c1 0xae43e07701be02e0

def z643 : W := mkw 0x0008000002c80000 0x0004000001640000 0x0400000003fc0001 0x0200000001fe0000

def z644 : W := mkw 0x100000000004284a 0x0800000000021425 0x010000000000783e 0x0080000000003c1f

def z645 : W := mkw 0x905dc5fe17dc2fcb 0xc82ee2ff0bee17e5 0x7cffccfe33fc67d9 0xbe7fe67f19fe33ec

def z646 : W := mkw 0x905dc5fe17dc2fcb 0xc82ee2ff0bee17e5 0x7cffc3fe0ffc1fc7 0xbe7fe1ff07fe0fe3

def z647 : W := mkw 0xc07da8fd63dac7b1 0xe03ed47eb1ed63d8 0xbbff3cf1f3f3e639 0xddff9e78f9f9f31c

def z648 : W := mkw 0xc07ca8b563cac6b1 0x603e545ab1e56358 0xbb78fcf7f38fe6f9 0xddbc7e7bf9c7f37c

def z649 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x458703080f739d27 0x22c3818407b9ce93

def z650 : W := mkw 0x100045021404284a 0x080022810a021425 0x2200cc1e3c8c67fe 0x9100660f1e4633ff

def z651 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x30ffc0f603fc02c0 0x187fe07b01fe0160

def z652 : W := mkw 0x6000002041108525 0xb000001020884292 0x0000000000000526 0x0000000000000293

def z653 : W := mkw 0x100045021404284a 0x080022810a021425 0xea00cf1e3c8c62d8 0xf500678f1e46316c

def z654 : W := mkw 0x0000000000000000 0x0000000000000000 0xef00c31e0c8c1fe7 0xf780618f06460ff3

def z655 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x7cffc0e003fc0001 0x3e7fe07001fe0000

def z656 : W := mkw 0x50386db37786ee7b 0x281c36d9bbc3773d 0xbb783ff1ff83fe3f 0xddbc1ff8ffc1ff1f

def z657 : W := mkw 0x61efba68cbfbd525 0xb0f7dd3465fdea92 0x10ff30e1c3738000 0x087f9870e1b9c000

def z658 : W := mkw 0x0182570000253800 0x00c12b8000129c00 0x0000030000001800 0x0000018000000c00

def z659 : W := mkw 0x0000450214000000 0x000022810a000000 0xef00cf1e3c001d27 0xf780678f1e000e93

def z660 : W := mkw 0x0055c5de14000000 0x002ae2ef0a000000 0xfaffcffe3c000000 0xfd7fe7ff1e000000

def z661 : W := mkw 0x807da8fd23da4791 0xc03ed47e91ed23c8 0x7cffccfe33fc67d9 0xbe7fe67f19fe33ec

def z662 : W := mkw 0x100000021400004a 0x080000010a000025 0x00000016300002d8 0x0000000b1800016c

def z663 : W := mkw 0x82f7ffffbd100781 0xc17bffffde8803c0 0xfafffffffc0007c0 0xfd7ffffffe0003e0

def z664 : W := mkw 0xe01312fcc93197a5 0xf009897e6498cbd2 0xdf8733ffcf739fe7 0xefc399ffe7b9cff3

def z665 : W := mkw 0x821100ffbd100781 0xc108807fde8803c0 0x020000fffc0007c0 0x8100007ffe0003e0

def z666 : W := mkw 0x100045021404284a 0x080022810a021425 0xcf000f083c007d3f 0xe78007841e003e9f

def z667 : W := mkw 0x0008000002824210 0x0004000001412108 0x0000000000806218 0x000000000040310c

def z668 : W := mkw 0x01eced0002ce6800 0x00f6768001673400 0xed78cf00008c7801 0x76bc678000463c00

def z669 : W := mkw 0x03feff9736ef7800 0x01ff7fcb9b77bc00 0xfdffff1633fff801 0x7effff8b19fffc00

def z670 : W := mkw 0x63fffffffffffd25 0xb1fffffffffffe92 0xfffffffffffffd27 0xfffffffffffffe93

def z671 : W := mkw 0x100045021404284a 0x080022810a021425 0x6400cf1e3c8c7bde 0x3200678f1e463def

def z672 : W := mkw 0x41fcedb163ceee31 0x20fe76d8b1e77718 0xbb78fcf1f38fe639 0xddbc7e78f9c7f31c

def z673 : W := mkw 0x2000000000311104 0x9000000000188882 0x0400000000701906 0x0200000000380c83

def z674 : W := mkw 0x01efff488aef7800 0x00f7ffa44577bc00 0xffffffe9cffff801 0xfffffff4e7fffc00

def z675 : W := mkw 0x100045021404284a 0x080022810a021425 0xc700cf0e3c0c79fe 0x638067871e063cff

def z676 : W := mkw 0x0108000002ce6800 0x0084000001673400 0x00000000008c6000 0x0000000000463000

def z677 : W := mkw 0x100000021400004a 0x080000010a000025 0x020000003c00003e 0x010000001e00001f

def z678 : W := mkw 0x100045021404284a 0x080022810a021425 0xed00cf0e0c8c79c7 0x7680678706463ce3

def z679 : W := mkw 0x001900f803900701 0x800c807c01c80380 0x7cff00f803f00701 0xbe7f807c01f80380

def z680 : W := mkw 0x402828204382c631 0x2014141021c16318 0xb9783c000383e639 0x5cbc1e0001c1f31c

def z681 : W := mkw 0x0000000000000000 0x0000000000000000 0xcd00030000001801 0x6680018000000c00

def z682 : W := mkw 0x7003126add31956f 0xb80189356e98cab7 0xdf8733ffff739fff 0xefc399ffffb9cfff

def z683 : W := mkw 0x100045021404284a 0x080022810a021425 0x4500c30e0c8c7fff 0x2280618706463fff

def z684 : W := mkw 0x2001004888100104 0x9000802444080082 0x000000080c000106 0x0000000406000083

def z685 : W := mkw 0x104cc50216cc284a 0x082662810b661425 0xffffcf1e3ffc7fff 0xffffe78f1ffe3fff

def z686 : W := mkw 0x02c4c50614000000 0x016262830a000000 0x0000c00600000000 0x0000600300000000

def z687 : W := mkw 0x0000450000000000 0x0000228000000000 0xe800cf0000000000 0x7400678000000000

def z688 : W := mkw 0x60035768c935bd25 0xb001abb4649ade92 0xff87ffe9cffffd27 0xffc3fff4e7fffe93

def z689 : W := mkw 0x100257021425384a 0x08012b810a129c25 0xff87ff1e3fffffff 0xffc3ff8f1fffffff

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000c1030806218 0x100006081840310c

def z691 : W := mkw 0x60021200c8219024 0x300109006410c812 0xdf873301cf739827 0x6fc39980e7b9cc13

def z692 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x78ffc0fe03700000 0xbc7fe07f01b80000

def z693 : W := mkw 0x402828016282c030 0x20141400b1416018 0xbb783c01f383e039 0x5dbc1e00f9c1f01c

def z694 : W := mkw 0x905d80fe17d807cb 0xc82ec07f0bec03e5 0x7effc0fe3ffc07ff 0xbf7fe07f1ffe03ff

def z695 : W := mkw 0xc07da8fd63dac7b1 0xe03ed47eb1ed63d8 0x7cfff0ffc3ff87c1 0xbe7ff87fe1ffc3e0

def z696 : W := mkw 0x02f6ff97bc000000 0x017b7fcbde000000 0xa278ff17fc000000 0x513c7f8bfe000000

def z697 : W := mkw 0x2003124888311104 0x9001892444188882 0xcf8703080c701d27 0xe7c3818406380e93

def z698 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x38ff00f003f00601 0x9c7f807801f80300

def z699 : W := mkw 0x81fffffc03ff7f81 0xc0fffffe01ffbfc0 0xfdffffe003fff801 0x7efffff001fffc00

def z700 : W := mkw 0x41ba7fb163a7fe31 0x20dd3fd8b1d3ff18 0xbb783ff1f383fe39 0xddbc1ff8f9c1ff1c

def z701 : W := mkw 0x62f7bafde9319525 0xb17bdd7ef498ca92 0x10ff30e1c3738000 0x087f9870e1b9c000

def z702 : W := mkw 0x621312fffd319525 0xb109897ffe98ca92 0xdf8733ffff739d27 0xefc399ffffb9ce93

def z703 : W := mkw 0x7001006add10856f 0xb80080356e8842b7 0x020000fffc0007fe 0x8100007ffe0003ff

def z704 : W := mkw 0x005580fc01100501 0x802ac07e00880280 0x7cffc0fe03700501 0xbe7fe07f01b80280

def z705 : W := mkw 0x001800b003800601 0x000c005801c00300 0x7c78c0fe038c07c1 0xbe3c607f01c603e0

def z706 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xb9783ce1c383e001 0x5cbc1e70e1c1f000

def z707 : W := mkw 0x400800204382c631 0x2004001021c16318 0x83000c003383e639 0x4180060019c1f31c

def z708 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xfdffff0003fffe39 0x7effff8001ffff1c

def z709 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xbb783ff1ff83fe3f 0xddbc1ff8ffc1ff1f

def z710 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfffffffffc8c1fe7 0xfffffffffe460ff3

def z711 : W := mkw 0x004c800002e91000 0x0026400001748800 0x7dffc00003ff9801 0x3effe00001ffcc00

def z712 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0x78fff3ffcc000000 0xbc7ff9ffe6000000

def z713 : W := mkw 0x7108002043fffd6f 0xb884001021fffeb7 0x0500000003ffffff 0x0280000001ffffff

def z714 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfefffffffc000501 0xff7ffffffe000280

def z715 : W := mkw 0x10f6ff933404284a 0x087b7fc99a021425 0xfffffffffc8c7fff 0xfffffffffe463fff

def z716 : W := mkw 0x0047924888000000 0x0023c92444000000 0xfafff3e9cc000000 0xfd7ff9f4e6000000

def z717 : W := mkw 0x403028916002c030 0x20181448b0016018 0xbb783cf1f083e639 0xddbc1e78f841f31c

def z718 : W := mkw 0x0030289120000000 0x0018144890000000 0x387830f1c0000000 0x9c3c1878e0000000

def z719 : W := mkw 0x005580dd20000000 0x002ac06e90000000 0x7affc0fff0000000 0xbd7fe07ff8000000

def z720 : W := mkw 0x805d80dc02d80380 0xc02ec06e016c01c0 0x6cffc01e00fc07c1 0xb67fe00f007e03e0

def z721 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfefffffffc8c1fc7 0xff7ffffffe460fe3

def z722 : W := mkw 0x11a27f021427784a 0x08d13f810a13bc25 0x81003f000c03f806 0x40801f800601fc03

def z723 : W := mkw 0x7003576add35bd6f 0xb801abb56e9adeb7 0x3087fcf7f3ffe2d8 0x1843fe7bf9fff16c

def z724 : W := mkw 0x025580dda8000000 0x012ac06ed4000000 0x78ffc0ffc0000000 0xbc7fe07fe0000000

def z725 : W := mkw 0xc03828b163dac7b1 0xe01c1458b1ed63d8 0xbb783cf1f3f3e639 0xddbc1e78f9f9f31c

def z726 : W := mkw 0x621100fde9108525 0xb108807ef4884292 0x020000e9cc000526 0x81000074e6000293

def z727 : W := mkw 0xc008002043d887b1 0xe004001021ec43d8 0x0400000003fc07f9 0x0200000001fe03fc

def z728 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x64ffc01e03fc07c1 0x327fe00f01fe03e0

def z729 : W := mkw 0x01eeff0216ef7800 0x00f77f810b77bc00 0xffffff1e3fffffc1 0xffffff8f1fffffe0

def z730 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xdd8733e9cf739907 0x6ec399f4e7b9cc83

def z731 : W := mkw 0xc05d80fc43d887a1 0xe02ec07e21ec43d0 0x7dffc0fe03ff87e1 0xbeffe07f01ffc3f0

def z732 : W := mkw 0x82aa7f23bfd80781 0xc1553f91dfec03c0 0x86003f01fffc07c1 0x43001f80fffe03e0

def z733 : W := mkw 0x6008002043b3d735 0xb004001021d9eb9a 0x0100000003f3e639 0x0080000001f9f31c

def z734 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0x93ff3fe1fc00783e 0x49ff9ff0fe003c1f

def z735 : W := mkw 0x804c802003d80781 0xc026401001ec03c0 0x7cffc01e03fc07c1 0xbe7fe00f01fe03e0

def z736 : W := mkw 0xc05d80fc43d887a1 0xe02ec07e21ec43d0 0x7cfff0ffc3ff87c1 0xbe7ff87fe1ffc3e0

def z737 : W := mkw 0x82f7badda8580180 0xc17bdd6ed42c00c0 0x10ff30e1c0700000 0x087f9870e0380000

def z738 : W := mkw 0x500800204382c67b 0x2804001021c1633d 0x010000000383e7ff 0x0080000001c1f3ff

def z739 : W := mkw 0xf008002043fdbfef 0xf804001021fedff7 0x0500000003ffffff 0x0280000001ffffff

def z740 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0x10ff3c000373e000 0x087f9e0001b9f000

def z741 : W := mkw 0x4108002043ebd631 0x2084001021f5eb18 0x0000000003738000 0x0000000001b9c000

def z742 : W := mkw 0x7108452257fffd6f 0xb88422912bfffeb7 0xef00cf1e3fffffff 0xf780678f1fffffff

def z743 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xfcffff00037f9800 0x7e7fff8001bfcc00

def z744 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xffffff1e3ffff9c7 0xffffff8f1ffffce3

def z745 : W := mkw 0x004e920002e91000 0x0027490001748800 0xddff330003739801 0x6eff998001b9cc00

def z746 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xdf8733e9cff3ff3f 0xefc399f4e7f9ff9f

def z747 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xfdffff0e0fffffff 0x7effff8707ffffff

def z748 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x5c8733e9cf739d07 0xae4399f4e7b9ce83

def z749 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfefffffffc0c01c0 0xff7ffffffe0600e0

def z750 : W := mkw 0x22f7ffdfbc311104 0x917bffefde188882 0xfffffffffc701d27 0xfffffffffe380e93

def z751 : W := mkw 0x01eeff0002ef7a10 0x00f77f800177bd08 0xfdffff0003fffa19 0x7effff8001fffd0c

def z752 : W := mkw 0x03f7ffdda86d3800 0x01fbffeed4369c00 0x54fff3e1c07c1800 0x2a7ff9f0e03e0c00

def z753 : W := mkw 0x62f4edb775319525 0xb17a76dbba98ca92 0x2578cc1633739d27 0x12bc660b19b9ce93

def z754 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0xfdfff30003ff9801 0x7efff98001ffcc00

def z755 : W := mkw 0x2003124888311104 0x9001892444188882 0xdf8733e9cf739907 0xefc399f4e7b9cc83

def z756 : W := mkw 0x12f4ed973404284a 0x097a76cb9a021425 0xbb78fcf7f08c66f9 0xddbc7e7bf846337c

def z757 : W := mkw 0x0057d7de9c000000 0x002bebef4e000000 0xfafffffffc000000 0xfd7ffffffe000000

def z758 : W := mkw 0x114c800002ef784a 0x08a640000177bc25 0x7dffc01e03ffffff 0xbeffe00f01ffffff

def z759 : W := mkw 0x02f7badda8211000 0x017bdd6ed4108800 0xddff33e1c3739801 0x6eff99f0e1b9cc00

def z760 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0xfafffcfff0000000 0xfd7ffe7ff8000000

def z761 : W := mkw 0x6008002043b3d735 0xb004001021d9eb9a 0x0500000003739d27 0x0280000001b9ce93

def z762 : W := mkw 0x13f7ffdfbc27784a 0x09fbffefde13bc25 0xfbfffffffc03f83e 0xfdfffffffe01fc1f

def z763 : W := mkw 0x0003124888211000 0x0001892444108800 0xdf8733e9cf739d27 0xefc399f4e7b9ce93

def z764 : W := mkw 0x005580dc88000000 0x002ac06e44000000 0x7affc0ffcc000000 0xbd7fe07fe6000000

def z765 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xff78fcf1f38fe639 0xffbc7e78f9c7f31c

def z766 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0xdfff33e9cc001d27 0xefff99f4e6000e93

def z767 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x7cffc0fe037c01c0 0xbe7fe07f01be00e0

def z768 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0x65ffcf0003fff801 0x32ffe78001fffc00

def z769 : W := mkw 0x002a7f0002a77800 0x00153f800153bc00 0xfdffff0003fff801 0x7effff8001fffc00

def z770 : W := mkw 0x601100f8c9108725 0xb008807c64884392 0x020000f9cc000726 0x8100007ce6000393

def z771 : W := mkw 0x400845204386ee31 0x2004229021c37718 0xed00cf00038ffe39 0x7680678001c7ff1c

def z772 : W := mkw 0x83f7ffdfbc7d3980 0xc1fbffefde3e9cc0 0xfefffffffc7c19c0 0xff7ffffffe3e0ce0

def z773 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x14ff300003ff8001 0x0a7f980001ffc000

def z774 : W := mkw 0x50386db37786ee7b 0x281c36d9bbc3773d 0x5478f3efcf0f99c6 0x2a3c79f7e787cce3

def z775 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfffffffffc001801 0xfffffffffe000c00

def z776 : W := mkw 0x023128dda8000000 0x0118946ed4000000 0xba783cf1f0000000 0xdd3c1e78f8000000

def z777 : W := mkw 0x6108002043fbd525 0xb084001021fdea92 0x0000000003738000 0x0000000001b9c000

def z778 : W := mkw 0x403828916282c030 0x201c1448b1416018 0xbb783cf1f383e039 0xddbc1e78f9c1f01c

def z779 : W := mkw 0x00223a0000211000 0x00111d0000108800 0xfdff3f0003739801 0x7eff9f8001b9cc00

def z780 : W := mkw 0x00323a91a8000000 0x00191d48d4000000 0xba783ff1fc000000 0xdd3c1ff8fe000000

def z781 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xfb78fcfff383e639 0xfdbc7e7ff9c1f31c

def z782 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x7cffc3fe0ffc1fc7 0xbe7fe1ff07fe0fe3

def z783 : W := mkw 0xe05d80fdebd887b5 0xf02ec07ef5ec43da 0x7effc0fffffc07ff 0xbf7fe07ffffe03ff

def z784 : W := mkw 0x805d80fd23d80791 0xc02ec07e91ec03c8 0x7cffc0fe33fc07d9 0xbe7fe07f19fe03ec

def z785 : W := mkw 0xc00800204392c7b1 0xe004001021c963d8 0x010000000383e7f9 0x0080000001c1f3fc

def z786 : W := mkw 0x92f7ffdfbc5c29ca 0xc97bffefde2e14e5 0xfffffffffcfc7fff 0xfffffffffe7e3fff

def z787 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfefffffffc001906 0xff7ffffffe000c83

def z788 : W := mkw 0xc01100fc411087a1 0xe008807e208843d0 0x020000ffc00007e0 0x8100007fe00003f0

def z789 : W := mkw 0x10337fdbbc04284a 0x0819bfedde021425 0xfffffffffc8c7fff 0xfffffffffe463fff

def z790 : W := mkw 0x825d80fdabd80781 0xc12ec07ed5ec03c0 0x7cffc0ffc3fc07c1 0xbe7fe07fe1fe03e0

def z791 : W := mkw 0x00f6ba9120000000 0x007b5d4890000000 0xbaff3cf1f0000000 0xdd7f9e78f8000000

def z792 : W := mkw 0x905dc5fe17dc2fcb 0xc82ee2ff0bee17e5 0x93ff0fe03f70783e 0x49ff87f01fb83c1f

def z793 : W := mkw 0x00f6ff9334000000 0x007b7fc99a000000 0xfafffffffc000000 0xfd7ffffffe000000

def z794 : W := mkw 0x01f6ff91206d3800 0x00fb7fc890369c00 0xfefffff1f07c1800 0xff7ffff8f83e0c00

def z795 : W := mkw 0x203b3ad9aab35314 0x901d9d6cd559a98a 0x64ff0f183cf07b1e 0x327f878c1e783d8f

def z796 : W := mkw 0x82f7ffdfbc000280 0x417bffefde000140 0xfafffffffc0002c0 0xfd7ffffffe000160

def z797 : W := mkw 0x00e7ff4a9c000000 0x0073ffa54e000000 0xfafffffffc000000 0xfd7ffffffe000000

def z798 : W := mkw 0xe05d80fc43d887a5 0xf02ec07e21ec43d2 0x7cffc0fe03fc07e7 0xbe7fe07f01fe03f3

def z799 : W := mkw 0x00e7ba4888000000 0x0073dd2444000000 0xdaff33e9cc000000 0xed7f99f4e6000000

def z800 : W := mkw 0x031900dfbeef7800 0x018c806fdf77bc00 0x070000fffffff801 0x8380007ffffffc00

def z801 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xd78733e9cf739926 0x6bc399f4e7b9cc93

def z802 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0x93ff3f003f73f83e 0x49ff9f801fb9fc1f

def z803 : W := mkw 0x021100dfbc000000 0x0108806fde000000 0x3a7800fffc000000 0x9d3c007ffe000000

def z804 : W := mkw 0x00337fdbbc000000 0x0019bfedde000000 0xfafffffffc000000 0xfd7ffffffe000000

def z805 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xb3783cf1f383e238 0x59bc1e78f9c1f11c

def z806 : W := mkw 0x025580dfbc000000 0x012ac06fde000000 0x2278c0fffc000000 0x913c607ffe000000

def z807 : W := mkw 0x805d80fc03da4791 0xc02ec07e01ed23c8 0x7cffc0fe03fc67d9 0xbe7fe07f01fe33ec

def z808 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x108733e1cf739806 0x084399f0e7b9cc03

def z809 : W := mkw 0x0030289120024010 0x0018144890012008 0xba783cf1f0006018 0xdd3c1e78f800300c

def z810 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfbffffffff038001 0xfdffffffff81c000

def z811 : W := mkw 0x12f5eddfbc04284a 0x097af6efde021425 0x2278ccfffc8c67fe 0x913c667ffe4633ff

def z812 : W := mkw 0x403028916002c030 0x20181448b0016018 0x93783ce1f003e038 0x49bc1e70f801f01c

def z813 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xba783cf1f383e218 0xdd3c1e78f9c1f10c

def z814 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x78ffc0fe03fc02c0 0xbc7fe07f01fe0160

def z815 : W := mkw 0x014c800002eb5000 0x00a640000175a800 0x7cffc00003ff8001 0x3e7fe00001ffc000

def z816 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x38ff30f1c0000000 0x9c7f9878e0000000

def z817 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x92ff33e1cc000000 0x497f99f0e6000000

def z818 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x568733e9cf739d26 0xab4399f4e7b9ce93

def z819 : W := mkw 0x32c7d74e9c35394e 0x9963eba74e1a9ca7 0x4487c30e0c7c19c6 0x2243e187063e0ce3

def z820 : W := mkw 0x400800204382c631 0x2004001021c16318 0x010000000303e038 0x008000000181f01c

def z821 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xffffff1033fff801 0xffffff8819fffc00

def z822 : W := mkw 0x6008002043a3d635 0x3004001021d1eb1a 0x010000000383fe3f 0x0080000001c1ff1f

def z823 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x30fff0f7c0000000 0x187ff87be0000000

def z824 : W := mkw 0x100045021404284a 0x080022810a021425 0xa300cf1e3c8c7ffe 0xd180678f1e463fff

def z825 : W := mkw 0x03f7ffdfbc066800 0x01fbffefde033400 0xfafffffffc006000 0xfd7ffffffe003000

def z826 : W := mkw 0x01eeff0216ef7800 0x00f77f810b77bc00 0xfdffff1633fff801 0x7effff8b19fffc00

def z827 : W := mkw 0xd01145ff7514affb 0xe808a2ffba8a57fd 0xef00cffffc8c7fff 0xf78067fffe463fff

def z828 : W := mkw 0x0074a89520000000 0x003a544a90000000 0xba78fcf7f0000000 0xdd3c7e7bf8000000

def z829 : W := mkw 0x02f5eddfbc000000 0x017af6efde000000 0xea78cffffc000000 0xf53c67fffe000000

def z830 : W := mkw 0x01eeff0002eb5000 0x00f77f800175a800 0x50fff30003738000 0x287ff98001b9c000

def z831 : W := mkw 0x0030289120000000 0x0018144890000000 0xba783cf1f0800601 0xdd3c1e78f8400300

def z832 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0xfdffccfe03fc67c1 0xfeffe67f01fe33e0

def z833 : W := mkw 0x71a27f02dc27f86e 0x38d13f816e13fc37 0x83003f01fc03f83e 0x41801f80fe01fc1f

def z834 : W := mkw 0x00233a4888000000 0x00119d2444000000 0xfaff3fe9cc000000 0xfd7f9ff4e6000000

def z835 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xfdffff1033fffa19 0x7effff8819fffd0c

def z836 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xddfff300037f9801 0x6efff98001bfcc00

def z837 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xffffff1e33fffff9 0xffffff8f19fffffc

def z838 : W := mkw 0xc01100fd611087b1 0xe008807eb08843d8 0xef00ccfff08c67f9 0xf780667ff84633fc

def z839 : W := mkw 0x42cfd76edf82c631 0x2167ebb76fc16318 0x4187c30e0f83e639 0x20c3e18707c1f31c

def z840 : W := mkw 0xc03828b163dac7b1 0xe01c1458b1ed63d8 0xff78fcfff3ffe7f9 0xffbc7e7ff9fff3fc

def z841 : W := mkw 0x11eeba0216eb504a 0x08f75d010b75a825 0x12ff301e3f7387fe 0x897f980f1fb9c3ff

def z842 : W := mkw 0x02f7ffdfbc480000 0x017bffefde240000 0xfefffffffc7c0000 0xff7ffffffe3e0000

def z843 : W := mkw 0x805580dc00580180 0xc02ac06e002c00c0 0x64ffc01e007c01c0 0x327fe00f003e00e0

def z844 : W := mkw 0x60031248c8219024 0x300189246410c812 0xdf8733e9cf739827 0xefc399f4e7b9cc13

def z845 : W := mkw 0x11fced9336ce6a5a 0x08fe76c99b67352d 0x2078cc16308c62d8 0x103c660b1846316c

def z846 : W := mkw 0x805580dc00580180 0xc02ac06e002c00c0 0x7cffc0fe00fc07c1 0xbe7fe07f007e03e0

def z847 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x5cff300003738001 0x2e7f980001b9c000

def z848 : W := mkw 0x02f7badfbc000000 0x017bdd6fde000000 0x10ff30f7f0000000 0x087f987bf8000000

def z849 : W := mkw 0x0010009000000000 0x0008004800000000 0xba7830f1c0000000 0xdd3c1878e0000000

def z850 : W := mkw 0xe01100fcc91087a5 0xf008807e648843d2 0x020000e9cc000526 0x81000074e6000293

def z851 : W := mkw 0xa2f7ffdfbc791184 0xd17bffefde3c88c2 0xfefffffffc7c19c6 0xff7ffffffe3e0ce3

def z852 : W := mkw 0x6008002043b3d735 0xb004001021d9eb9a 0xef000f183ff3ff3f 0xf780078c1ff9ff9f

def z853 : W := mkw 0x01eeff0002eb5000 0x00f77f800175a800 0xfcffff0003ff8001 0x7e7fff8001ffc000

def z854 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xfdffff1633ffffff 0x7effff8b19ffffff

def z855 : W := mkw 0x103028933400004a 0x081814499a000025 0xba783cfffc0007fe 0xdd3c1e7ffe0003ff

def z856 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0xffffc0fe03fc07e1 0xffffe07f01fe03f0

def z857 : W := mkw 0x03f7ffdfbc6f7800 0x01fbffefde37bc00 0xfffffffffc7ff800 0xfffffffffe3ffc00

def z858 : W := mkw 0x012a3a0002ef7800 0x00951d000177bc00 0xfdff3f0003fff801 0x7eff9f8001fffc00

def z859 : W := mkw 0x0075a8dd20000000 0x003ad46e90000000 0xbaff3cf1f0000000 0xdd7f9e78f8000000

def z860 : W := mkw 0x02f7ffdfbc000210 0x017bffefde000108 0xfafffffffc000218 0xfd7ffffffe00010c

def z861 : W := mkw 0x805580fc01580581 0xc02ac07e00ac02c0 0x7cffc0fe037c05c1 0xbe7fe07f01be02e0

def z862 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xdf87f3efcf7f9de7 0xefc3f9f7e7bfcef3

def z863 : W := mkw 0x0075eddf34000000 0x003af6ef9a000000 0xfafffffffc000000 0xfd7ffffffe000000

def z864 : W := mkw 0x02f7badfbc000000 0x017bdd6fde000000 0x12ff30e1fc000000 0x097f9870fe000000

def z865 : W := mkw 0x81b37ffc01377f81 0xc0d9bffe009bbfc0 0x81003ffe0003ffc0 0xc0801fff0001ffe0

def z866 : W := mkw 0x805d80dc02d80180 0xc02ec06e016c00c0 0x7cffc0fe03fc01c1 0xbe7fe07f01fe00e0

def z867 : W := mkw 0x10306d933404284a 0x081836c99a021425 0xbb783ff1fc00783e 0xddbc1ff8fe003c1f

def z868 : W := mkw 0x01e6ff00006d3800 0x00f37f8000369c00 0xfdffff00037f9801 0x7effff8001bfcc00

def z869 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x10ffc0e6037c00c0 0x087fe07301be0060

def z870 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xffffff003fffffff 0x7fffff801fffffff

def z871 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x91ff330003739800 0x48ff998001b9cc00

def z872 : W := mkw 0x41d6d7b1616dbe31 0x20eb6bd8b0b6df18 0x4687c3f1f07c1e38 0xa343e1f8f83e0f1c

def z873 : W := mkw 0x61cfd768cbfffd25 0xb0e7ebb465fffe92 0x4587c3080ffffd27 0x22c3e18407fffe93

def z874 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x50ff33e9cc000000 0x287f99f4e6000000

def z875 : W := mkw 0x0030289120000210 0x0018144890000108 0xba783cf1f0000218 0xdd3c1e78f800010c

def z876 : W := mkw 0x7008002043b7ff7f 0xb804001021dbffbf 0x0500000003ffffff 0x0280000001ffffff

def z877 : W := mkw 0x02f4a89520000000 0x017a544a90000000 0x107830e1c0000000 0x083c1870e0000000

def z878 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x7cffc0f603fc02c1 0x3e7fe07b01fe0160

def z879 : W := mkw 0x02302893bc000000 0x01181449de000000 0xba783cf1fc000000 0xdd3c1e78fe000000

def z880 : W := mkw 0x61eded68cbdeed25 0xb0f6f6b465ef7692 0x2278cce9cc8c6526 0x913c6674e6463293

def z881 : W := mkw 0x02b27f93bc000000 0x01593fc9de000000 0x92783fe1fc000000 0x493c1ff0fe000000

def z882 : W := mkw 0x103028912004284a 0x0818144890021425 0xbf783cf1f08c7fff 0xdfbc1e78f8463fff

def z883 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfbfffffffc8c66f9 0xfdfffffffe46337c

def z884 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0xfefff0ffc3fc07c1 0xff7ff87fe1fe03e0

def z885 : W := mkw 0x804d804c02d80180 0xc026c026016c00c0 0x7cffc01e03fc07c1 0xbe7fe00f01fe03e0

def z886 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xfb783ff9ff83e639 0xfdbc1ffcffc1f31c

def z887 : W := mkw 0x10306d933404284a 0x081836c99a021425 0xfe78fffffc0c19c6 0xff3c7ffffe060ce3

def z888 : W := mkw 0x10306d933404284a 0x081836c99a021425 0xba78fcf7f08c62d8 0xdd3c7e7bf846316c

def z889 : W := mkw 0xe05d80fccbd887a5 0xf02ec07e65ec43d2 0xffffc3ffcffc1fe7 0xffffe1ffe7fe0ff3

def z890 : W := mkw 0x12f7badda804284a 0x097bdd6ed4021425 0x15ff30e1c08c7fff 0x0aff9870e0463fff

def z891 : W := mkw 0x41aa7f2043a7fe31 0x20d53f9021d3ff18 0x81003f000383fe39 0x40801f8001c1ff1c

def z892 : W := mkw 0x023128dfbc000000 0x0118946fde000000 0x127830fffc000000 0x893c187ffe000000

def z893 : W := mkw 0xd008002043deeffb 0xe804001021ef77fd 0x0500000003ffffff 0x0280000001ffffff

def z894 : W := mkw 0x601100f9e9108735 0xb008807cf488439a 0x020000f1f0000638 0x81000078f800031c

def z895 : W := mkw 0x400a122043a3d631 0x2005091021d1eb18 0xdd87330003f3fe39 0x6ec3998001f9ff1c

def z896 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xffffff1e0fffffe7 0xffffff8f07fffff3

def z897 : W := mkw 0x13f7ffdfbc27784a 0x09fbffefde13bc25 0xfffffffffc8fffff 0xfffffffffe47ffff

def z898 : W := mkw 0xc01100fd611087b1 0xe008807eb08843d8 0x000000e1c0000000 0x00000070e0000000

def z899 : W := mkw 0x601100f9e9108525 0xb008807cf4884292 0x020000f9fc000526 0x8100007cfe000293

def z900 : W := mkw 0x0046920000211000 0x0023490000108800 0xfdfff30003739801 0x7efff98001b9cc00

def z901 : W := mkw 0x03eeff029eef7800 0x01f77f814f77bc00 0xfdffff000ffff801 0x7effff8007fffc00

def z902 : W := mkw 0x01eeff0216ef7800 0x00f77f810b77bc00 0xffffff1e3ffffe39 0xffffff8f1fffff1c

def z903 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0xfafff3ffcc000000 0xfd7ff9ffe6000000

def z904 : W := mkw 0xe008002043f997a5 0xf004001021fccbd2 0x0000000003738000 0x0000000001b9c000

def z905 : W := mkw 0x100045021404284a 0x080022810a021425 0x6500cf1e3c8c7fff 0x3280678f1e463fff

def z906 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x7dffc0fe03fc1fe7 0xbeffe07f01fe0ff3

def z907 : W := mkw 0xe05d80fccbd887a5 0xf02ec07e65ec43d2 0xfffff0ffcfff87e7 0xfffff87fe7ffc3f3

def z908 : W := mkw 0xc008002043d887a1 0xe004001021ec43d0 0x0500000003ff87e1 0x0280000001ffc3f0

def z909 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x30fff00003ff8000 0x187ff80001ffc000

def z910 : W := mkw 0x13f7ffdfbc6d384a 0x09fbffefde369c25 0xfffffffffcfc7fff 0xfffffffffe7e3fff

def z911 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xb9ff3f0003f3f801 0x5cff9f8001f9fc00

def z912 : W := mkw 0x004e920002e91000 0x0027490001748800 0x7cfff00003ff8001 0x3e7ff80001ffc000

def z913 : W := mkw 0x621145fffd108525 0xb108a2fffe884292 0xef00cffffc001d27 0xf78067fffe000e93

def z914 : W := mkw 0x01eeff0122ef7800 0x00f77f809177bc00 0xffffff01f3fff801 0x7fffff80f9fffc00

def z915 : W := mkw 0x0030289120000000 0x0018144890000000 0x22780cf1f0000000 0x913c0678f8000000

def z916 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0x35fffc0003fff801 0x1afffe0001fffc00

def z917 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0x7cfff30003ff9801 0x3e7ff98001ffcc00

def z918 : W := mkw 0x00b27f9120000000 0x00593fc890000000 0xba783ff1f0000000 0xdd3c1ff8f8000000

def z919 : W := mkw 0x805c809402c80280 0x402e404a01640140 0x7cffc01e03fc07c1 0xbe7fe00f01fe03e0

def z920 : W := mkw 0x400800204382c631 0x2004001021c16318 0x8b0000000383e639 0xc580000001c1f31c

def z921 : W := mkw 0x02e7ff4e9c000000 0x0173ffa74e000000 0xfaffffefcc000000 0xfd7ffff7e6000000

def z922 : W := mkw 0x805580fc01580781 0xc02ac07e00ac03c0 0x7cffc0fe007c07c0 0xbe7fe07f003e03e0

def z923 : W := mkw 0x600b1268cbb3d735 0xb005893465d9eb9a 0x458703080ff3ff3f 0x22c3818407f9ff9f

def z924 : W := mkw 0x006ced0002ce6800 0x0036768001673400 0xfdffff0003fff801 0x7effff8001fffc00

def z925 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0xfdffc3fe03fc1fc1 0xfeffe1ff01fe0fe0

def z926 : W := mkw 0x02f7badfbc000000 0x017bdd6fde000000 0xdaff33fffc000000 0xed7f99fffe000000

def z927 : W := mkw 0x12f7ffdfbc00004a 0x097bffefde000025 0xfafffffffc00003e 0xfd7ffffffe00001f

def z928 : W := mkw 0xe21100fffd1087a5 0xf108807ffe8843d2 0x020000fffc0007e6 0x8100007ffe0003f3

def z929 : W := mkw 0x02f7badfbc000000 0x017bdd6fde000000 0xbaff3cfffc000000 0xdd7f9e7ffe000000

def z930 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xfdffff1e03fff801 0xfeffff8f01fffc00

def z931 : W := mkw 0x0030289120000000 0x0018144890000000 0x92783ce1f0000000 0x493c1e70f8000000

def z932 : W := mkw 0x82f7ffdfbc580180 0xc17bffefde2c00c0 0xfafffffffc700000 0xfd7ffffffe380000

def z933 : W := mkw 0x0255c5dfbc000000 0x012ae2efde000000 0xfaffcffffc000000 0xfd7fe7fffe000000

def z934 : W := mkw 0x4108452043effe31 0x2084229021f7ff18 0xef00cf1033fffe39 0xf780678819ffff1c

def z935 : W := mkw 0x601100fcc9108525 0xb008807e64884292 0x020000ffcc000526 0x8100007fe6000293

def z936 : W := mkw 0xf008452257fdbfef 0xf80422912bfedff7 0xef00cf1e3fffffff 0xf780678f1fffffff

def z937 : W := mkw 0x6108002043fbd525 0xb084001021fdea92 0x0500000003739d27 0x0280000001b9ce93

def z938 : W := mkw 0x01eeff0002eb5000 0x00f77f800175a800 0x90ff3f0003738000 0x487f9f8001b9c000

def z939 : W := mkw 0x0030289120000000 0x0018144890000000 0xbb783cf1f0006038 0xddbc1e78f800301c

def z940 : W := mkw 0xe01100fde91087b5 0xf008807ef48843da 0x020000fffc0007fe 0x8100007ffe0003ff

def z941 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfafffffffc8c67fe 0xfd7ffffffe4633ff

def z942 : W := mkw 0x6008002043f99525 0xb004001021fcca92 0x0500000003ff9d27 0x0280000001ffce93

def z943 : W := mkw 0x8075a8dd20580180 0xc03ad46e902c00c0 0xfefffcfff07c01c0 0xff7ffe7ff83e00e0

def z944 : W := mkw 0x02b23a91a8000000 0x01591d48d4000000 0xba783cf1f0000000 0xdd3c1e78f8000000

def z945 : W := mkw 0x804c800402c80080 0x4026400201640040 0x7cffc00603fc00c1 0x3e7fe00301fe0060

def z946 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x93783ce1f383e639 0x49bc1e70f9c1f31c

def z947 : W := mkw 0x13a27f03bc27784a 0x09d13f81de13bc25 0x83003f01fc03f83e 0x41801f80fe01fc1f

def z948 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfbfffffffc806001 0xfdfffffffe403000

def z949 : W := mkw 0xe008002043f997a5 0xf004001021fccbd2 0xef00c31e0fff9fe7 0xf780618f07ffcff3

def z950 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xbb783cf1f303e038 0xddbc1e78f981f01c

def z951 : W := mkw 0x400800204382c631 0x2004001021c16318 0x030000103383e639 0x8180000819c1f31c

def z952 : W := mkw 0x02f7badfbc000000 0x017bdd6fde000000 0x7afff0fffc000000 0xbd7ff87ffe000000

def z953 : W := mkw 0xc05d80fd63d887b1 0xe02ec07eb1ec43d8 0xffffccfff3fc67f9 0xffffe67ff9fe33fc

def z954 : W := mkw 0x01b27f9120277800 0x00d93fc89013bc00 0xbb783ff1f003f800 0xddbc1ff8f801fc00

def z955 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x10ff30ffc0000000 0x887f987fe0000000

def z956 : W := mkw 0x6108452043fffd25 0xb084229021fffe92 0xef00cf080ffffd27 0xf780678407fffe93

def z957 : W := mkw 0x106ced0216ce684a 0x083676810b673425 0xffffff1e3fffffff 0xffffff8f1fffffff

def z958 : W := mkw 0x13f7ffdfbc6d384a 0x09fbffefde369c25 0xfefffffffc7c19c6 0xff7ffffffe3e0ce3

def z959 : W := mkw 0x804d806c03d80581 0xc026c03601ec02c0 0x7cffc0ee03fc05c1 0xbe7fe07701fe02e0

def z960 : W := mkw 0x002a3a0002a35000 0x00151d000151a800 0xddff330003739801 0x6eff998001b9cc00

def z961 : W := mkw 0x4108002043ebd631 0x2084001021f5eb18 0x0100000003f3e639 0x0080000001f9f31c

def z962 : W := mkw 0x02f7ffdda8000000 0x017bffeed4000000 0xfafffff1f0000000 0xfd7ffff8f8000000

def z963 : W := mkw 0x01aa7f0002a77800 0x00d53f800153bc00 0xfdff3f0003f3f801 0x7eff9f8001f9fc00

def z964 : W := mkw 0x03eeff0616ef7800 0x01f77f830b77bc00 0xfdffff0603fff801 0x7effff8301fffc00

def z965 : W := mkw 0x81eeff0002ef7a80 0x40f77f800177bd40 0xfdffff0003fffac1 0x7effff8001fffd60

def z966 : W := mkw 0x12f7badfbc00004a 0x097bdd6fde000025 0x12ff30fffc0007fe 0x897f987ffe0003ff

def z967 : W := mkw 0x01ced70002ef7800 0x00e76b800177bc00 0x7dffc30003fff801 0x3effe18001fffc00

def z968 : W := mkw 0x104ed70216ed384a 0x08276b810b769c25 0xffffff1e3fffffff 0xffffff8f1fffffff

def z969 : W := mkw 0xc065a84d605ac1b0 0xe032d426b02d60d8 0xc787fc0ff07fe1f8 0x63c3fe07f83ff0fc

def z970 : W := mkw 0x603828b16392c735 0xb01c1458b1c9639a 0xbb783cf1f383e73f 0xddbc1e78f9c1f39f

def z971 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xdf8733f9ff739f3f 0xefc399fcffb9cf9f

def z972 : W := mkw 0x00e6ba0000211000 0x00735d0000108800 0xddff330003739801 0x6eff998001b9cc00

def z973 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfafffffffc806218 0xfd7ffffffe40310c

def z974 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xfdffff080ffff907 0x7effff8407fffc83

def z975 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfafffffffc006018 0xfd7ffffffe00300c

def z976 : W := mkw 0x01eeba0002ef7800 0x00f75d000177bc00 0x10ff300003ffe000 0x087f980001fff000

def z977 : W := mkw 0x400800204382c631 0x2004001021c16318 0x05000000038fe7f9 0x0280000001c7f3fc

def z978 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x12ff30e9cc000000 0x897f9874e6000000

def z979 : W := mkw 0x02b27f93bc000000 0x01593fc9de000000 0xfa78fffffc000000 0xfd3c7ffffe000000

def z980 : W := mkw 0x005d80dc02c80000 0x002ec06e01640000 0x7cffc0fe03fc07c1 0xbe7fe07f01fe03e0

def z981 : W := mkw 0x401800b16382c631 0x200c0058b1c16318 0x010000103383e639 0x0080000819c1f31c

def z982 : W := mkw 0xc008002043dac7b1 0xe004001021ed63d8 0xef00cc1e33ffe7f9 0xf780660f19fff3fc

def z983 : W := mkw 0x805d80fc03da4781 0xc02ec07e01ed23c0 0x7dffc0fe03ffe7c1 0xbeffe07f01fff3e0

def z984 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xb9fffc0003ffe001 0x5cfffe0001fff000

def z985 : W := mkw 0x4108002043effc21 0x2084001021f7fe10 0x0500000003fffc21 0x0280000001fffe10

def z986 : W := mkw 0x0030289120000000 0x0018144890000000 0xfa78fcfff0000000 0xfd3c7e7ff8000000

def z987 : W := mkw 0x006eba0002eb5000 0x00375d000175a800 0xfdffff0003fff801 0x7effff8001fffc00

def z988 : W := mkw 0x13eeff03beef784a 0x09f77f81df77bc25 0xffffff1fffffffff 0xffffff8fffffffff

def z989 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xfdffff0003fffd27 0x7effff8001fffe93

def z990 : W := mkw 0x0000000000000000 0x0000000000000000 0xef00cf1e3c8c7fff 0xf780678f1e463fff

def z991 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x54ffc0fe037c07c0 0xaa7fe07f01be03e0

def z992 : W := mkw 0x005c80b003c80601 0x002e405801e40300 0x7cffc0fe03fc07c1 0xbe7fe07f01fe03e0

def z993 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xf8ffffefcc000000 0x7c7ffff7e6000000

def z994 : W := mkw 0xe008002043d887a5 0xf004001021ec43d2 0x0400000003fc07e7 0x0200000001fe03f3

def z995 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xfdffff1003fffe01 0xfeffff8801ffff00

def z996 : W := mkw 0x016ca80002ef7800 0x00b654000177bc00 0xfdfffc0003fff801 0x7efffe0001fffc00

def z997 : W := mkw 0x03f7ffdfbc6d3800 0x01fbffefde369c00 0xffffffffff7f9801 0xffffffffffbfcc00

def z998 : W := mkw 0x400800204382c631 0x2004001021c16318 0x000000000383e218 0x0000000001c1f10c

def z999 : W := mkw 0xc05d80fd63dac7b1 0xe02ec07eb1ed63d8 0x7fffc0fff3ffe7f9 0xbfffe07ff9fff3fc

def z1000 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xd5ffff00037ff800 0x6affff8001bffc00

def z1001 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x31783cf1f383e639 0x18bc1e78f9c1f31c

def z1002 : W := mkw 0xc05d80fc43dac7b1 0xe02ec07e21ed63d8 0xffffccfe33ffe7f9 0xffffe67f19fff3fc

def z1003 : W := mkw 0x72a27f03fc25b86e 0x39513f81fe12dc37 0x83003f01fc03f83e 0x41801f80fe01fc1f

def z1004 : W := mkw 0x32f7ffdfbc35394e 0x997bffefde1a9ca7 0xfefffffffc7c19c6 0xff7ffffffe3e0ce3

def z1005 : W := mkw 0x6008002043b19725 0xb004001021d8cb92 0x0500000003f39f27 0x0280000001f9cf93

def z1006 : W := mkw 0xc05d80fc43dac7b1 0xe02ec07e21ed63d8 0x7cffc0fe03ff87c1 0xbe7fe07f01ffc3e0

def z1007 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xff873fe9cff3fd27 0xffc39ff4e7f9fe93

def z1008 : W := mkw 0x02f7ffdfbc211000 0x017bffefde108800 0xfbfffffffc039800 0xfdfffffffe01cc00

def z1009 : W := mkw 0x02f5eddfbc000000 0x017af6efde000000 0x2078ccf7f0000000 0x103c667bf8000000

def z1010 : W := mkw 0x82f7ffdfbc480080 0x417bffefde240040 0xfafffffffc0c00c0 0xfd7ffffffe060060

def z1011 : W := mkw 0xc05d80fd63d887b1 0xe02ec07eb1ec43d8 0x7cffc0ffc3fc07c1 0xbe7fe07fe1fe03e0

def z1012 : W := mkw 0x721100fffd10856f 0xb908807ffe8842b7 0x020000fffc0007fe 0x8100007ffe0003ff

def z1013 : W := mkw 0xe008002043f997a5 0xf004001021fccbd2 0x0500000003739d27 0x0280000001b9ce93

def z1014 : W := mkw 0xa05d80fc8bd80785 0xd02ec07e45ec03c2 0x7cffc0fe0ffc07c7 0xbe7fe07f07fe03e3

def z1015 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xbaff3ff1fc000000 0xdd7f9ff8fe000000

def z1016 : W := mkw 0x721145fffd14ad6f 0xb908a2fffe8a56b7 0xef00cffffc8c7fff 0xf78067fffe463fff

def z1017 : W := mkw 0x004e920002e91000 0x0027490001748800 0x10ff300003738000 0x087f980001b9c000

def z1018 : W := mkw 0x400800204382c631 0x2004001021c16318 0x010000000383e001 0x0080000001c1f000

def z1019 : W := mkw 0x400800204382c421 0x2004001021c16210 0x010000000383e421 0x0080000001c1f210

def z1020 : W := mkw 0x701100fbfd10877f 0xb808807dfe8843bf 0x020000fffc0007fe 0x8100007ffe0003ff

def z1021 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xb2fffff7fc000000 0x597ffffbfe000000

def z1022 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xffffff163ffffaff 0x7fffff8b1ffffd7f

def z1023 : W := mkw 0x123128dfbc00004a 0x0918946fde000025 0xbb783cfffc8067ff 0xddbc1e7ffe4033ff

def z1024 : W := mkw 0x805580dc00580180 0xc02ac06e002c00c0 0x54ffc0ee007c01c0 0x2a7fe077003e00e0

def z1025 : W := mkw 0xe05e9294cae992a4 0x702f494a6574c952 0xa378f317cc8f9ae6 0x51bc798be647cd73

def z1026 : W := mkw 0x005792dc88000000 0x002bc96e44000000 0x78fff0ffc0000000 0xbc7ff87fe0000000

def z1027 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0x10ff330003739800 0x087f998001b9cc00

def z1028 : W := mkw 0x12b27f93bc04284a 0x09593fc9de021425 0xbb783ff1fc807e3f 0xddbc1ff8fe403f1f

def z1029 : W := mkw 0xd01100ff751087fb 0xe808807fba8843fd 0x020000fffc0007fe 0x8100007ffe0003ff

def z1030 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xdf8733e9cfff9fe7 0xefc399f4e7ffcff3

def z1031 : W := mkw 0x51a27f037427f87a 0x28d13f81ba13fc3d 0x83003f01fc03f83e 0x41801f80fe01fc1f

def z1032 : W := mkw 0x004d806803d80501 0x8026c03401ec0280 0x7cffc0fe03fc07c1 0xbe7fe07f01fe03e0

def z1033 : W := mkw 0x5108002043effe7b 0x2884001021f7ff3d 0x0500000003ffffff 0x0280000001ffffff

def z1034 : W := mkw 0x02316ddfbc000000 0x0118b6efde000000 0xfa78fffffc000000 0xfd3c7ffffe000000

def z1035 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xf8ffff0003ffe000 0x7c7fff8001fff000

def z1036 : W := mkw 0x621100fde9108525 0xb108807ef4884292 0x000000e1c0000000 0x00000070e0000000

def z1037 : W := mkw 0x02333adfbc000000 0x01199d6fde000000 0xfaff3ffffc000000 0xfd7f9ffffe000000

def z1038 : W := mkw 0x12f7ffdfbc00004a 0x097bffefde000025 0xfafffffffc0002d8 0xfd7ffffffe00016c

def z1039 : W := mkw 0x0230289734000000 0x0118144b9a000000 0xba783cf7f0000000 0xdd3c1e7bf8000000

def z1040 : W := mkw 0xc05d80fc43d887a1 0xe02ec07e21ec43d0 0x7effc0ffc3fc07e1 0xbf7fe07fe1fe03f0

def z1041 : W := mkw 0x400800204382c631 0x2004001021c16318 0x0000000003838601 0x0000000001c1c300

def z1042 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x30ff3cf1f0000000 0x187f9e78f8000000

def z1043 : W := mkw 0x0030289120000000 0x0018144890000000 0xbb783cf1f0806001 0xddbc1e78f8403000

def z1044 : W := mkw 0xc008002043dac7b1 0xe004001021ed63d8 0x0000000003738000 0x0000000001b9c000

def z1045 : W := mkw 0xc01100fd611087b1 0xe008807eb08843d8 0x000000ffc00007c0 0x8000007fe00003e0

def z1046 : W := mkw 0x01eeff0216ef7800 0x00f77f810b77bc00 0xffffff003ffff801 0x7fffff801ffffc00

def z1047 : W := mkw 0x6108002043fffd25 0xb084001021fffe92 0x0500000003fff801 0x0280000001fffc00

def z1048 : W := mkw 0x00323a9120000000 0x00191d4890000000 0xfaff3ff1f0000000 0xfd7f9ff8f8000000

def z1049 : W := mkw 0x400845225782c631 0x200422912bc16318 0xeb00cf1e3f83e639 0xf580678f1fc1f31c

def z1050 : W := mkw 0x01eeff0122ef7810 0x00f77f809177bc08 0xfdffff0033fff819 0x7effff8019fffc0c

def z1051 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x9b8733e1cf739c27 0xcdc399f0e7b9ce13

def z1052 : W := mkw 0x12f7ffdfbc25384a 0x097bffefde129c25 0xffffffffffffffff 0xffffffffffffffff

def z1053 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xfdffff0803fffd01 0xfeffff8401fffe80

def z1054 : W := mkw 0x02f7ffdfbc211000 0x017bffefde108800 0xffffffffff739d27 0xffffffffffb9ce93

def z1055 : W := mkw 0x00f4ed9120000000 0x007a76c890000000 0xba78fcf1f0000000 0xdd3c7e78f8000000

def z1056 : W := mkw 0x13eeff03beef784a 0x09f77f81df77bc25 0xffffff01fffff83f 0x7fffff80fffffc1f

def z1057 : W := mkw 0x0010009120000000 0x0008004890000000 0x3a7800f1f0000000 0x9d3c0078f8000000

def z1058 : W := mkw 0x805c809402c80280 0x402e404a01640140 0x30ffc01603fc02c0 0x187fe00b01fe0160

def z1059 : W := mkw 0x805d80dc02d80380 0xc02ec06e016c01c0 0x7cffc0fe00fc03c0 0xbe7fe07f007e01e0

def z1060 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0xb8ff3ce1c0000000 0x5c7f9e70e0000000

def z1061 : W := mkw 0x804d804c02d80180 0xc026c026016c00c0 0x64ffc00e00fc01c0 0x327fe007007e00e0

def z1062 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0x70fffffffc000000 0x387ffffffe000000

def z1063 : W := mkw 0x004c800002c80000 0x0026400001640000 0x7cffc00e03fc01c1 0x3e7fe00701fe00e0

def z1064 : W := mkw 0x400800204382c631 0x2004001021c16318 0x6d00c01e038fe7f9 0xb680600f01c7f3fc

def z1065 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xffffff0e3ffff9ff 0x7fffff871ffffcff

def z1066 : W := mkw 0x02f4ed9734000000 0x017a76cb9a000000 0x3078fcf7f0000000 0x183c7e7bf8000000

def z1067 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x7dffc0fe03fc67f9 0xbeffe07f01fe33fc

def z1068 : W := mkw 0x500845225786ee7b 0x280422912bc3773d 0x83000f003f83fe3f 0x418007801fc1ff1f

def z1069 : W := mkw 0xc01100fd611087b1 0xe008807eb08843d8 0x020000f1f0000638 0x81000078f800031c

def z1070 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x74ffc0fe03fc03c0 0x3a7fe07f01fe01e0

def z1071 : W := mkw 0x907ced9736ce6ada 0x483e76cb9b67356d 0x2078cc16308c62d8 0x103c660b1846316c

def z1072 : W := mkw 0xd008452257deeffb 0xe80422912bef77fd 0xef00cf1e3fffffff 0xf780678f1fffffff

def z1073 : W := mkw 0x13fced9736ce684a 0x09fe76cb9b673425 0x2078cc16308c62d8 0x103c660b1846316c

def z1074 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x78fff00003738000 0x3c7ff80001b9c000

def z1075 : W := mkw 0x22f7ffdfbc311104 0x917bffefde188882 0xfafffffffc700000 0xfd7ffffffe380000

def z1076 : W := mkw 0x02d7d7dfbc000000 0x016bebefde000000 0x7affc3fffc000000 0xbd7fe1fffe000000

def z1077 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0x10fff000037f8000 0x087ff80001bfc000

def z1078 : W := mkw 0x10e6ff021425384a 0x08737f810a129c25 0xffffff1e3fffffff 0xffffff8f1fffffff

def z1079 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xff783ff1f383fe39 0xffbc1ff8f9c1ff1c

def z1080 : W := mkw 0x01eeff008aef7800 0x00f77f804577bc00 0xffffff01cffff801 0x7fffff80e7fffc00

def z1081 : W := mkw 0x0030289120000000 0x0018144890000000 0xba783cf1f0806218 0xdd3c1e78f840310c

def z1082 : W := mkw 0x02f7ffdfbc042800 0x017bffefde021400 0xfbfffffffc007800 0xfdfffffffe003c00

def z1083 : W := mkw 0x32f7ffdfbc35394e 0x997bffefde1a9ca7 0xfffffffffcfc7fff 0xfffffffffe7e3fff

def z1084 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0x74ffff0003fff800 0x3a7fff8001fffc00

def z1085 : W := mkw 0x01ced70002ed3800 0x00e76b8001769c00 0xfdfff30003ff9801 0x7efff98001ffcc00

def z1086 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x78fff0e1c0000000 0x3c7ff870e0000000

def z1087 : W := mkw 0x00eeff0002a35000 0x00777f800151a800 0xfdffff0003f3f801 0x7effff8001f9fc00

def z1088 : W := mkw 0xe04f926ccbf997a5 0xf027c93665fccbd2 0x4587c30e0fff9fe7 0x22c3e18707ffcff3

def z1089 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfafffffffc800601 0xfd7ffffffe400300

def z1090 : W := mkw 0xc03828b163cac6b1 0x601c1458b1e56358 0xbb783cf1f38fe6f9 0xddbc1e78f9c7f37c

def z1091 : W := mkw 0x4108002043ceee31 0x2084001021e77718 0x01000000038fe639 0x0080000001c7f31c

def z1092 : W := mkw 0x02f7ffdfbc100100 0x817bffefde080080 0xfefffffffc700100 0xff7ffffffe380080

def z1093 : W := mkw 0x22f7ffdfbc100104 0x917bffefde080082 0xfafffffffc000106 0xfd7ffffffe000083

def z1094 : W := mkw 0x002a3a0002a35000 0x00151d000151a800 0xb9ff3c0003f3e001 0x5cff9e0001f9f000

def z1095 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0x10fff0e7c0000000 0x087ff873e0000000

def z1096 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xff78ffffff8fffff 0xffbc7fffffc7ffff

def z1097 : W := mkw 0x0075a8dd20000000 0x003ad46e90000000 0x78fff0ffc0000000 0xbc7ff87fe0000000

def z1098 : W := mkw 0x004c800002c80000 0x0026400001640000 0x7cffc01603fc02c1 0x3e7fe00b01fe0160

def z1099 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x32783cf1f383e638 0x993c1e78f9c1f31c

def z1100 : W := mkw 0xa05792dc88791184 0xd02bc96e443c88c2 0xfefff3ffcc7c19c6 0xff7ff9ffe63e0ce3

def z1101 : W := mkw 0x60e6ff2041319525 0xb0737f902098ca92 0xfdffff0003739d27 0x7effff8001b9ce93

def z1102 : W := mkw 0xc04d806c43dac7b1 0xe026c03621ed63d8 0x4587c00e03ffe7f9 0x22c3e00701fff3fc

def z1103 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x38783cf1f383e619 0x9c3c1e78f9c1f30c

def z1104 : W := mkw 0xc03828b56382c6b1 0x601c145ab1c16358 0xbb783cf7f383e6f9 0xddbc1e7bf9c1f37c

def z1105 : W := mkw 0x400800204382c631 0x2004001021c16318 0x050000000383ff3f 0x0280000001c1ff9f

def z1106 : W := mkw 0x600800204392c735 0xb004001021c9639a 0x010000000383e73f 0x0080000001c1f39f

def z1107 : W := mkw 0x02f5a8dfbc000000 0x017ad46fde000000 0x027800fffc000000 0x813c007ffe000000

def z1108 : W := mkw 0x005580dc00000000 0x002ac06e00000000 0xfafff0ffc0000000 0xfd7ff87fe0000000

def z1109 : W := mkw 0xe01100fcc91087a5 0xf008807e648843d2 0x000000e1c0000000 0x00000070e0000000

def z1110 : W := mkw 0x02e7ff4bbc000000 0x0173ffa5de000000 0xfaffffe9fc000000 0xfd7ffff4fe000000

def z1111 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfafffffffc8c02c0 0xfd7ffffffe460160

def z1112 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xff87ffffffffffff 0xffc3ffffffffffff

def z1113 : W := mkw 0x12f7ffdfbc00004a 0x097bffefde000025 0xfafffffffc0001c6 0xfd7ffffffe0000e3

def z1114 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xffffff0033fff839 0x7fffff8019fffc1c

def z1115 : W := mkw 0x02f7ffdfbc042800 0x017bffefde021400 0xfffffffffc8c7fc1 0xfffffffffe463fe0

def z1116 : W := mkw 0x004c800002ca4000 0x0026400001652000 0x7dffc00003ffe001 0x3effe00001fff000

def z1117 : W := mkw 0x7008452257b7ff7f 0xb80422912bdbffbf 0xef00cf1e3fffffff 0xf780678f1fffffff

def z1118 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0xbbff3cf1f0806639 0xddff9e78f840331c

def z1119 : W := mkw 0x023128dda8000000 0x0118946ed4000000 0x107830e1c0000000 0x083c1870e0000000

def z1120 : W := mkw 0x02f4a89520000000 0x017a544a90000000 0xba783cf1f0000000 0xdd3c1e78f8000000

def z1121 : W := mkw 0x804d804c02d80180 0xc026c026016c00c0 0x54ffc00e037c01c0 0x2a7fe00701be00e0

def z1122 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xa3783cf1f083e638 0xd1bc1e78f841f31c

def z1123 : W := mkw 0x102a7f0216a7784a 0x08153f810b53bc25 0xffffff1e3fffffff 0xffffff8f1fffffff

def z1124 : W := mkw 0x02f5eddf34000000 0x017af6ef9a000000 0xfafffcfff0000000 0xfd7ffe7ff8000000

def z1125 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xffffff1633fffef9 0xffffff8b19ffff7c

def z1126 : W := mkw 0x03f7badda8691000 0x01fbdd6ed4348800 0x10ff30e1c0700000 0x087f9870e0380000

def z1127 : W := mkw 0x00f6ff9120042800 0x007b7fc890021400 0xfffffff1f08c7e39 0xfffffff8f8463f1c

def z1128 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xffffff0e0ffffde7 0xffffff8707fffef3

def z1129 : W := mkw 0x0030289120000000 0x0018144890000000 0x127830f1f0000000 0x893c1878f8000000

def z1130 : W := mkw 0xf01145fedd14afef 0xf808a2ff6e8a57f7 0xef00cffffc8c7fff 0xf78067fffe463fff

def z1131 : W := mkw 0x03f7ffdfbc691000 0x01fbffefde348800 0xfafffffffc700000 0xfd7ffffffe380000

def z1132 : W := mkw 0xc01100fc411087b1 0xe008807e208843d8 0x000000fe000007f8 0x8000007f000003fc

def z1133 : W := mkw 0x22f7ffdfbc211004 0x117bffefde108802 0xfafffffffc001806 0xfd7ffffffe000c03

def z1134 : W := mkw 0x004e920002e91000 0x0027490001748800 0xfffff31e0fff9fe7 0xfffff98f07ffcff3

def z1135 : W := mkw 0x03eeff01aaef7800 0x01f77f80d577bc00 0xfdffff01c3fff801 0x7effff80e1fffc00

def z1136 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0x55fff30003fff801 0x2afff98001fffc00

def z1137 : W := mkw 0x6008002043b3d735 0xb004001021d9eb9a 0x0000000003738000 0x0000000001b9c000

def z1138 : W := mkw 0x03eeff0336ef7800 0x01f77f819b77bc00 0xfdffff0033fff801 0x7effff8019fffc00

def z1139 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x5cffc0ee037c05c1 0xae7fe07701be02e0

def z1140 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x99ff300003738001 0x4cff980001b9c000

def z1141 : W := mkw 0xe01100fcc91087a5 0xf008807e648843d2 0xef00c3ffcc8c1fe7 0xf78061ffe6460ff3

def z1142 : W := mkw 0x03f7ffdfbc253800 0x01fbffefde129c00 0xfafffffffc001800 0xfd7ffffffe000c00

def z1143 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xff87f3ffcf739d27 0xffc3f9ffe7b9ce93

def z1144 : W := mkw 0x02f4ed9734000000 0x017a76cb9a000000 0xfa78fffffc000000 0xfd3c7ffffe000000

def z1145 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0xfdff3f0003f3f801 0x7eff9f8001f9fc00

def z1146 : W := mkw 0x02f7badda8211000 0x017bdd6ed4108800 0x10ff30e1c3738000 0x087f9870e1b9c000

def z1147 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x38ffc0f603fc06c1 0x9c7fe07b01fe0360

def z1148 : W := mkw 0x0030289120000000 0x0018144890000000 0xfa783ff9fc000000 0xfd3c1ffcfe000000

def z1149 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xbb783cf9ff83e73f 0xddbc1e7cffc1f39f

def z1150 : W := mkw 0x02f5eddfbc000000 0x017af6efde000000 0x7affccfffc000000 0xbd7fe67ffe000000

def z1151 : W := mkw 0x400800204386ee31 0x2004001021c37718 0x05000000038ffe39 0x0280000001c7ff1c

def z1152 : W := mkw 0x02f7ffdfbc211000 0x017bffefde108800 0xfaffffffff738000 0xfd7fffffffb9c000

def z1153 : W := mkw 0x02f7ffdfbc042800 0x017bffefde021400 0xfffffffffc8c7e39 0xfffffffffe463f1c

def z1154 : W := mkw 0x03f7badda8235000 0x01fbdd6ed411a800 0x10ff30e1c0038000 0x087f9870e001c000

def z1155 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xde8733e9cf739906 0xef4399f4e7b9cc83

def z1156 : W := mkw 0x03eeba01aaeb5000 0x01f75d00d575a800 0x10ff3001c3738000 0x087f9800e1b9c000

def z1157 : W := mkw 0x12f7ffdfbc00004a 0x097bffefde000025 0xfefffffffc8c07ff 0xff7ffffffe4603ff

def z1158 : W := mkw 0x500845225786ee7b 0x280422912bc3773d 0x2100cc16338fe6f9 0x1080660b19c7f37c

def z1159 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0x32fffcfffc000000 0x997ffe7ffe000000

def z1160 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0xdfff33080f739d27 0xefff998407b9ce93

def z1161 : W := mkw 0x03f7ffdfbc235000 0x01fbffefde11a800 0xfafffffffc038000 0xfd7ffffffe01c000

def z1162 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfefffffffc0c1ffe 0xff7ffffffe060fff

def z1163 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0xd8ff33e1c0000000 0x6c7f99f0e0000000

def z1164 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x938733e9cf739d26 0xc9c399f4e7b9ce93

def z1165 : W := mkw 0x403028b16102c631 0x20181458b0816318 0xbb783cf1f003e638 0xddbc1e78f801f31c

def z1166 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0xbbff3c1033f3e639 0xddff9e0819f9f31c

def z1167 : W := mkw 0xc108002043ffffb1 0xe084001021ffffd8 0x0500000003fffff9 0x0280000001fffffc

def z1168 : W := mkw 0x11a27f021427784a 0x08d13f810a13bc25 0x81003f003003f818 0x40801f801801fc0c

def z1169 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xffffff103ffffe3f 0xffffff881fffff1f

def z1170 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfbfffffffc8c7afe 0xfdfffffffe463d7f

def z1171 : W := mkw 0x0074a89120000000 0x003a544890000000 0xfafffcf1f0000000 0xfd7ffe78f8000000

def z1172 : W := mkw 0x014cc50002ef7800 0x00a662800177bc00 0xfdffcf0003fff801 0x7effe78001fffc00

def z1173 : W := mkw 0x20333ad9a8311104 0x90199d6cd4188882 0xfeff3ff9fc701906 0xff7f9ffcfe380c83

def z1174 : W := mkw 0x003128d9a8000000 0x0018946cd4000000 0xba783cf9fc000000 0xdd3c1e7cfe000000

def z1175 : W := mkw 0x00306d9334000000 0x001836c99a000000 0xba78fcf7f0000000 0xdd3c7e7bf8000000

def z1176 : W := mkw 0x21eeff008aef7804 0x10f77f804577bc02 0xfdffff000ffff807 0x7effff8007fffc03

def z1177 : W := mkw 0x014c800002eb5000 0x00a640000175a800 0x10ff000003738000 0x087f800001b9c000

def z1178 : W := mkw 0x601100f9e9108735 0xb008807cf488439a 0xef000ff9fc807f3f 0xf78007fcfe403f9f

def z1179 : W := mkw 0x403028b161008421 0x20181458b0804210 0xbb783cf1f383e639 0xddbc1e78f9c1f31c

def z1180 : W := mkw 0x0030289120000000 0x0018144890000000 0x9a7830e1c0000000 0xcd3c1870e0000000

def z1181 : W := mkw 0x81eeff0402ef7880 0x40f77f820177bc40 0xfdffff0603fff8c1 0x7effff8301fffc60

def z1182 : W := mkw 0x6008002043b3d525 0xb004001021d9ea92 0x0500000003f3fd27 0x0280000001f9fe93

def z1183 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xdafff3efcc000000 0xed7ff9f7e6000000

def z1184 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfffffffffc0c1de7 0xfffffffffe060ef3

def z1185 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0xb8ff3c0003738000 0x5c7f9e0001b9c000

def z1186 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x10783ce1f303e018 0x083c1e70f981f00c

def z1187 : W := mkw 0x31c7d74a9c7d394e 0x98e3eba54e3e9ca7 0x4487c30e0c7c19c6 0x2243e187063e0ce3

def z1188 : W := mkw 0x0030289120000000 0x0018144890000000 0x30783cf1f0000000 0x183c1e78f8000000

def z1189 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xffffff000ffff827 0x7fffff8007fffc13

def z1190 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x9b783ce1f303e439 0xcdbc1e70f981f21c

def z1191 : W := mkw 0x02f7ffdda8042800 0x017bffeed4021400 0xfdffffe1c08c7801 0x7efffff0e0463c00

def z1192 : W := mkw 0x003128dd20000000 0x0018946e90000000 0xba783cfff0000000 0xdd3c1e7ff8000000

def z1193 : W := mkw 0x13c7d74e9c6d384a 0x09e3eba74e369c25 0x4487c30e0c7c19c6 0x2243e187063e0ce3

def z1194 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xfdffff1e3ffffbdf 0x7effff8f1ffffdef

def z1195 : W := mkw 0x21e7ff48887d3904 0x90f3ffa4443e9c82 0xfeffffe9cc7c1906 0xff7ffff4e63e0c83

def z1196 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xff873ff9ff739d27 0xffc39ffcffb9ce93

def z1197 : W := mkw 0xe07fbafdebfbd7b5 0xf03fdd7ef5fdebda 0x10ff30e1c3738000 0x087f9870e1b9c000

def z1198 : W := mkw 0x1255c5dfbc04284a 0x092ae2efde021425 0xffffcffffc8c7fff 0xffffe7fffe463fff

def z1199 : W := mkw 0x005580fc01100501 0x802ac07e00880280 0x7cffc0fe03fc07c1 0xbe7fe07f01fe03e0

def z1200 : W := mkw 0x4002122041219421 0x200109102090ca10 0xdf8733e9cf739d27 0xefc399f4e7b9ce93

def z1201 : W := mkw 0x621100fffd108525 0xb108807ffe884292 0x020000fffc000000 0x8100007ffe000000

def z1202 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x15ff300003739801 0x0aff980001b9cc00

def z1203 : W := mkw 0x002a3a0002a35000 0x00151d000151a800 0x10ff300003738000 0x087f980001b9c000

def z1204 : W := mkw 0x82f7ffdfbc100180 0xc17bffefde0800c0 0xfafffffffc0001c0 0xfd7ffffffe0000e0

def z1205 : W := mkw 0x601100f9e9108735 0xb008807cf488439a 0x020000e9cc000526 0x81000074e6000293

def z1206 : W := mkw 0x00306d9120000000 0x001836c890000000 0xfa78fff1f0000000 0xfd3c7ff8f8000000

def z1207 : W := mkw 0x02f5eddfbc000000 0x017af6efde000000 0xba78fcfffc000000 0xdd3c7e7ffe000000

def z1208 : W := mkw 0x22f7badda8311104 0x917bdd6ed4188882 0x54ff33e9cc701906 0x2a7f99f4e6380c83

def z1209 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xdb8733e9cf739826 0xedc399f4e7b9cc13

def z1210 : W := mkw 0x22f7ffdfbc311104 0x917bffefde188882 0xffffffffff739907 0xffffffffffb9cc83

def z1211 : W := mkw 0x000a120002a11000 0x0005090001508800 0xfdff330003f39801 0x7eff998001f9cc00

def z1212 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x558733e9cf739d27 0x2ac399f4e7b9ce93

def z1213 : W := mkw 0x00e6ba0000211000 0x00735d0000108800 0x10ff300003738000 0x087f980001b9c000

def z1214 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x7cfff0ffc08c07c1 0xbe7ff87fe04603e0

def z1215 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0xfdfffc0003ffe001 0x7efffe0001fff000

def z1216 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfbfffffffc006038 0xfdfffffffe00301c

def z1217 : W := mkw 0x023128dfbc000000 0x0118946fde000000 0x22780cfffc000000 0x913c067ffe000000

def z1218 : W := mkw 0x805c80b403c80681 0x402e405a01e40340 0x7cffc0f603fc06c1 0xbe7fe07b01fe0360

def z1219 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfeffffffff700001 0xff7fffffffb80000

def z1220 : W := mkw 0xe008002043f997a5 0xf004001021fccbd2 0x0400000003ff87c1 0x0200000001ffc3e0

def z1221 : W := mkw 0x403828b16392c731 0xa01c1458b1c96398 0xbf783cf1f3f3e739 0xdfbc1e78f9f9f39c

def z1222 : W := mkw 0x025580dfbc000000 0x012ac06fde000000 0x12ff00fffc000000 0x897f807ffe000000

def z1223 : W := mkw 0x403828b163cac631 0x201c1458b1e56318 0xbf783cf1f3ffe639 0xdfbc1e78f9fff31c

def z1224 : W := mkw 0x03f7ffdfbc6d3800 0x01fbffefde369c00 0xfffffffffcfc7801 0xfffffffffe7e3c00

def z1225 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0xfaff3ff9fc000000 0xfd7f9ffcfe000000

def z1226 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xffffff083ffffd3f 0xffffff841ffffe9f

def z1227 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfefffffffc8c0001 0xff7ffffffe460000

def z1228 : W := mkw 0x0030289120000000 0x0018144890000000 0xb8783ce1c0000000 0x5c3c1e70e0000000

def z1229 : W := mkw 0x805c80b403d80781 0xc02e405a01ec03c0 0x7cffc01603fc07c1 0x3e7fe00b01fe03e0

def z1230 : W := mkw 0xe008002043fbd7b5 0xf004001021fdebda 0x0500000003ffffff 0x0280000001ffffff

def z1231 : W := mkw 0x03f7ffdfbc277800 0x01fbffefde13bc00 0xffffffffff73f801 0xffffffffffb9fc00

def z1232 : W := mkw 0x005792dc88000000 0x002bc96e44000000 0x10ff30e1c0000000 0x087f9870e0000000

def z1233 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xffffffe1c3fff801 0xfffffff0e1fffc00

def z1234 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xffff3cf1f3f3e639 0xffff9e78f9f9f31c

def z1235 : W := mkw 0x0075a8dd20000000 0x003ad46e90000000 0xfffffcfff08c67f9 0xfffffe7ff84633fc

def z1236 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x38ff300003f38001 0x1c7f980001f9c000

def z1237 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x12ff30f1f0000000 0x897f9878f8000000

def z1238 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfffffffffc0c79fe 0xfffffffffe063cff

def z1239 : W := mkw 0x02f5a8dda8000000 0x017ad46ed4000000 0x007800e1c0000000 0x003c0070e0000000

def z1240 : W := mkw 0x02f7ffdfbc253800 0x017bffefde129c00 0xfffffffffffff801 0xfffffffffffffc00

def z1241 : W := mkw 0x0030289120000000 0x0018144890000000 0xfe78fcfff08c07c1 0xff3c7e7ff84603e0

def z1242 : W := mkw 0x006ca80002ca4000 0x0036540001652000 0xb9ff3c0003f3e001 0x5cff9e0001f9f000

def z1243 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0x92ff3ffffc000000 0xc97f9ffffe000000

def z1244 : W := mkw 0x114cc50216ef784a 0x08a662810b77bc25 0xffffcf1e3fffffff 0xffffe78f1fffffff

def z1245 : W := mkw 0x82f7ffdfbc580180 0xc17bffefde2c00c0 0xfefffffffcfc07c1 0xff7ffffffe7e03e0

def z1246 : W := mkw 0x03f7ffdfbc277800 0x01fbffefde13bc00 0xfffffffffc8ff801 0xfffffffffe47fc00

def z1247 : W := mkw 0x03eeff03beef7800 0x01f77f81df77bc00 0xffffff1ffffff801 0xffffff8ffffffc00

def z1248 : W := mkw 0x02f6ff93bc000000 0x017b7fc9de000000 0xfafffff1fc000000 0xfd7ffff8fe000000

def z1249 : W := mkw 0x02f7ffdfbc042800 0x017bffefde021400 0xfffffffffc8c7d27 0xfffffffffe463e93

def z1250 : W := mkw 0xe01100fcc91087a5 0xf008807e648843d2 0x000000ffc00007c0 0x8000007fe00003e0

def z1251 : W := mkw 0x402828216382c431 0x20141410b1c16218 0xbb783ce1f383e439 0xddbc1e70f9c1f21c

def z1252 : W := mkw 0x0077badda8000000 0x003bdd6ed4000000 0xfafffffffc000000 0xfd7ffffffe000000

def z1253 : W := mkw 0x805d80dc02d80380 0xc02ec06e016c01c0 0x44ffc00e007c01c0 0x227fe007003e00e0

def z1254 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xf8fffff7f0000000 0x7c7ffffbf8000000

def z1255 : W := mkw 0x00eeff0002ca4000 0x00777f8001652000 0xfdffff0003ffe001 0x7effff8001fff000

def z1256 : W := mkw 0x01eeff0216ef7800 0x00f77f810b77bc00 0xffffff1e3ffffd27 0xffffff8f1ffffe93

def z1257 : W := mkw 0x805d80fd23d80781 0xc02ec07e91ec03c0 0x7effc0fff3fc07c1 0xbf7fe07ff9fe03e0

def z1258 : W := mkw 0x4008002043cac631 0x2004001021e56318 0x0500000003ffe639 0x0280000001fff31c

def z1259 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xffffff080ffff801 0xffffff8407fffc00

def z1260 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0x95ff3f0003fff801 0x4aff9f8001fffc00

def z1261 : W := mkw 0x01eeff0002eb5000 0x00f77f800175a800 0xfdffff0003739801 0x7effff8001b9cc00

def z1262 : W := mkw 0x805d80dc02d80380 0xc02ec06e016c01c0 0x20ffc01600fc02c0 0x107fe00b007e0160

def z1263 : W := mkw 0x60031268c9319735 0xb00189346498cb9a 0xdf8733e9cf739f3f 0xefc399f4e7b9cf9f

def z1264 : W := mkw 0x00e7ba4888000000 0x0073dd2444000000 0x10ff30e1c0000000 0x087f9870e0000000

def z1265 : W := mkw 0x4008002043808631 0x2004001021c04318 0x0000000003800639 0x0000000001c0031c

def z1266 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xfdffff1603fffac1 0x7effff8b01fffd60

def z1267 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xffffff183fffff3f 0xffffff8c1fffff9f

def z1268 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0x52fff3fffc000000 0xa97ff9fffe000000

def z1269 : W := mkw 0x006ca80002ca4000 0x0036540001652000 0xfffffc1e33ffe7f9 0xfffffe0f19fff3fc

def z1270 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0xfeffccfe33fc07c1 0xff7fe67f19fe03e0

def z1271 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x9aff30e1c0000000 0xcd7f9870e0000000

def z1272 : W := mkw 0x0038289122824000 0x001c144891412000 0xbb783cf1f383e639 0xddbc1e78f9c1f31c

def z1273 : W := mkw 0x01eced0002ce6800 0x00f6768001673400 0xfdfffc0003ffe001 0x7efffe0001fff000

def z1274 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xfdffff1e0fffffc7 0xfeffff8f07ffffe3

def z1275 : W := mkw 0x00333ad9a8000000 0x00199d6cd4000000 0x10ff30e1c0000000 0x087f9870e0000000

def z1276 : W := mkw 0x00e6ff0000211000 0x00737f8000108800 0xf8ffff0003738000 0x7c7fff8001b9c000

def z1277 : W := mkw 0x001312d888000000 0x0009896c44000000 0xfaff33f9cc000000 0xfd7f99fce6000000

def z1278 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfaffffe1fc000000 0x7d7ffff0fe000000

def z1279 : W := mkw 0x403028b16102c431 0x20181458b0816218 0xbb783cf1f303e439 0xddbc1e78f981f21c

def z1280 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xfdffff0003ffffc1 0x7effff8001ffffe0

def z1281 : W := mkw 0x00e7ff4888042800 0x0073ffa444021400 0xffffffe9cc8c7d27 0xfffffff4e6463e93

def z1282 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xffffff0003fffc21 0xffffff8001fffe10

def z1283 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xbf783cf1f38fe7f9 0xdfbc1e78f9c7f3fc

def z1284 : W := mkw 0xc03828b16392c7b1 0xe01c1458b1c963d8 0xbb783cf1f383e7f9 0xddbc1e78f9c1f3fc

def z1285 : W := mkw 0x400800204382c631 0x2004001021c16318 0xa9000c000383e639 0x5480060001c1f31c

def z1286 : W := mkw 0x00f7ffdd20000000 0x007bffee90000000 0xfafffffff0000000 0xfd7ffffff8000000

def z1287 : W := mkw 0xb047d74e9c7d39ce 0xd823eba74e3e9ce7 0x4487c30e0c7c19c6 0x2243e187063e0ce3

def z1288 : W := mkw 0x01eeba0002ef7800 0x00f75d000177bc00 0x7dfff00003fff801 0x3efff80001fffc00

def z1289 : W := mkw 0x004ed70002ed3800 0x00276b8001769c00 0xfdffff0003fff801 0x7effff8001fffc00

def z1290 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xfdffff0033fff819 0x7effff8019fffc0c

def z1291 : W := mkw 0x01eced0002ef7800 0x00f676800177bc00 0x7dffcc0003fff801 0x3effe60001fffc00

def z1292 : W := mkw 0x02b37fdbbc000000 0x0159bfedde000000 0xfaff3ff9fc000000 0xfd7f9ffcfe000000

def z1293 : W := mkw 0xe0031268c93197a5 0xf00189346498cbd2 0xdf8733e9cf739fe7 0xefc399f4e7b9cff3

def z1294 : W := mkw 0x02f7ffdda8000000 0x017bffeed4000000 0x30fffce1c0000000 0x187ffe70e0000000

def z1295 : W := mkw 0x00eeff0002e91000 0x00777f8001748800 0xfdffff0003ff9801 0x7effff8001ffcc00

def z1296 : W := mkw 0x00306d9334000000 0x001836c99a000000 0xba783ff1fc000000 0xdd3c1ff8fe000000

def z1297 : W := mkw 0x02b06d9334000000 0x015836c99a000000 0xba783cf1f0000000 0xdd3c1e78f8000000

def z1298 : W := mkw 0x00323a9120211000 0x00191d4890108800 0xffff3ff1f3739801 0xffff9ff8f9b9cc00

def z1299 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfefffffffc8c67d9 0xff7ffffffe4633ec

def z1300 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xfdffff0603fff8c1 0x7effff8301fffc60

def z1301 : W := mkw 0x02f6ff9734000000 0x017b7fcb9a000000 0xfafffff7f0000000 0xfd7ffffbf8000000

def z1302 : W := mkw 0x92f7ffdfbc5c29ca 0xc97bffefde2e14e5 0xfefffffffc7c19c6 0xff7ffffffe3e0ce3

def z1303 : W := mkw 0x22f7badda8311104 0x917bdd6ed4188882 0x10ff30e1c0700000 0x087f9870e0380000

def z1304 : W := mkw 0x12f7ffdfbc00004a 0x097bffefde000025 0xfbfffffffc8067ff 0xfdfffffffe4033ff

def z1305 : W := mkw 0x0020280000000000 0x0010140000000000 0xba783ce1c0000000 0xdd3c1e70e0000000

def z1306 : W := mkw 0x4108002043a7fe31 0x2084001021d3ff18 0x010000000383fe39 0x0080000001c1ff1c

def z1307 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0xd8ff330003738000 0x6c7f998001b9c000

def z1308 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x91ff3c000373e000 0x48ff9e0001b9f000

def z1309 : W := mkw 0x400800204382c631 0x2004001021c16318 0x21000c103383e639 0x1080060819c1f31c

def z1310 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfbfffffffc007ffe 0xfdfffffffe003fff

def z1311 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfafffffffc001806 0xfd7ffffffe000c03

def z1312 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0xffffcffe3ffc7fff 0xffffe7ff1ffe3fff

def z1313 : W := mkw 0x01eeff0216eb5000 0x00f77f810b75a800 0xfaffff1e3f738000 0xfd7fff8f1fb9c000

def z1314 : W := mkw 0x12316ddfbc04284a 0x0918b6efde021425 0xff78fffffc8c7fff 0xffbc7ffffe463fff

def z1315 : W := mkw 0x004c800002c80000 0x0026400001640000 0xfdfff00003ff8001 0x7efff80001ffc000

def z1316 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xbb783ce1f383e039 0x5dbc1e70f9c1f01c

def z1317 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xff8733f9cff39f27 0xffc399fce7f9cf93

def z1318 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xddff3f000373f801 0x6eff9f8001b9fc00

def z1319 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x58ff30e9c0000000 0xac7f9874e0000000

def z1320 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0x10ff3ce1f0000000 0x087f9e70f8000000

def z1321 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xfdffff1e33ffffd9 0xfeffff8f19ffffec

def z1322 : W := mkw 0x00e6ff0000253800 0x00737f8000129c00 0xfdffff0003fff801 0x7effff8001fffc00

def z1323 : W := mkw 0xe05d80fccbd887a5 0xf02ec07e65ec43d2 0x7cffc0ffc3fc07c1 0xbe7fe07fe1fe03e0

def z1324 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x50fff0efc0000000 0x287ff877e0000000

def z1325 : W := mkw 0x805c809402c80280 0x402e404a01640140 0x64ffc01600fc02c0 0x327fe00b007e0160

def z1326 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfffffffffc8c783f 0xfffffffffe463c1f

def z1327 : W := mkw 0x402828216382c631 0x20141410b1c16318 0x01000c003383e639 0x0080060019c1f31c

def z1328 : W := mkw 0x00e7ff4888000000 0x0073ffa444000000 0xf8ffffe1c0000000 0x7c7ffff0e0000000

def z1329 : W := mkw 0xc008002043dac7b1 0xe004001021ed63d8 0x0100000003f3e639 0x0080000001f9f31c

def z1330 : W := mkw 0x500845225786ee7b 0x280422912bc3773d 0x4500c30e0f8fffff 0x2280618707c7ffff

def z1331 : W := mkw 0x100045021404284a 0x080022810a021425 0xff00fffffc8c7fff 0xff807ffffe463fff

def z1332 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xfdffff0e03fff9c1 0x7effff8701fffce0

def z1333 : W := mkw 0x10e7ff4a9c04284a 0x0873ffa54e021425 0xfffffffffc8c7fff 0xfffffffffe463fff

def z1334 : W := mkw 0x11eeff0002ef784a 0x08f77f800177bc25 0xfdffff0003fff83f 0x7effff8001fffc1f

def z1335 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x7cffc0ee03fc01c1 0x3e7fe07701fe00e0

def z1336 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x64ffc0fe00fc07c0 0xb27fe07f007e03e0

def z1337 : W := mkw 0xf01100fedd1087ef 0xf808807f6e8843f7 0x020000fffc0007fe 0x8100007ffe0003ff

def z1338 : W := mkw 0x00f7ffdc88000000 0x007bffee44000000 0xfaffffffcc000000 0xfd7fffffe6000000

def z1339 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xfdffff000ffff807 0x7effff8007fffc03

def z1340 : W := mkw 0x805d80fc8bd80781 0xc02ec07e45ec03c0 0x7effc0ffcffc07c1 0xbf7fe07fe7fe03e0

def z1341 : W := mkw 0xc008002043dac7b1 0xe004001021ed63d8 0x0400000003ff87c1 0x0200000001ffc3e0

def z1342 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x30ffc0fe03fc07c0 0x987fe07f01fe03e0

def z1343 : W := mkw 0x400800204382c631 0x2004001021c16318 0x0000000000806638 0x000000000040331c

def z1344 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfafffffffc000638 0xfd7ffffffe00031c

def z1345 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xbf783cf1f383ff3f 0xdfbc1e78f9c1ff9f

def z1346 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0x30fffcf7f08c62d8 0x187ffe7bf846316c

def z1347 : W := mkw 0x001900f803900701 0x800c807c01c80380 0x7cffc0fe03fc07c1 0xbe7fe07f01fe03e0

def z1348 : W := mkw 0x4108002043effe31 0x2084001021f7ff18 0x0500000003fff801 0x0280000001fffc00

def z1349 : W := mkw 0x006ca80002ca4000 0x0036540001652000 0x7cfff00003ff8001 0x3e7ff80001ffc000

def z1350 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x54ff330003739800 0x2a7f998001b9cc00

def z1351 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfffffffffc8c67f9 0xfffffffffe4633fc

def z1352 : W := mkw 0x11eeff0002ef784a 0x08f77f800177bc25 0xfdffff1e03ffffff 0xfeffff8f01ffffff

def z1353 : W := mkw 0x805d80dc02c80280 0x402ec06e01640140 0x7cffc0fe03fc02c1 0xbe7fe07f01fe0160

def z1354 : W := mkw 0x02f7ffdfbc042800 0x017bffefde021400 0xfefffffffc0c1800 0xff7ffffffe060c00

def z1355 : W := mkw 0x100045021404284a 0x080022810a021425 0x6600cf1e3c8c7ffe 0xb300678f1e463fff

def z1356 : W := mkw 0x00f6ba9120000000 0x007b5d4890000000 0x10ff30e1c0000000 0x087f9870e0000000

def z1357 : W := mkw 0xc05d80fc43d887b1 0xe02ec07e21ec43d8 0x7cffc0fe03fc07f9 0xbe7fe07f01fe03fc

def z1358 : W := mkw 0x12f4ed973404284a 0x097a76cb9a021425 0xff78fffffc8c7fff 0xffbc7ffffe463fff

def z1359 : W := mkw 0x804d806c03d80781 0xc026c03601ec03c0 0x7cffc00e03fc07c1 0x3e7fe00701fe03e0

def z1360 : W := mkw 0x005792dc88000000 0x002bc96e44000000 0xfffff3ffcc8c1fe7 0xfffff9ffe6460ff3

def z1361 : W := mkw 0x5108452257effe7b 0x288422912bf7ff3d 0xef00cf1e3fffffff 0xf780678f1fffffff

def z1362 : W := mkw 0x02f7badfbc000000 0x017bdd6fde000000 0x10ff30efcc000000 0x087f9877e6000000

def z1363 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0xfdfff0fe03ff87c1 0xfefff87f01ffc3e0

def z1364 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xffffff1e3ffff83f 0xffffff8f1ffffc1f

def z1365 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0x93783cf1f303e638 0xc9bc1e78f981f31c

def z1366 : W := mkw 0x03f7ffdfbc4c2800 0x01fbffefde261400 0xfafffffffc0c0000 0xfd7ffffffe060000

def z1367 : W := mkw 0x100045021404284a 0x080022810a021425 0xff87cf1e3ffc7fff 0xffc3e78f1ffe3fff

def z1368 : W := mkw 0x02f7ffdda8000000 0x017bffeed4000000 0x90ff3fe1c0000000 0x487f9ff0e0000000

def z1369 : W := mkw 0x00f7ffd9a8000000 0x007bffecd4000000 0xfafffff9fc000000 0xfd7ffffcfe000000

def z1370 : W := mkw 0x805d80dc02d80380 0xc02ec06e016c01c0 0x7cffc01e03fc03c1 0x3e7fe00f01fe01e0

def z1371 : W := mkw 0x11eeff0002ef784a 0x08f77f800177bc25 0xffffff080fffffff 0xffffff8407ffffff

def z1372 : W := mkw 0x01eeba0002ef7800 0x00f75d000177bc00 0x11ff30000373f800 0x08ff980001b9fc00

def z1373 : W := mkw 0x500800225782c67b 0x280400112bc1633d 0x0300001e3f83e7ff 0x8180000f1fc1f3ff

def z1374 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfffffffffc807f3f 0xfffffffffe403f9f

def z1375 : W := mkw 0x0030289120024000 0x0018144890012000 0xbb783cf1f003e000 0xddbc1e78f801f000

def z1376 : W := mkw 0xc05d80fc43d887a1 0xe02ec07e21ec43d0 0xfffffcfff3ffe7f9 0xfffffe7ff9fff3fc

def z1377 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x7cfff01e03ff87c1 0xbe7ff80f01ffc3e0

def z1378 : W := mkw 0x002a3a0002a35000 0x00151d000151a800 0xffff3f183ff3ff3f 0xffff9f8c1ff9ff9f

def z1379 : W := mkw 0xc05d80fc43d887a1 0xe02ec07e21ec43d0 0xfffff3ffcfff9fe7 0xfffff9ffe7ffcff3

def z1380 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xb1ffff0003fff800 0x58ffff8001fffc00

def z1381 : W := mkw 0x0030289120000000 0x0018144890000000 0xbb783cf1f3038001 0xddbc1e78f981c000

def z1382 : W := mkw 0xc05d80fd63d887b1 0xe02ec07eb1ec43d8 0xfffff0fff3ff87f9 0xfffff87ff9ffc3fc

def z1383 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xbb783cfff383e7f9 0xddbc1e7ff9c1f3fc

def z1384 : W := mkw 0x0028280002824000 0x0014140001412000 0xfdff3c0003f3e001 0x7eff9e0001f9f000

def z1385 : W := mkw 0x03f7ffdda8277800 0x01fbffeed413bc00 0x91ff3fe1c003f800 0x48ff9ff0e001fc00

def z1386 : W := mkw 0xc008002043cac6b1 0x6004001021e56358 0x01000000038fe6f9 0x0080000001c7f37c

def z1387 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfbfffffffc807e3f 0xfdfffffffe403f1f

def z1388 : W := mkw 0x02f7ffdda8000000 0x017bffeed4000000 0x50fff3e1c0000000 0x287ff9f0e0000000

def z1389 : W := mkw 0x400800204382c631 0x2004001021c16318 0x290000100383e639 0x9480000801c1f31c

def z1390 : W := mkw 0x014c800002ef7800 0x00a640000177bc00 0x15ff000003fff801 0x0aff800001fffc00

def z1391 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x30ff3c0003f3e000 0x187f9e0001f9f000

def z1392 : W := mkw 0x00e6ff0000000000 0x00737f8000000000 0xfaffffe1c0000000 0xfd7ffff0e0000000

def z1393 : W := mkw 0x01eeba0002ef7800 0x00f75d000177bc00 0xbdff3c0003fff801 0x5eff9e0001fffc00

def z1394 : W := mkw 0x500800204386ee7b 0x2804001021c3773d 0x01000000038fe6f9 0x0080000001c7f37c

def z1395 : W := mkw 0x402828204382c421 0x2014141021c16210 0xbb783cf1f383e639 0xddbc1e78f9c1f31c

def z1396 : W := mkw 0x12f5eddfbc04284a 0x097af6efde021425 0xef78cffffc8c7fff 0xf7bc67fffe463fff

def z1397 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0x30fffc1633ffe2d8 0x187ffe0b19fff16c

def z1398 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x7effc0fe0ffc07e7 0xbf7fe07f07fe03f3

def z1399 : W := mkw 0x01eeff0216ef7800 0x00f77f810b77bc00 0xfdffff0e0ffff801 0x7effff8707fffc00

def z1400 : W := mkw 0x0038289122824210 0x001c144891412108 0xbb783cf1f383e219 0xddbc1e78f9c1f10c

def z1401 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0x78fffcfff0000000 0xbc7ffe7ff8000000

def z1402 : W := mkw 0x02f7ffdfbc211000 0x017bffefde108800 0xfefffffffc701800 0xff7ffffffe380c00

def z1403 : W := mkw 0xe108002043ffffa5 0xf084001021ffffd2 0x0500000003ffffe7 0x0280000001fffff3

def z1404 : W := mkw 0x402828204382c631 0x2014141021c16318 0x81003c000383e639 0x40801e0001c1f31c

def z1405 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x34ffc0f603fc07c1 0x1a7fe07b01fe03e0

def z1406 : W := mkw 0xc05d80fc43dac7b1 0xe02ec07e21ed63d8 0xfffff0ffc3ffe7f9 0xfffff87fe1fff3fc

def z1407 : W := mkw 0x400800204392c731 0xa004001021c96398 0x0500000003f3e739 0x0280000001f9f39c

def z1408 : W := mkw 0x100045021404284a 0x080022810a021425 0xff00ff1e3f8fffff 0xff807f8f1fc7ffff

def z1409 : W := mkw 0xe01100fc411087a5 0xf008807e208843d2 0x000000fe000007e6 0x8000007f000003f3

def z1410 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x54fff000037f8000 0x2a7ff80001bfc000

def z1411 : W := mkw 0x1057d7de9c04284a 0x082bebef4e021425 0xfffffffffc8c7fff 0xfffffffffe463fff

def z1412 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfafffffffc0007c0 0xfd7ffffffe0003e0

def z1413 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0xfeffc3fe0ffc07c1 0xff7fe1ff07fe03e0

def z1414 : W := mkw 0x0075a8dd20000000 0x003ad46e90000000 0x10ff30e1c0000000 0x087f9870e0000000

def z1415 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0x54fff3efcc0c19c6 0x2a7ff9f7e6060ce3

def z1416 : W := mkw 0x025792dfbc000000 0x012bc96fde000000 0xfafff3fffc000000 0xfd7ff9fffe000000

def z1417 : W := mkw 0x00f6ff9120000000 0x007b7fc890000000 0xf8ffffe1c0000000 0x7c7ffff0e0000000

def z1418 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfffffffffc8c7ad9 0xfffffffffe463d6c

def z1419 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x54ffc0ee03fc07c1 0x2a7fe07701fe03e0

def z1420 : W := mkw 0x11eeff0002ef784a 0x08f77f800177bc25 0xfdffff0003fffad9 0x7effff8001fffd6c

def z1421 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfbfffffffc000421 0xfdfffffffe000210

def z1422 : W := mkw 0x003128d920000000 0x0018946c90000000 0xfaff3cf9f0000000 0xfd7f9e7cf8000000

def z1423 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfafffffffc000526 0xfd7ffffffe000293

def z1424 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0xf9ffff000373f800 0x7cffff8001b9fc00

def z1425 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0x10ff33e1cc000000 0x087f99f0e6000000

def z1426 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0x978733e1cf739d27 0x4bc399f0e7b9ce93

def z1427 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xdf873fe9ff73fd3f 0xefc39ff4ffb9fe9f

def z1428 : W := mkw 0x006ca80002ca4000 0x0036540001652000 0x10ff300003738000 0x087f980001b9c000

def z1429 : W := mkw 0x01e6ff0000277800 0x00f37f800013bc00 0xfdffff000373f801 0x7effff8001b9fc00

def z1430 : W := mkw 0x8045804c00580180 0xc022c026002c00c0 0x7cffc00e007c01c0 0x3e7fe007003e00e0

def z1431 : W := mkw 0x03eeff03beeb5000 0x01f77f81df75a800 0x92ff3f01ff738000 0x497f9f80ffb9c000

def z1432 : W := mkw 0x60021220c9219425 0x300109106490ca12 0xdf8733e1cf739c27 0xefc399f0e7b9ce13

def z1433 : W := mkw 0x010b12488aef7800 0x008589244577bc00 0xdf8733e9cffff801 0xefc399f4e7fffc00

def z1434 : W := mkw 0x025580dda8000000 0x012ac06ed4000000 0x10ff00e1c0000000 0x087f8070e0000000

def z1435 : W := mkw 0x400800204382c631 0x2004001021c16318 0x0000000003038638 0x000000000181c31c

def z1436 : W := mkw 0x00333ad9a8000000 0x00199d6cd4000000 0xffff3ff9fc807f3f 0xffff9ffcfe403f9f

def z1437 : W := mkw 0x014e920002ef7800 0x00a749000177bc00 0xfdfff30003fff801 0x7efff98001fffc00

def z1438 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfffffffffc007d3f 0xfffffffffe003e9f

def z1439 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xbafffcf7f0000000 0xdd7ffe7bf8000000

def z1440 : W := mkw 0x4008002043a3d631 0x2004001021d1eb18 0x0500000003f3fe39 0x0280000001f9ff1c

def z1441 : W := mkw 0x701145fbfd14af7f 0xb808a2fdfe8a57bf 0xef00cffffc8c7fff 0xf78067fffe463fff

def z1442 : W := mkw 0x11eeff0002ef784a 0x08f77f800177bc25 0xffffff1033ffffff 0xffffff8819ffffff

def z1443 : W := mkw 0x01eeba0002eb5000 0x00f75d000175a800 0x11ff300003f3e001 0x08ff980001f9f000

def z1444 : W := mkw 0x4001006841108521 0xa000803420884290 0xdf8733e9cf739d27 0xefc399f4e7b9ce93

def z1445 : W := mkw 0x401100f961108731 0xa008807cb0884398 0x020000f9f0000738 0x8100007cf800039c

def z1446 : W := mkw 0x01eeff0002ef7800 0x00f77f800177bc00 0x7cfffc0003ffe001 0x3e7ffe0001fff000

def z1447 : W := mkw 0x02f7ffdda8000000 0x017bffeed4000000 0xf8ffffffc0000000 0xfc7fffffe0000000

def z1448 : W := mkw 0x11eeba0002ef784a 0x08f75d000177bc25 0x15ff300003ffffff 0x0aff980001ffffff

def z1449 : W := mkw 0x005792dc88000000 0x002bc96e44000000 0xdaff33e9cc000000 0xed7f99f4e6000000

def z1450 : W := mkw 0x6108002043ffff35 0xb084001021ffff9a 0x0500000003ffff3f 0x0280000001ffff9f

def z1451 : W := mkw 0x1075eddf3404284a 0x083af6ef9a021425 0xfffffffffc8c7fff 0xfffffffffe463fff

def z1452 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xbb78fcf7f38fe6f9 0xddbc7e7bf9c7f37c

def z1453 : W := mkw 0x500800204386ee7b 0x2804001021c3773d 0x010000000383fe3f 0x0080000001c1ff1f

def z1454 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0x54fff30e0f7f99c6 0x2a7ff98707bfcce3

def z1455 : W := mkw 0x02f7ffdfbc024000 0x017bffefde012000 0xfbfffffffc03e000 0xfdfffffffe01f000

def z1456 : W := mkw 0x125580dfbc00004a 0x092ac06fde000025 0x7effc0fffc8c07ff 0xbf7fe07ffe4603ff

def z1457 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xdf8733ffcf739fe7 0xefc399ffe7b9cff3

def z1458 : W := mkw 0x82f7badda8580180 0xc17bdd6ed42c00c0 0x54fff0efc07c01c0 0x2a7ff877e03e00e0

def z1459 : W := mkw 0x11eeff0216ef784a 0x08f77f810b77bc25 0xffffff1e3ffffad9 0xffffff8f1ffffd6c

def z1460 : W := mkw 0x0030289120000000 0x0018144890000000 0xff783ff9fc001d27 0xffbc1ffcfe000e93

def z1461 : W := mkw 0x400800204382c631 0x2004001021c16318 0x0100000003038421 0x008000000181c210

def z1462 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xdf8733e1cf739827 0x6fc399f0e7b9cc13

def z1463 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0x62ffcffffc000000 0xb17fe7fffe000000

def z1464 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x7cffccfe33fc67d9 0xbe7fe67f19fe33ec

def z1465 : W := mkw 0x02f6ff97bc000000 0x017b7fcbde000000 0xba78fff7fc000000 0xdd3c7ffbfe000000

def z1466 : W := mkw 0x601100f9e9108735 0xb008807cf488439a 0x000000e1c0000000 0x00000070e0000000

def z1467 : W := mkw 0x02f7ffdda8000000 0x017bffeed4000000 0xfaffffe9cc000000 0xfd7ffff4e6000000

def z1468 : W := mkw 0x02f4ed9734000000 0x017a76cb9a000000 0x2278ccf7f0000000 0x913c667bf8000000

def z1469 : W := mkw 0x02b23a91a8000000 0x01591d48d4000000 0x107830e1c0000000 0x083c1870e0000000

def z1470 : W := mkw 0x403828916282c230 0x201c1448b1416118 0xbb783cf1f083e238 0xddbc1e78f841f11c

def z1471 : W := mkw 0x02f7badda8000000 0x017bdd6ed4000000 0x92ff3ce1f0000000 0x497f9e70f8000000

def z1472 : W := mkw 0x12b27f93bc04284a 0x09593fc9de021425 0xff78fffffc8c7fff 0xffbc7ffffe463fff

def z1473 : W := mkw 0x0030289120000000 0x0018144890000000 0xbb783cf1f0000421 0xddbc1e78f8000210

def z1474 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfafffffffc0c00c0 0xfd7ffffffe060060

def z1475 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xfbfffffffc001826 0xfdfffffffe000c13

def z1476 : W := mkw 0x401800b043808621 0x200c005821c04310 0xbb783cf1f383e639 0xddbc1e78f9c1f31c

def z1477 : W := mkw 0x60031268c9319525 0xb00189346498ca92 0xff87f3e9cfff9d27 0xffc3f9f4e7ffce93

def z1478 : W := mkw 0xc21100fffd1087b1 0xe108807ffe8843d8 0x020000fffc0007f8 0x8100007ffe0003fc

def z1479 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfefffffffc8c7bde 0xff7ffffffe463def

def z1480 : W := mkw 0x00e6ff0214211000 0x00737f810a108800 0xffffff1e3f739d27 0xffffff8f1fb9ce93

def z1481 : W := mkw 0x00333ad9a8000000 0x00199d6cd4000000 0xbaff3cf1f0000000 0xdd7f9e78f8000000

def z1482 : W := mkw 0x23f7ffdfbc7d3904 0x91fbffefde3e9c82 0xfefffffffc7c1906 0xff7ffffffe3e0c83

def z1483 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xff783cf9f383e739 0xffbc1e7cf9c1f39c

def z1484 : W := mkw 0x02d7d7de9c000000 0x016bebef4e000000 0xfafff3ffcc000000 0xfd7ff9ffe6000000

def z1485 : W := mkw 0x01eeba0002ef7800 0x00f75d000177bc00 0x14ff3000037f9800 0x0a7f980001bfcc00

def z1486 : W := mkw 0x805d80fc03d80781 0xc02ec07e01ec03c0 0x7effc0fe33fc07f9 0xbf7fe07f19fe03fc

def z1487 : W := mkw 0x0030289334000000 0x001814499a000000 0xba783cfffc000000 0xdd3c1e7ffe000000

def z1488 : W := mkw 0x403828b16382c631 0x201c1458b1c16318 0xb9783cf1f383e219 0x5cbc1e78f9c1f10c

def z1489 : W := mkw 0x400800204382c631 0x2004001021c16318 0x990030000383e639 0x4c80180001c1f31c

def z1490 : W := mkw 0x00333ad9a8000000 0x00199d6cd4000000 0xdaff33e9cc000000 0xed7f99f4e6000000

def z1491 : W := mkw 0x01eeff0002eb5000 0x00f77f800175a800 0x30fffc0003738000 0x187ffe0001b9c000

def z1492 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xdaff3fe9fc000000 0xed7f9ff4fe000000

def z1493 : W := mkw 0x0275a8dfbc000000 0x013ad46fde000000 0xfafffcfffc000000 0xfd7ffe7ffe000000

def z1494 : W := mkw 0x02f7ffdfbc024010 0x017bffefde012008 0xfafffffffc006018 0xfd7ffffffe00300c

def z1495 : W := mkw 0x4008002043808621 0x2004001021c04310 0x0100000003838621 0x0080000001c1c310

def z1496 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xd2ffffeffc000000 0x697ffff7fe000000

def z1497 : W := mkw 0x41ced72043effe31 0x20e76b9021f7ff18 0x4587c30003fffe39 0x22c3e18001ffff1c

def z1498 : W := mkw 0x12f7ffdfbc04284a 0x097bffefde021425 0xfffffffffc8c79c7 0xfffffffffe463ce3

def z1499 : W := mkw 0x70227f03fc27f87e 0x38113f81fe13fc3f 0x83003f01fc03f83e 0x41801f80fe01fc1f

def z1500 : W := mkw 0xe003126cc93195a5 0xf00189366498cad2 0xdf8733efcf739de7 0xefc399f7e7b9cef3

def z1501 : W := mkw 0x400800204382c631 0x2004001021c16318 0xcf0003080f83ff3f 0xe780018407c1ff9f

def z1502 : W := mkw 0x01eeba0002ef7800 0x00f75d000177bc00 0xddff330003fff801 0x6eff998001fffc00

def z1503 : W := mkw 0x621100fffd108735 0xb108807ffe88439a 0x020000fffc00073e 0x8100007ffe00039f

def z1504 : W := mkw 0x00306d9120042800 0x001836c890021400 0xff78fff1f08c7801 0xffbc7ff8f8463c00

def z1505 : W := mkw 0x11eeff0002ef784a 0x08f77f800177bc25 0xfdffff0003fff9c7 0x7effff8001fffce3

def z1506 : W := mkw 0x02f7ffdfbc042800 0x017bffefde021400 0xfafffffffc8c6000 0xfd7ffffffe463000

def z1507 : W := mkw 0x01eeff0002eb5000 0x00f77f800175a800 0xf9ffff0003f3e001 0x7cffff8001f9f000

def z1508 : W := mkw 0x02b37fdfbc000000 0x0159bfefde000000 0xba783ffffc000000 0xdd3c1ffffe000000

def z1509 : W := mkw 0x12f7ffdfbc00004a 0x097bffefde000025 0xfffffffffc001fff 0xfffffffffe000fff

def z1510 : W := mkw 0x0030289120000000 0x0018144890000000 0xba783cf1f0000638 0xdd3c1e78f800031c

def z1511 : W := mkw 0x02f7ffdfbc000000 0x017bffefde000000 0xa278fffffc000000 0xd13c7ffffe000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z8,z6]),(0,[z9,z1,z3,z4,z5,z6,z10]),(0,[z1,z2,z11,z4,z12,z5,z6])],[(0,[z13,z1,z2,z3,z4,z5,z6]),(1,[z1,z3,z14,z4,z5,z6]),(0,[z1,z2,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z16,z4,z5,z6]),(0,[z17,z1,z2,z3,z5,z6,z18])],[(0,[z1,z19,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z21,z4,z5,z6]),(0,[z22,z1,z2,z3,z4,z5,z23])],[(0,[z24,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z25,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z26,z6]),(1,[z1,z3,z4,z5,z27,z6])],[(0,[z28,z1,z2,z3,z4,z5,z18])],[(0,[z29,z1,z30,z3,z4,z5,z6]),(0,[z31,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z32,z4,z5,z6]),(0,[z1,z2,z3,z4,z33,z5,z6]),(0,[z1,z2,z3,z34,z4,z5,z6]),(0,[z1,z3,z35,z36,z4,z5,z6])],[(0,[z37,z2,z3,z38,z4,z5,z6]),(0,[z39,z1,z2,z3,z4,z5,z6]),(0,[z24,z1,z2,z3,z4,z5,z18]),(0,[z40,z1,z2,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z5,z42])],[(0,[z43,z2,z3,z4,z44,z5,z6]),(0,[z1,z30,z2,z45,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z47,z6])],[(0,[z43,z19,z2,z3,z4,z5,z6]),(0,[z48,z1,z2,z3,z4,z5,z6]),(0,[z41,z1,z3,z45,z4,z5,z6]),(0,[z1,z20,z3,z45,z4,z5,z6]),(0,[z49,z1,z30,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z50,z6]),(0,[z43,z2,z3,z38,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z6])],[(0,[z52,z1,z2,z3,z4,z5,z6])],[(1,[z2,z3,z53,z4,z5,z6]),(0,[z1,z2,z3,z54,z4,z5,z6]),(0,[z1,z2,z3,z55,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z56]),(0,[z57,z1,z3,z4,z5,z58,z6])],[(0,[z1,z3,z59,z4,z5,z60,z6]),(0,[z1,z61,z2,z3,z4,z5,z6]),(0,[z1,z2,z62,z3,z4,z5,z6])],[(0,[z63,z1,z2,z3,z4,z5,z6]),(0,[z49,z1,z3,z45,z4,z5,z6]),(1,[z9,z1,z3,z5,z6,z18])]],
   [[(0,[z2,z3,z38,z64,z4,z5,z6]),(0,[z1,z3,z38,z59,z4,z5,z6]),(0,[z65,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z66,z3,z4,z5,z6])],[(0,[z1,z30,z3,z67,z4,z5,z6]),(0,[z68,z1,z2,z3,z4,z69,z6])],[(0,[z43,z2,z3,z4,z5,z70,z6]),(0,[z1,z30,z3,z4,z71,z5,z6]),(0,[z1,z2,z3,z72,z4,z5,z6])],[(0,[z1,z3,z45,z59,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z73,z6]),(0,[z1,z2,z3,z4,z5,z74,z6]),(0,[z75,z1,z2,z3,z4,z5,z6])],[],[(0,[z76,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z12,z5,z77,z6]),(0,[z1,z2,z3,z78,z4,z5,z6])],[(0,[z1,z2,z79,z3,z4,z5,z6]),(0,[z68,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z80,z5,z6,z18])],[(0,[z1,z81,z2,z3,z4,z5,z6])],[(0,[z82,z2,z3,z38,z4,z5,z6]),(0,[z2,z3,z83,z38,z4,z5,z6])],[(0,[z84,z9,z1,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z5,z86])],[(0,[z87,z1,z2,z3,z4,z5,z6]),(0,[z22,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z88,z4,z5,z6])],[(0,[z89,z1,z2,z3,z4,z5,z6]),(0,[z90,z2,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z91,z4,z5,z92])],[(0,[z84,z1,z2,z3,z4,z5,z6])],[(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z1,z94,z2,z3,z4,z5,z6]),(0,[z2,z95,z3,z96,z4,z5,z6])],[(0,[z43,z2,z3,z59,z4,z5,z6]),(0,[z1,z3,z45,z4,z5,z6,z97])]],
   [[(0,[z98,z1,z19,z3,z4,z5,z6]),(0,[z99,z1,z2,z3,z4,z5,z6]),(0,[z9,z43,z1,z3,z4,z5,z6]),(0,[z1,z3,z45,z4,z5,z6,z100]),(0,[z1,z2,z3,z101,z4,z5,z6]),(0,[z1,z2,z3,z102,z4,z5,z6])],[(0,[z1,z3,z4,z103,z104,z5,z6])],[(0,[z85,z43,z2,z3,z4,z5,z6])],[(0,[z105,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z106,z4,z5,z6])],[(0,[z43,z2,z11,z3,z4,z5,z6]),(0,[z43,z2,z3,z4,z5,z6,z18]),(0,[z107,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z108,z6])],[(0,[z1,z2,z3,z4,z5,z60,z6])],[(0,[z9,z1,z66,z3,z4,z5,z6]),(0,[z9,z1,z2,z3,z109,z5,z6]),(0,[z22,z1,z2,z3,z4,z5,z110])],[(0,[z111,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z100,z97])],[(0,[z1,z2,z3,z4,z112,z5,z6]),(0,[z113,z1,z2,z3,z4,z5,z6]),(0,[z114,z1,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z18,z97])],[(0,[z115,z1,z2,z3,z4,z5,z6]),(0,[z116,z1,z2,z3,z4,z5,z6]),(0,[z41,z2,z3,z38,z4,z5,z6]),(0,[z117,z1,z3,z4,z5,z60,z6]),(0,[z1,z2,z3,z118,z4,z5,z6])],[(0,[z2,z3,z38,z67,z4,z5,z6]),(0,[z1,z119,z2,z3,z91,z5,z6]),(0,[z1,z3,z59,z4,z5,z120,z6]),(0,[z1,z2,z3,z121,z4,z5,z6])],[(0,[z1,z95,z3,z25,z4,z5,z6]),(0,[z122,z1,z123,z3,z4,z5,z6]),(0,[z1,z2,z3,z124,z4,z5,z6])],[(0,[z2,z3,z38,z4,z5,z73,z6]),(0,[z43,z2,z3,z4,z5,z6,z100])],[(0,[z1,z125,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z126,z5,z6]),(0,[z1,z2,z3,z4,z5,z127,z6])],[(0,[z49,z2,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z128,z5,z6]),(0,[z1,z2,z3,z5,z23,z6,z129]),(0,[z85,z1,z130,z3,z4,z5,z6]),(0,[z1,z131,z3,z4,z5,z92,z6])]],
   [[(0,[z2,z3,z67,z4,z132,z5,z6]),(0,[z1,z2,z133,z3,z4,z5,z6]),(1,[z2,z134,z3,z4,z5,z6]),(1,[z1,z123,z3,z4,z5,z6])],[(0,[z43,z135,z2,z3,z4,z5,z6]),(1,[z1,z136,z3,z4,z5,z6]),(0,[z137,z9,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z27,z58,z6])],[(0,[z2,z3,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z12,z6,z97]),(1,[z1,z3,z4,z5,z6,z138])],[],[(0,[z1,z3,z45,z4,z5,z92,z6])],[(0,[z1,z139,z3,z59,z4,z5,z6]),(0,[z1,z140,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z73,z97])],[(0,[z1,z2,z3,z141,z4,z5,z6]),(0,[z1,z2,z142,z3,z4,z5,z6])],[(1,[z1,z3,z4,z143,z5,z6]),(0,[z1,z2,z3,z4,z5,z144,z6]),(0,[z145,z1,z2,z3,z4,z5,z6]),(1,[z122,z1,z2,z4,z5,z100]),(0,[z1,z2,z3,z4,z5,z6,z146])],[(0,[z1,z2,z147,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z148,z6]),(0,[z9,z149,z1,z3,z4,z5,z6]),(0,[z150,z1,z3,z45,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z6,z151]),(0,[z1,z2,z152,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z153])],[(0,[z1,z154,z2,z3,z4,z5,z6]),(1,[z1,z3,z36,z4,z5,z6])],[(0,[z1,z2,z3,z67,z4,z5,z155]),(1,[z1,z2,z11,z4,z12,z6])],[(0,[z9,z1,z3,z4,z5,z60,z6])],[(0,[z156,z1,z2,z3,z4,z5,z6]),(0,[z157,z1,z2,z3,z4,z5,z6]),(1,[z158,z1,z3,z4,z159,z6])],[(0,[z1,z2,z3,z4,z5,z6,z160]),(0,[z9,z22,z1,z3,z4,z5,z6]),(0,[z41,z1,z161,z3,z4,z5,z6])],[(0,[z1,z3,z59,z4,z5,z23,z6])],[(0,[z1,z2,z3,z4,z162,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z163]),(0,[z164,z9,z1,z3,z4,z5,z6])]],
   [[(0,[z165,z2,z3,z4,z5,z60,z6]),(0,[z49,z1,z2,z3,z166,z5,z6]),(1,[z2,z3,z4,z5,z6,z167])],[(0,[z43,z2,z168,z3,z4,z5,z6]),(0,[z1,z30,z3,z4,z132,z5,z6]),(0,[z1,z2,z3,z4,z169,z5,z6]),(0,[z1,z2,z3,z4,z5,z120,z6])],[(0,[z98,z1,z3,z45,z4,z5,z6]),(0,[z43,z2,z3,z91,z4,z5,z6]),(1,[z170,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z171])],[(0,[z2,z3,z38,z4,z109,z5,z6]),(0,[z172,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z173])],[(0,[z1,z2,z3,z4,z5,z174,z6]),(0,[z2,z3,z67,z4,z71,z5,z6]),(0,[z175,z1,z2,z3,z4,z5,z6]),(1,[z1,z20,z3,z4,z176,z6]),(0,[z1,z2,z3,z4,z5,z6,z177]),(1,[z2,z3,z178,z4,z5,z6])],[(0,[z28,z1,z136,z3,z4,z5,z6]),(0,[z1,z119,z3,z45,z4,z5,z6]),(0,[z49,z1,z2,z3,z80,z5,z6])],[(1,[z149,z2,z3,z67,z5,z6]),(0,[z1,z3,z59,z4,z5,z8,z6]),(0,[z1,z179,z2,z3,z4,z5,z6]),(1,[z2,z3,z96,z4,z5,z6]),(0,[z1,z2,z3,z180,z4,z5,z6])],[(0,[z181,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z45,z4,z5,z77,z6]),(0,[z1,z2,z182,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z183,z5,z6])],[(0,[z1,z2,z3,z184,z4,z5,z6]),(0,[z43,z1,z2,z147,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z185,z6]),(0,[z186,z1,z2,z3,z4,z5,z6]),(0,[z9,z1,z30,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z104,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z187])],[(0,[z188,z43,z2,z3,z4,z5,z6]),(1,[z1,z30,z66,z4,z5,z6]),(0,[z1,z2,z3,z4,z189,z5,z6])],[(0,[z190,z1,z2,z3,z4,z5,z6]),(0,[z1,z191,z2,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z192,z5,z6]),(0,[z1,z2,z193,z3,z4,z5,z6]),(0,[z1,z2,z194,z3,z4,z5,z6])],[(0,[z63,z98,z2,z3,z4,z5,z6]),(0,[z1,z30,z3,z38,z4,z5,z6]),(0,[z9,z43,z2,z3,z4,z5,z6]),(0,[z1,z2,z195,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z196]),(0,[z122,z28,z1,z2,z3,z4,z5]),(0,[z197,z1,z3,z45,z4,z5,z6]),(0,[z1,z30,z3,z166,z4,z5,z6]),(0,[z1,z198,z2,z3,z4,z5,z6]),(0,[z199,z1,z2,z3,z4,z5,z6])],[(0,[z37,z1,z2,z45,z4,z5,z6])],[(0,[z1,z2,z200,z3,z4,z5,z6]),(0,[z1,z2,z3,z201,z4,z5,z6])],[(0,[z1,z19,z3,z4,z5,z23,z6]),(0,[z9,z1,z147,z3,z4,z5,z6]),(0,[z202,z1,z2,z3,z4,z5,z6])],[(1,[z3,z38,z45,z4,z5,z6]),(0,[z203,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z95,z80,z4,z5,z6])]],
   [[(0,[z204,z1,z2,z3,z4,z5,z6]),(0,[z205,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z206]),(0,[z1,z3,z59,z4,z5,z58,z6]),(0,[z1,z161,z2,z3,z4,z5,z6])],[(0,[z2,z3,z38,z207,z4,z5,z6]),(0,[z1,z30,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z208]),(0,[z1,z2,z3,z4,z5,z209,z6])],[(0,[z1,z2,z3,z4,z210,z5,z6]),(0,[z1,z211,z2,z3,z4,z5,z6])],[(0,[z43,z2,z3,z4,z5,z77,z6]),(0,[z1,z2,z212,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z213]),(1,[z150,z1,z3,z4,z5,z6]),(0,[z1,z2,z11,z3,z4,z77,z6])],[(0,[z1,z2,z3,z4,z214,z5,z6]),(0,[z1,z130,z2,z3,z4,z5,z6]),(0,[z1,z215,z2,z3,z4,z5,z6])],[(0,[z43,z1,z2,z3,z4,z5,z6]),(0,[z158,z1,z3,z4,z5,z159,z6]),(0,[z1,z2,z3,z4,z5,z23,z6])],[(0,[z43,z2,z3,z4,z5,z216,z6]),(0,[z1,z2,z3,z4,z5,z6,z217]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z30,z3,z4,z218,z5,z6]),(0,[z17,z9,z1,z3,z4,z5,z6]),(0,[z68,z9,z1,z3,z4,z5,z6]),(0,[z219,z1,z2,z3,z4,z5,z6])],[(0,[z165,z7,z2,z3,z4,z5,z6]),(0,[z220,z1,z2,z3,z4,z5,z6])],[(0,[z1,z119,z2,z3,z5,z6,z18]),(0,[z1,z3,z59,z80,z4,z5,z6]),(0,[z1,z2,z3,z221,z4,z5,z6])],[(0,[z222,z1,z2,z3,z4,z5,z6]),(0,[z17,z1,z2,z3,z4,z5,z6])],[(0,[z90,z1,z2,z147,z4,z5,z6]),(0,[z2,z3,z38,z4,z132,z5,z6]),(1,[z1,z223,z3,z4,z5,z6]),(0,[z1,z2,z3,z224,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z225,z6])],[(0,[z1,z2,z3,z83,z4,z5,z6]),(1,[z117,z1,z3,z4,z5,z6]),(0,[z1,z3,z45,z4,z5,z6,z18]),(0,[z1,z2,z3,z4,z5,z6,z226]),(0,[z85,z1,z2,z3,z80,z5,z6]),(0,[z1,z2,z3,z35,z4,z5,z6])],[(0,[z1,z168,z3,z4,z5,z23,z6]),(0,[z1,z227,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z228])],[(0,[z7,z1,z30,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z8,z6]),(0,[z28,z1,z2,z227,z3,z4,z5]),(0,[z1,z3,z4,z5,z6,z138,z18])],[(0,[z149,z1,z229,z3,z4,z5,z6]),(0,[z1,z230,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z231,z6]),(0,[z1,z2,z3,z4,z5,z232,z6])],[(0,[z1,z2,z3,z4,z5,z233,z6]),(0,[z1,z2,z3,z4,z104,z5,z6]),(0,[z1,z2,z3,z4,z5,z234,z6])]],
   [[(0,[z7,z43,z2,z3,z4,z5,z6]),(0,[z24,z1,z2,z227,z3,z4,z5]),(0,[z1,z30,z3,z59,z4,z5,z6])],[(0,[z63,z1,z3,z59,z4,z5,z6]),(0,[z98,z19,z2,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z5,z6,z196]),(0,[z1,z2,z3,z4,z192,z5,z6])],[(0,[z98,z2,z3,z38,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z235]),(0,[z1,z3,z45,z4,z12,z5,z6]),(0,[z85,z1,z30,z3,z4,z5,z6]),(0,[z122,z9,z1,z3,z4,z5,z6]),(0,[z1,z2,z236,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z100,z18])],[(0,[z237,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z38,z38,z4,z5,z6]),(0,[z2,z3,z38,z166,z4,z5,z6]),(0,[z43,z1,z3,z59,z4,z5,z6]),(0,[z1,z2,z238,z3,z4,z5,z6]),(0,[z239,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z240,z5,z6]),(0,[z1,z2,z241,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z5,z242]),(0,[z243,z1,z2,z3,z4,z5,z6]),(0,[z122,z1,z2,z3,z4,z5,z6])],[(0,[z43,z2,z3,z4,z5,z6,z110]),(0,[z1,z3,z166,z59,z4,z5,z6])],[(0,[z90,z1,z2,z3,z4,z5,z6]),(1,[z9,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z244]),(0,[z1,z2,z3,z4,z5,z58,z6])],[(1,[z245,z2,z3,z38,z4,z5]),(0,[z85,z1,z3,z45,z4,z5,z6]),(0,[z17,z1,z3,z59,z4,z5,z6]),(0,[z68,z1,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z91,z104,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z246]),(0,[z1,z2,z3,z247,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z248,z3,z4,z5,z6]),(0,[z249,z1,z30,z3,z4,z5,z6])],[(0,[z1,z2,z3,z250,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z251]),(0,[z9,z1,z3,z4,z5,z23,z6])],[(0,[z1,z30,z3,z4,z5,z6,z97]),(1,[z1,z81,z3,z4,z5,z6]),(0,[z252,z1,z2,z3,z4,z5,z6])],[(0,[z24,z2,z168,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z253,z5,z6]),(0,[z37,z170,z2,z3,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z6,z100]),(0,[z22,z1,z3,z59,z4,z5,z6]),(0,[z254,z1,z2,z3,z4,z5,z6])],[(0,[z255,z1,z2,z3,z4,z5,z6]),(0,[z1,z19,z30,z3,z4,z5,z6]),(0,[z2,z3,z256,z38,z4,z5,z6]),(0,[z2,z3,z38,z4,z71,z5,z6]),(0,[z43,z2,z3,z4,z12,z5,z6]),(0,[z28,z1,z257,z3,z4,z5,z6]),(0,[z1,z2,z227,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z258])],[(0,[z1,z2,z3,z4,z259,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z260]),(0,[z158,z1,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z261,z4,z5,z6]),(0,[z1,z2,z3,z80,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z86,z6])]],
   [[(0,[z1,z2,z3,z262,z4,z5,z6]),(0,[z1,z147,z3,z45,z4,z5,z6]),(0,[z24,z28,z2,z3,z4,z5,z6]),(0,[z263,z1,z2,z3,z4,z5,z6]),(0,[z1,z264,z2,z3,z4,z5,z92])],[(0,[z1,z2,z3,z4,z5,z265,z6]),(0,[z1,z2,z266,z3,z4,z5,z6]),(0,[z9,z1,z3,z35,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z73,z18]),(0,[z1,z2,z267,z3,z4,z5,z6])],[(0,[z1,z82,z2,z3,z4,z5,z6]),(0,[z268,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z269,z4,z5,z6])],[(0,[z9,z1,z3,z4,z5,z8,z6]),(0,[z1,z2,z3,z270,z4,z5,z6]),(0,[z1,z2,z3,z4,z271,z5,z6])],[(0,[z1,z19,z3,z45,z4,z5,z6]),(0,[z272,z1,z2,z3,z4,z5,z6]),(0,[z122,z1,z3,z59,z4,z5,z6]),(0,[z1,z20,z2,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z273]),(0,[z1,z2,z274,z3,z4,z5,z6])],[(0,[z1,z275,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z276]),(0,[z1,z277,z2,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z104,z5,z6])],[(0,[z278,z2,z3,z38,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z279,z6])],[(0,[z7,z149,z2,z3,z4,z5,z6]),(0,[z165,z2,z3,z4,z5,z8,z6])],[(0,[z2,z3,z38,z59,z4,z5,z6]),(0,[z1,z280,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z132,z5,z6]),(0,[z1,z2,z3,z4,z5,z281,z6]),(0,[z1,z3,z45,z91,z4,z5,z6]),(1,[z1,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z282])],[(0,[z24,z98,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z283,z4,z5,z6]),(0,[z1,z2,z3,z45,z4,z5,z6])],[(0,[z1,z2,z3,z4,z284,z5,z6]),(0,[z1,z2,z3,z4,z5,z285,z6])],[(0,[z9,z1,z3,z4,z5,z58,z6]),(0,[z255,z1,z3,z59,z4,z5,z6]),(0,[z286,z1,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z287,z6])],[(0,[z288,z1,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z289,z5,z6])],[(0,[z290,z1,z30,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z291,z6])]],
   [[(1,[z1,z3,z292,z4,z5,z6]),(0,[z293,z1,z2,z3,z4,z5,z6])],[(0,[z24,z1,z2,z3,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z92,z6]),(0,[z122,z1,z294,z3,z4,z5,z6]),(0,[z122,z1,z2,z3,z4,z295,z6])],[(0,[z1,z168,z3,z45,z4,z5,z6]),(0,[z1,z30,z168,z3,z4,z5,z6]),(0,[z290,z43,z2,z3,z4,z5,z6])],[(0,[z63,z1,z168,z3,z4,z5,z6]),(0,[z1,z3,z45,z4,z176,z5,z6]),(0,[z1,z20,z3,z59,z4,z5,z6]),(0,[z1,z296,z2,z3,z4,z5,z6])],[(0,[z9,z1,z227,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z297,z6])],[(0,[z2,z3,z38,z4,z5,z6,z97]),(0,[z9,z1,z3,z80,z4,z5,z6])],[(0,[z2,z3,z38,z4,z5,z6,z100]),(0,[z1,z2,z3,z4,z5,z298,z6]),(1,[z1,z294,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z295,z6])],[(0,[z1,z299,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z300,z6]),(0,[z1,z2,z3,z4,z5,z301,z6]),(0,[z1,z2,z3,z302,z4,z5,z6])],[(0,[z30,z2,z3,z38,z4,z5,z6]),(0,[z85,z2,z3,z38,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z303,z6]),(0,[z1,z30,z3,z4,z304,z5,z6]),(0,[z9,z1,z3,z270,z4,z5,z6]),(0,[z1,z3,z35,z59,z4,z5,z6]),(0,[z158,z1,z2,z3,z4,z176,z6]),(1,[z1,z2,z95,z80,z5,z6])],[(0,[z1,z2,z305,z3,z4,z5,z6])],[(0,[z1,z2,z306,z3,z4,z5,z6]),(0,[z199,z9,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z59,z4,z5,z307]),(0,[z308,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z64,z4,z5,z6]),(0,[z1,z2,z309,z3,z4,z5,z6]),(0,[z1,z66,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z310,z6]),(0,[z1,z2,z3,z4,z5,z311,z6]),(0,[z57,z1,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z71,z5,z6]),(0,[z28,z1,z3,z59,z4,z5,z6]),(0,[z1,z3,z45,z4,z5,z216,z6])],[(0,[z1,z2,z3,z4,z5,z312,z6]),(0,[z313,z1,z30,z3,z4,z5,z6])],[(0,[z22,z1,z168,z3,z4,z5,z6]),(0,[z43,z2,z3,z4,z176,z5,z6]),(0,[z1,z3,z59,z67,z4,z5,z6])]],
   [[(0,[z165,z1,z133,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z314]),(0,[z24,z1,z3,z59,z4,z5,z6])],[(0,[z9,z1,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z315,z6]),(0,[z1,z2,z316,z3,z4,z5,z6])],[(0,[z19,z2,z3,z4,z71,z5,z6]),(0,[z317,z1,z2,z3,z4,z5,z6]),(0,[z37,z9,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z318,z5,z6]),(0,[z85,z1,z236,z3,z4,z5,z6]),(0,[z319,z1,z2,z3,z4,z5,z6])],[(0,[z43,z2,z3,z4,z5,z159,z6]),(0,[z1,z2,z3,z320,z4,z5,z6])],[(1,[z63,z168,z3,z4,z5,z6]),(0,[z1,z2,z321,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z322,z6])],[(0,[z7,z1,z2,z3,z132,z5,z6]),(0,[z37,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z227,z4,z5,z73,z6])],[(0,[z43,z264,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z323,z6]),(0,[z324,z1,z2,z3,z4,z5,z6]),(0,[z325,z1,z2,z3,z4,z5,z6])],[(0,[z1,z326,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z71,z5,z60,z6]),(0,[z1,z3,z327,z45,z4,z5,z6])],[(0,[z1,z2,z3,z4,z328,z5,z6]),(0,[z165,z290,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z287,z5,z6]),(0,[z1,z2,z3,z4,z5,z329,z6]),(0,[z1,z2,z3,z4,z330,z5,z6])],[(0,[z331,z9,z1,z3,z4,z5,z6]),(0,[z332,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z129]),(0,[z1,z333,z2,z3,z4,z5,z6]),(0,[z1,z334,z2,z3,z4,z5,z6])],[(0,[z2,z3,z38,z4,z5,z92,z6]),(0,[z335,z1,z30,z3,z4,z5,z6]),(0,[z122,z1,z2,z3,z336,z5,z6])],[(0,[z337,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z338,z4,z5,z6]),(0,[z1,z2,z3,z4,z295,z5,z6])],[(0,[z331,z1,z2,z3,z4,z5,z6]),(0,[z9,z1,z264,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z339,z5,z6])],[(0,[z335,z43,z2,z3,z4,z5,z6]),(1,[z1,z257,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z340,z5,z6]),(0,[z1,z3,z45,z4,z5,z6,z110])],[(0,[z341,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z336,z5,z6])]],
   [[(0,[z202,z1,z3,z59,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z120]),(0,[z1,z2,z3,z342,z4,z5,z6]),(0,[z343,z2,z95,z3,z4,z5,z6])],[(0,[z1,z223,z95,z3,z4,z5,z6]),(0,[z344,z1,z2,z3,z4,z5,z6])],[(1,[z2,z3,z345,z38,z4,z5]),(0,[z122,z24,z1,z2,z3,z4,z5]),(0,[z9,z1,z3,z4,z5,z310,z6]),(0,[z122,z346,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z69,z5,z216])],[(0,[z1,z95,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z166,z4,z5,z347]),(0,[z1,z2,z3,z4,z5,z92,z97])],[(0,[z37,z1,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z348,z4,z5,z6]),(0,[z1,z2,z95,z3,z4,z5,z6]),(0,[z1,z2,z11,z3,z4,z12,z6]),(0,[z1,z2,z3,z4,z5,z92,z100])],[(0,[z1,z20,z168,z3,z4,z5,z6]),(1,[z1,z2,z3,z91,z5,z92])],[(0,[z349,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z67,z4,z5,z6]),(0,[z7,z1,z3,z45,z4,z5,z6]),(0,[z149,z1,z2,z3,z67,z5,z6]),(0,[z350,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z351,z5,z6])],[(0,[z90,z9,z1,z3,z4,z5,z6]),(0,[z1,z2,z352,z3,z4,z5,z6]),(0,[z249,z1,z3,z80,z4,z5,z6]),(1,[z346,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z353,z5,z6]),(0,[z1,z30,z11,z3,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z6,z18]),(0,[z1,z3,z59,z4,z109,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z354])],[(0,[z355,z1,z2,z3,z4,z5,z6]),(0,[z356,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z357,z5,z6]),(0,[z1,z11,z3,z45,z4,z5,z6])],[(0,[z1,z2,z3,z4,z358,z5,z6])],[(0,[z1,z359,z2,z3,z4,z5,z6]),(1,[z222,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z16,z5,z6]),(1,[z17,z1,z2,z3,z5,z18])],[(0,[z98,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z360]),(0,[z1,z361,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z362,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z363]),(1,[z243,z1,z3,z4,z5,z6])],[(0,[z364,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z138])],[(0,[z290,z2,z3,z4,z71,z5,z6]),(0,[z1,z30,z3,z4,z12,z5,z6]),(1,[z1,z3,z59,z4,z5,z120]),(0,[z1,z2,z4,z5,z73,z6,z100]),(0,[z365,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z366])]],
   [[(0,[z245,z2,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z367]),(0,[z263,z9,z1,z3,z4,z5,z6]),(0,[z1,z119,z2,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z6,z307])],[(0,[z9,z2,z3,z38,z4,z5,z6]),(0,[z85,z1,z2,z4,z104,z5,z6])],[(0,[z9,z1,z19,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z368,z5,z6]),(0,[z1,z2,z3,z104,z5,z58,z6]),(0,[z1,z2,z3,z4,z216,z6,z97])],[(0,[z369,z2,z11,z3,z4,z5,z6]),(0,[z1,z370,z2,z3,z4,z5,z6])],[(0,[z371,z1,z2,z3,z4,z5,z6]),(0,[z43,z1,z2,z38,z4,z5,z6]),(1,[z1,z2,z3,z345,z4,z5]),(0,[z41,z9,z1,z3,z4,z5,z6]),(0,[z1,z2,z372,z3,z4,z5,z6]),(0,[z22,z1,z3,z4,z5,z6,z110])],[(0,[z1,z2,z3,z36,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z373])],[(0,[z197,z1,z2,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z16,z5,z6])],[(0,[z374,z1,z2,z3,z4,z5,z6])],[(0,[z375,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z376,z6]),(0,[z90,z1,z3,z59,z4,z5,z6]),(0,[z29,z1,z2,z3,z4,z5,z6]),(0,[z9,z1,z2,z3,z91,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z377])],[(0,[z1,z2,z3,z4,z378,z5,z6]),(0,[z9,z1,z95,z3,z4,z5,z6]),(1,[z1,z119,z3,z59,z5,z6]),(0,[z1,z2,z3,z4,z5,z379,z6]),(1,[z380,z2,z3,z4,z5,z6]),(0,[z381,z1,z2,z3,z4,z5,z6])],[(0,[z158,z1,z3,z4,z5,z23,z6])],[(0,[z7,z2,z3,z4,z132,z5,z6]),(0,[z9,z1,z3,z67,z4,z5,z6])],[(0,[z43,z2,z382,z3,z4,z5,z6]),(0,[z383,z1,z2,z3,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z384,z6]),(0,[z49,z1,z2,z3,z4,z5,z6])],[(1,[z1,z280,z3,z4,z5,z6])],[(0,[z264,z2,z3,z38,z4,z5,z6]),(1,[z1,z3,z385,z4,z5,z6]),(0,[z1,z3,z59,z4,z132,z5,z6]),(0,[z1,z2,z3,z4,z109,z5,z6]),(0,[z1,z119,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z386])]],
   [[(0,[z1,z2,z3,z387,z4,z5,z6]),(0,[z9,z28,z1,z3,z4,z5,z6]),(1,[z37,z1,z45,z4,z5,z6]),(0,[z1,z2,z3,z14,z4,z5,z6]),(0,[z388,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z389,z6]),(0,[z2,z3,z38,z4,z5,z6,z18]),(0,[z278,z1,z2,z3,z4,z5,z6]),(0,[z165,z2,z3,z67,z4,z5,z6]),(0,[z1,z3,z45,z4,z69,z5,z6]),(0,[z390,z1,z2,z3,z4,z5,z6])],[(1,[z43,z30,z3,z4,z5,z6]),(0,[z1,z3,z45,z4,z5,z391,z6]),(1,[z392,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z393,z5,z6]),(0,[z1,z2,z3,z4,z5,z27,z6])],[(0,[z1,z394,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z5,z6,z395]),(0,[z90,z1,z2,z38,z4,z5,z6]),(0,[z7,z2,z3,z38,z4,z5,z6]),(0,[z1,z30,z3,z91,z4,z5,z6]),(0,[z41,z1,z3,z59,z4,z5,z6]),(1,[z1,z3,z4,z103,z5,z6])],[(0,[z1,z2,z3,z396,z4,z5,z6]),(0,[z1,z2,z3,z4,z397,z5,z6])],[(0,[z290,z1,z3,z45,z4,z5,z6])],[(0,[z398,z43,z2,z3,z4,z5,z6])],[(0,[z9,z63,z1,z3,z4,z5,z6]),(0,[z1,z3,z45,z4,z5,z159,z6]),(1,[z1,z2,z3,z399,z5,z6])],[(0,[z19,z2,z3,z38,z4,z5,z6]),(0,[z400,z43,z2,z3,z4,z5,z6]),(0,[z401,z1,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z402])],[(0,[z1,z2,z3,z403,z4,z5,z6]),(0,[z49,z1,z3,z59,z4,z5,z6])],[(0,[z43,z2,z3,z4,z69,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z151])],[(0,[z1,z2,z3,z4,z404,z5,z6]),(1,[z1,z2,z3,z4,z379,z6]),(0,[z49,z1,z2,z3,z4,z58,z6]),(0,[z405,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z406,z4,z5,z6]),(1,[z9,z3,z38,z4,z5,z6]),(0,[z2,z3,z4,z71,z5,z8,z6]),(0,[z1,z2,z3,z4,z5,z6,z407]),(0,[z408,z2,z3,z4,z5,z6,z18])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z409]),(0,[z1,z30,z3,z4,z176,z5,z6]),(0,[z158,z22,z1,z3,z4,z5,z6])],[(0,[z63,z1,z3,z4,z176,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z410]),(0,[z1,z2,z3,z4,z5,z411,z6]),(0,[z1,z2,z412,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z413]),(0,[z1,z2,z3,z4,z414,z5,z6]),(0,[z68,z1,z2,z3,z4,z5,z216])],[(0,[z1,z3,z59,z4,z71,z5,z6]),(0,[z1,z3,z45,z4,z415,z5,z6])],[(0,[z1,z3,z59,z4,z5,z73,z6]),(0,[z1,z2,z3,z4,z5,z92,z73]),(1,[z1,z131,z3,z4,z5,z6])],[(0,[z1,z2,z3,z416,z4,z5,z6]),(0,[z165,z1,z30,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z109,z5,z6])],[(0,[z114,z1,z2,z3,z4,z5,z6]),(0,[z1,z227,z3,z59,z4,z5,z6])],[(0,[z1,z30,z3,z4,z5,z77,z6]),(0,[z417,z1,z2,z3,z4,z5,z6])],[(0,[z165,z43,z2,z3,z4,z5,z6]),(0,[z418,z1,z2,z3,z4,z5,z6]),(0,[z9,z1,z119,z3,z4,z5,z6]),(0,[z419,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z420,z6]),(0,[z1,z421,z2,z3,z4,z5,z6])],[(1,[z1,z229,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z422,z5,z6]),(0,[z1,z30,z3,z4,z5,z216,z6]),(0,[z1,z2,z3,z4,z5,z423,z6])],[(0,[z1,z2,z3,z4,z424,z5,z6]),(0,[z158,z1,z30,z3,z4,z5,z6]),(0,[z1,z264,z3,z4,z5,z23,z6])],[(0,[z425,z1,z30,z3,z4,z5,z6]),(0,[z1,z3,z14,z80,z4,z5,z6])],[(0,[z22,z1,z3,z4,z176,z5,z6])],[(0,[z158,z43,z2,z3,z4,z5,z6]),(1,[z1,z326,z3,z4,z5,z6]),(0,[z426,z1,z2,z3,z4,z5,z6])],[(0,[z2,z3,z38,z91,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z427,z6])]],
   [[(0,[z1,z2,z3,z4,z428,z5,z6]),(0,[z1,z2,z3,z166,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z429])],[(0,[z1,z2,z3,z4,z71,z5,z235]),(0,[z1,z2,z3,z4,z5,z430,z6])],[(0,[z335,z1,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z431,z6]),(0,[z1,z2,z3,z91,z80,z5,z6])],[(0,[z432,z1,z2,z3,z4,z5,z6]),(0,[z369,z1,z2,z3,z4,z5,z6])],[(1,[z433,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z434,z6])],[(0,[z150,z1,z2,z3,z4,z5,z6]),(0,[z435,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z436,z4,z5,z6]),(0,[z122,z1,z2,z4,z5,z6,z100])],[(0,[z1,z2,z3,z437,z4,z5,z6]),(0,[z9,z1,z2,z3,z5,z6,z18]),(0,[z1,z438,z2,z3,z4,z5,z6])],[(0,[z290,z2,z3,z38,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z439,z6]),(1,[z85,z1,z2,z104,z5,z6])],[(0,[z1,z2,z3,z4,z71,z5,z6]),(0,[z117,z1,z2,z3,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z6,z110]),(0,[z440,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z6,z97]),(0,[z1,z2,z3,z4,z441,z5,z6]),(0,[z1,z2,z3,z35,z5,z58,z6]),(0,[z1,z442,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z443,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z6,z100]),(0,[z1,z2,z3,z4,z5,z73,z6]),(0,[z49,z1,z2,z3,z35,z4,z6])],[(0,[z1,z2,z3,z4,z444,z5,z6])],[],[],[(0,[z43,z2,z3,z4,z5,z6,z196]),(1,[z1,z3,z4,z5,z445,z6]),(0,[z446,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z38,z4,z5,z77,z6]),(0,[z1,z2,z136,z3,z4,z5,z6]),(0,[z447,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z166,z4,z58,z6])],[(0,[z448,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z449,z4,z5,z6]),(0,[z2,z3,z38,z4,z5,z216,z6]),(0,[z450,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z451]),(0,[z1,z2,z3,z67,z4,z5,z276])],[],[(0,[z452,z43,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z143,z5,z6]),(0,[z9,z1,z3,z166,z4,z5,z6])],[(0,[z43,z2,z66,z3,z4,z5,z6]),(0,[z149,z1,z30,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z453,z6])],[(0,[z380,z2,z3,z4,z5,z58,z6]),(0,[z454,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z455])],[(0,[z188,z1,z2,z3,z4,z5,z6]),(0,[z149,z43,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z176,z5,z159,z6]),(0,[z1,z2,z456,z3,z4,z5,z6])],[(0,[z1,z264,z30,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z457,z6])],[(0,[z1,z2,z3,z4,z5,z458,z6]),(0,[z1,z2,z3,z4,z69,z77,z6]),(0,[z1,z2,z3,z4,z5,z6,z459])],[(0,[z1,z2,z3,z4,z5,z216,z100])],[(0,[z1,z2,z3,z460,z4,z5,z6])],[(0,[z98,z1,z3,z59,z4,z5,z6]),(0,[z1,z461,z2,z3,z4,z5,z6]),(0,[z149,z1,z359,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z92,z6])]],
   [[(0,[z9,z1,z3,z4,z71,z5,z6]),(0,[z1,z2,z3,z4,z462,z5,z6]),(0,[z408,z1,z2,z3,z4,z5,z6]),(0,[z1,z463,z2,z3,z4,z5,z6])],[(0,[z1,z464,z2,z3,z4,z5,z6]),(1,[z24,z2,z3,z4,z5,z196]),(0,[z9,z1,z3,z4,z5,z73,z6]),(0,[z1,z2,z3,z4,z5,z6,z97])],[(0,[z19,z2,z168,z3,z4,z5,z6])],[(0,[z2,z3,z38,z4,z5,z6,z110]),(0,[z335,z2,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z465,z4,z5,z6]),(0,[z1,z2,z466,z3,z4,z5,z6]),(0,[z467,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z402,z97])],[(0,[z68,z1,z2,z3,z4,z6,z97])],[(1,[z432,z2,z3,z4,z5,z6])],[(0,[z1,z66,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z242]),(0,[z1,z2,z468,z3,z4,z5,z6])],[(1,[z469,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z470])],[(0,[z471,z43,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z472,z6])],[(0,[z1,z2,z3,z473,z4,z5,z6]),(0,[z398,z1,z30,z3,z4,z5,z6]),(0,[z1,z2,z3,z474,z4,z5,z6]),(1,[z252,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z307]),(0,[z1,z2,z3,z399,z4,z5,z6]),(0,[z1,z475,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z69,z12,z6]),(0,[z1,z476,z227,z3,z4,z5,z6])],[(0,[z2,z3,z38,z4,z12,z5,z6]),(1,[z43,z3,z45,z4,z5,z6]),(0,[z9,z1,z3,z4,z5,z477,z6]),(0,[z478,z1,z2,z3,z4,z5,z6])],[(1,[z3,z38,z59,z4,z5,z6]),(0,[z43,z2,z3,z4,z5,z60,z6])],[(0,[z9,z98,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z479,z6]),(0,[z480,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z481]),(0,[z1,z30,z3,z482,z4,z5,z6]),(0,[z1,z30,z3,z4,z69,z5,z6])],[(1,[z2,z3,z4,z5,z74,z6])]],
   [[(0,[z2,z168,z3,z4,z5,z8,z6]),(0,[z1,z2,z3,z207,z4,z5,z6]),(0,[z1,z2,z3,z53,z4,z5,z6]),(0,[z1,z2,z3,z483,z4,z5,z6])],[(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z484,z5,z6]),(0,[z41,z469,z2,z3,z4,z5,z6]),(0,[z485,z1,z2,z3,z4,z5,z6])],[(0,[z28,z1,z2,z3,z4,z5,z196]),(1,[z1,z2,z227,z4,z5,z73])],[(0,[z85,z9,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z486,z6]),(0,[z264,z2,z134,z3,z4,z5,z6]),(0,[z1,z2,z3,z487,z4,z5,z6])],[(0,[z346,z1,z2,z3,z4,z5,z6])],[(0,[z488,z1,z2,z3,z4,z5,z6]),(0,[z24,z1,z2,z3,z4,z5,z196]),(0,[z489,z1,z2,z3,z4,z5,z6])],[(0,[z85,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z92,z6])],[(0,[z9,z24,z1,z3,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z159,z6]),(0,[z9,z1,z3,z4,z5,z6,z97])],[(0,[z1,z2,z490,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z491,z6])],[(0,[z492,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z132,z5,z6]),(0,[z1,z30,z493,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z494,z6])],[(0,[z495,z1,z2,z3,z4,z5,z6]),(1,[z94,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z496,z6]),(0,[z17,z1,z2,z3,z4,z5,z92])],[(0,[z24,z2,z3,z4,z5,z6,z196])],[(1,[z165,z2,z3,z4,z60,z6]),(0,[z170,z1,z2,z3,z4,z5,z6]),(1,[z369,z2,z3,z4,z5,z6])],[(0,[z2,z3,z345,z38,z4,z5,z6]),(0,[z43,z2,z3,z141,z4,z5,z6]),(0,[z1,z2,z3,z497,z4,z5,z6])],[(0,[z165,z1,z3,z45,z4,z5,z6]),(1,[z9,z1,z3,z59,z5,z6]),(0,[z1,z2,z3,z4,z5,z498,z6]),(0,[z1,z2,z3,z4,z5,z366,z6])],[(1,[z1,z464,z3,z4,z5,z6]),(0,[z43,z2,z147,z3,z4,z5,z6]),(0,[z22,z1,z2,z3,z4,z5,z92]),(0,[z1,z2,z3,z4,z499,z5,z6]),(0,[z1,z2,z3,z91,z5,z92,z6])]],
   [[(0,[z7,z1,z3,z59,z4,z5,z6]),(0,[z41,z1,z2,z11,z4,z5,z6])],[(0,[z98,z1,z168,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z44,z5,z6]),(0,[z1,z3,z3,z45,z4,z5,z6]),(0,[z1,z3,z59,z59,z4,z5,z6])],[(0,[z1,z19,z2,z3,z4,z5,z6]),(0,[z1,z2,z500,z3,z4,z5,z6]),(0,[z501,z1,z3,z45,z4,z5,z6]),(0,[z432,z2,z3,z4,z5,z159,z6]),(0,[z469,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z502,z5,z6]),(0,[z1,z2,z3,z38,z4,z5,z6]),(0,[z1,z503,z2,z3,z4,z5,z6]),(1,[z68,z1,z2,z3,z4,z97])],[(0,[z504,z1,z2,z3,z4,z5,z6]),(0,[z158,z1,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z505,z4,z5,z6]),(0,[z1,z2,z3,z91,z4,z5,z18])],[(0,[z85,z1,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z506,z6]),(0,[z1,z2,z3,z166,z4,z5,z366]),(1,[z507,z1,z3,z4,z5,z6])],[(0,[z149,z2,z3,z67,z4,z5,z6]),(0,[z1,z3,z45,z4,z5,z6,z196]),(0,[z1,z3,z59,z4,z5,z6,z18]),(0,[z1,z223,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z508,z4,z5,z6])],[(1,[z1,z3,z482,z4,z5,z6]),(0,[z1,z30,z2,z66,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z509,z6])],[(0,[z158,z1,z2,z3,z4,z159,z6]),(1,[z1,z3,z510,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z3,z511,z45,z4,z5,z6]),(0,[z1,z2,z3,z512,z4,z5,z6]),(1,[z125,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z513,z6])],[(0,[z1,z2,z3,z4,z5,z70,z6]),(0,[z1,z2,z3,z5,z92,z6,z18])],[(0,[z2,z3,z38,z4,z176,z5,z6]),(0,[z514,z1,z2,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z5,z92,z6]),(0,[z1,z2,z3,z4,z5,z6,z515])],[(0,[z1,z147,z3,z59,z4,z5,z6]),(0,[z516,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z517]),(0,[z1,z2,z3,z4,z5,z216,z73])],[(0,[z1,z2,z3,z4,z218,z5,z6])],[(0,[z149,z1,z2,z3,z132,z5,z6]),(0,[z9,z1,z3,z4,z132,z5,z6]),(0,[z518,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z38,z4,z5,z159,z6]),(0,[z2,z3,z38,z4,z5,z519,z6]),(0,[z1,z3,z45,z4,z5,z23,z6])],[(0,[z1,z19,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z520,z6])],[(0,[z1,z2,z521,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z522]),(0,[z523,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z524,z3,z4,z5,z6]),(0,[z1,z2,z3,z345,z4,z5,z6]),(0,[z111,z43,z2,z3,z4,z5,z6]),(0,[z290,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z525,z5,z6])],[],[(0,[z115,z43,z2,z3,z4,z5,z6]),(1,[z343,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z526,z4,z5,z6])],[(0,[z527,z2,z3,z38,z4,z5,z6]),(0,[z1,z3,z45,z4,z5,z6,z226]),(0,[z1,z3,z45,z35,z4,z5,z6]),(0,[z1,z20,z3,z4,z176,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z347])],[(0,[z43,z30,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z528,z4,z5,z6]),(0,[z1,z30,z66,z3,z4,z5,z6]),(0,[z529,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z477,z6]),(0,[z530,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z216,z18])],[(0,[z9,z1,z3,z38,z4,z5,z6]),(1,[z365,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z6,z531])],[(0,[z28,z1,z2,z3,z4,z5,z216])],[(0,[z1,z2,z3,z4,z5,z532,z6])],[(0,[z43,z2,z3,z4,z5,z23,z6]),(0,[z533,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z8,z6,z196]),(0,[z9,z9,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z534,z5,z6])],[(0,[z165,z19,z2,z3,z4,z5,z6]),(0,[z535,z1,z2,z3,z4,z5,z6]),(0,[z24,z1,z2,z3,z4,z5,z216]),(0,[z1,z2,z11,z3,z4,z5,z6]),(0,[z536,z1,z2,z3,z4,z5,z6]),(0,[z537,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z18])],[(0,[z165,z2,z3,z38,z4,z5,z6]),(0,[z245,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z538,z4,z5,z6]),(0,[z1,z438,z11,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z539,z6])],[(0,[z1,z168,z3,z59,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z92]),(0,[z9,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z292,z4,z5,z6])]],
   [[(0,[z149,z1,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z540,z5,z6]),(0,[z541,z1,z2,z3,z4,z5,z6])],[(0,[z542,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z80,z5,z58,z6])],[(0,[z43,z2,z3,z35,z4,z5,z6]),(0,[z24,z1,z2,z3,z4,z5,z92]),(0,[z1,z3,z45,z4,z5,z58,z6]),(0,[z313,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z543,z5,z6]),(0,[z1,z544,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z69,z216,z6])],[(0,[z1,z3,z45,z4,z5,z60,z6]),(1,[z1,z2,z3,z4,z5,z314])],[(0,[z158,z2,z3,z38,z4,z5,z6]),(0,[z43,z2,z3,z4,z5,z8,z6]),(0,[z1,z264,z3,z45,z4,z5,z6]),(0,[z1,z3,z72,z59,z4,z5,z6]),(0,[z1,z3,z59,z91,z4,z5,z6]),(1,[z1,z3,z25,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z167])],[(0,[z290,z1,z2,z3,z4,z60,z6]),(0,[z37,z94,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z545,z5,z6]),(0,[z1,z2,z294,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z100])],[(0,[z43,z2,z3,z4,z104,z5,z6]),(0,[z1,z2,z546,z3,z4,z5,z6]),(0,[z1,z2,z3,z547,z4,z5,z6])],[(1,[z30,z3,z38,z4,z5,z6]),(0,[z529,z1,z3,z59,z4,z5,z6])],[(0,[z1,z2,z3,z548,z4,z5,z6]),(0,[z1,z2,z3,z327,z4,z5,z6]),(0,[z9,z401,z1,z3,z4,z5,z6]),(0,[z1,z2,z139,z3,z4,z5,z6]),(0,[z1,z2,z3,z178,z4,z5,z6])],[(0,[z440,z2,z66,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z549,z5,z6]),(0,[z1,z135,z2,z3,z4,z5,z6]),(0,[z1,z3,z45,z80,z4,z5,z6]),(0,[z1,z2,z3,z96,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z42]),(0,[z1,z81,z3,z35,z4,z5,z6])],[(0,[z20,z2,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z550,z6])],[(0,[z1,z2,z551,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z552]),(0,[z1,z2,z3,z553,z4,z5,z6])],[(0,[z2,z3,z38,z4,z554,z5,z6]),(0,[z1,z2,z555,z3,z4,z5,z6]),(0,[z433,z1,z3,z4,z132,z5,z6]),(0,[z556,z1,z2,z3,z4,z5,z6]),(0,[z122,z1,z2,z3,z4,z539,z6])],[(0,[z335,z1,z2,z3,z4,z5,z6]),(0,[z43,z2,z3,z4,z5,z58,z6]),(0,[z9,z1,z3,z59,z4,z5,z6]),(0,[z122,z1,z2,z3,z289,z5,z6]),(0,[z49,z1,z2,z3,z35,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z557]),(0,[z1,z2,z3,z4,z558,z5,z6])]],
   [[(0,[z1,z2,z559,z3,z4,z5,z6]),(0,[z560,z1,z2,z3,z4,z5,z6])],[(0,[z7,z9,z1,z3,z4,z5,z6])],[(0,[z561,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z384,z6]),(1,[z1,z2,z3,z4,z539,z6])],[(0,[z1,z2,z3,z4,z5,z562,z6]),(0,[z1,z3,z38,z45,z4,z5,z6]),(0,[z9,z1,z11,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z5,z6,z18]),(0,[z1,z2,z3,z4,z5,z563,z6]),(1,[z1,z2,z3,z289,z5,z6])],[],[(0,[z43,z2,z227,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z77,z6])],[(0,[z43,z2,z3,z80,z4,z5,z6]),(0,[z1,z3,z45,z45,z4,z5,z6])],[(0,[z7,z24,z2,z3,z4,z5,z6]),(0,[z85,z222,z2,z3,z4,z5,z6])],[(0,[z2,z3,z250,z38,z4,z5,z6]),(0,[z165,z1,z2,z3,z4,z60,z6]),(0,[z1,z3,z59,z4,z5,z216,z6])],[],[(0,[z1,z2,z168,z3,z4,z5,z6]),(0,[z1,z2,z3,z564,z4,z5,z6]),(0,[z565,z1,z2,z3,z4,z5,z6]),(0,[z2,z227,z3,z53,z4,z5,z6]),(1,[z49,z1,z2,z3,z35,z6])],[(0,[z63,z1,z30,z3,z4,z5,z6]),(0,[z43,z20,z2,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z5,z6,z100]),(0,[z9,z49,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z91,z4,z5,z6])],[],[(0,[z158,z63,z1,z3,z4,z5,z6]),(0,[z158,z98,z1,z3,z4,z5,z6]),(0,[z1,z566,z2,z3,z4,z5,z6]),(0,[z433,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z567,z3,z4,z5,z6])],[(0,[z63,z43,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z568,z4,z5,z6]),(0,[z249,z9,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z569,z6]),(0,[z90,z1,z464,z3,z4,z5,z6]),(0,[z41,z1,z2,z4,z5,z77,z6])]],
   [[(0,[z149,z2,z3,z38,z4,z5,z6]),(0,[z1,z30,z147,z3,z4,z5,z6]),(0,[z1,z3,z443,z59,z4,z5,z6]),(0,[z1,z95,z3,z59,z4,z5,z6]),(0,[z1,z3,z4,z176,z5,z23,z6])],[(0,[z249,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z304,z5,z6]),(0,[z570,z1,z2,z3,z4,z5,z6])],[(0,[z43,z2,z3,z45,z4,z5,z6]),(0,[z68,z1,z30,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z571,z6]),(0,[z1,z2,z3,z4,z572,z5,z6])],[],[(0,[z573,z1,z2,z3,z4,z5,z6])],[(0,[z17,z43,z2,z3,z4,z5,z6]),(0,[z68,z43,z2,z3,z4,z5,z6]),(0,[z1,z574,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z23,z6,z110])],[(0,[z1,z11,z3,z59,z4,z5,z6])],[(0,[z22,z1,z30,z3,z4,z5,z6]),(0,[z1,z2,z3,z575,z4,z5,z6]),(0,[z1,z119,z2,z3,z59,z5,z6])],[(0,[z1,z3,z59,z4,z5,z6,z110])],[(0,[z1,z2,z3,z4,z576,z5,z6]),(0,[z1,z2,z3,z4,z577,z5,z6]),(0,[z578,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z579])],[(0,[z2,z3,z38,z4,z69,z5,z6]),(0,[z22,z43,z2,z3,z4,z5,z6]),(0,[z343,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z445,z6]),(0,[z37,z1,z2,z66,z4,z5,z6])],[(0,[z580,z1,z2,z3,z4,z5,z6]),(1,[z90,z2,z38,z4,z5,z6]),(0,[z514,z9,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z77,z6]),(0,[z1,z581,z2,z3,z4,z5,z6])],[(0,[z2,z227,z3,z38,z4,z5,z6]),(0,[z28,z2,z3,z4,z5,z8,z6]),(1,[z1,z30,z45,z4,z5,z6]),(0,[z1,z3,z45,z4,z318,z5,z6]),(0,[z1,z11,z3,z292,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z582,z5,z6]),(0,[z1,z3,z59,z4,z5,z583,z6]),(0,[z1,z2,z3,z59,z4,z5,z120]),(0,[z1,z20,z2,z3,z4,z176,z6]),(0,[z584,z1,z2,z3,z4,z5,z6]),(0,[z585,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z6,z129]),(0,[z1,z2,z95,z3,z104,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z586])],[(0,[z98,z1,z3,z4,z176,z5,z6]),(0,[z2,z3,z38,z4,z126,z5,z6])]],
   [[(0,[z9,z1,z168,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z12,z5,z6])],[(0,[z122,z43,z2,z3,z4,z5,z6]),(1,[z1,z133,z3,z4,z5,z6]),(0,[z1,z587,z2,z3,z4,z5,z6]),(0,[z9,z1,z3,z91,z4,z5,z6]),(0,[z1,z2,z3,z4,z588,z5,z6]),(0,[z1,z2,z3,z35,z4,z77,z6])],[(1,[z41,z1,z2,z4,z77,z6])],[(0,[z1,z147,z3,z385,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z6,z196]),(1,[z22,z1,z3,z4,z5,z110]),(0,[z1,z2,z3,z4,z5,z6,z589]),(0,[z1,z2,z590,z3,z4,z5,z6]),(0,[z507,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z69,z5,z97])],[],[(0,[z1,z2,z3,z591,z4,z5,z6])],[(1,[z43,z2,z3,z4,z5,z6])],[(0,[z1,z2,z134,z3,z4,z5,z6]),(1,[z1,z142,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z592,z5,z6]),(0,[z1,z264,z2,z3,z4,z5,z18]),(1,[z57,z1,z3,z4,z5,z6])],[(0,[z1,z2,z593,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z6,z153])],[(0,[z85,z1,z2,z3,z4,z379,z6]),(0,[z1,z2,z3,z4,z594,z5,z6])],[(1,[z1,z359,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z595,z6]),(0,[z1,z3,z45,z4,z5,z8,z6]),(0,[z115,z1,z3,z45,z4,z5,z6]),(1,[z1,z2,z3,z351,z5,z6]),(0,[z1,z2,z3,z35,z166,z4,z6])],[(0,[z596,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z74,z159,z6]),(0,[z1,z2,z3,z4,z5,z6,z597])],[(0,[z43,z2,z3,z4,z5,z323,z6]),(0,[z1,z3,z45,z4,z104,z5,z6]),(0,[z1,z30,z3,z4,z5,z23,z6]),(0,[z392,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z598])],[(0,[z1,z2,z3,z385,z4,z5,z6]),(0,[z1,z3,z59,z4,z4,z5,z6])],[(0,[z43,z2,z3,z4,z328,z5,z6]),(0,[z1,z2,z3,z4,z5,z599,z6]),(1,[z296,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z35,z4,z12,z6]),(0,[z600,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z601,z6]),(1,[z408,z2,z3,z4,z5,z6])],[(0,[z2,z147,z3,z38,z4,z5,z6]),(0,[z527,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z602,z4,z5,z6]),(0,[z1,z257,z2,z3,z4,z5,z6]),(0,[z41,z1,z142,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z603])],[(0,[z63,z1,z19,z3,z4,z5,z6]),(0,[z604,z1,z2,z3,z4,z5,z6]),(0,[z165,z63,z2,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z5,z77,z6])],[(0,[z1,z2,z605,z3,z4,z5,z6]),(0,[z1,z30,z3,z35,z4,z5,z6]),(0,[z2,z66,z3,z474,z4,z5,z6]),(1,[z1,z130,z3,z4,z5,z6]),(0,[z606,z1,z2,z3,z4,z5,z6])],[],[(0,[z290,z1,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z4,z103,z5,z6]),(0,[z1,z607,z2,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z351,z5,z6]),(0,[z1,z227,z3,z510,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z608,z6]),(0,[z1,z609,z2,z3,z4,z5,z6])],[(0,[z49,z1,z2,z3,z104,z5,z6]),(0,[z1,z2,z3,z4,z12,z5,z6])],[(0,[z1,z280,z147,z3,z4,z5,z6]),(0,[z1,z3,z101,z45,z4,z5,z6]),(0,[z1,z2,z3,z104,z5,z6,z18]),(0,[z610,z1,z2,z3,z4,z5,z6])],[(0,[z165,z1,z2,z3,z4,z5,z6]),(0,[z41,z296,z2,z3,z4,z5,z6])],[(0,[z28,z43,z2,z3,z4,z5,z6]),(0,[z611,z1,z2,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z77,z6])],[(0,[z63,z2,z3,z4,z71,z5,z6]),(0,[z43,z2,z95,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z612]),(0,[z1,z2,z3,z4,z5,z613,z6])],[(0,[z2,z3,z38,z4,z5,z6,z196])],[(0,[z614,z1,z2,z3,z4,z5,z6]),(0,[z43,z2,z3,z67,z4,z5,z6]),(0,[z24,z43,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z615,z6]),(0,[z501,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z616,z5,z6])],[(0,[z617,z1,z2,z3,z4,z5,z6]),(0,[z335,z9,z1,z3,z4,z5,z6]),(0,[z507,z1,z3,z4,z5,z6,z97])],[(0,[z1,z30,z3,z4,z5,z58,z6]),(0,[z618,z1,z2,z3,z4,z5,z6]),(0,[z158,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z30,z3,z4,z5,z60,z6]),(0,[z425,z1,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z322,z6])],[(0,[z290,z1,z2,z3,z4,z71,z6]),(0,[z1,z2,z3,z4,z5,z6,z619]),(1,[z9,z1,z3,z109,z5,z6]),(0,[z1,z3,z59,z4,z176,z5,z6]),(0,[z1,z2,z3,z4,z620,z5,z6]),(1,[z537,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z155,z6]),(0,[z1,z2,z3,z4,z5,z621,z6]),(0,[z122,z1,z2,z227,z4,z5,z6])],[(0,[z2,z168,z3,z38,z4,z5,z6]),(0,[z1,z2,z622,z3,z4,z5,z6])],[(1,[z290,z2,z3,z4,z71,z6]),(0,[z537,z1,z3,z4,z5,z6,z18])],[(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z9,z1,z3,z4,z5,z6,z110]),(0,[z1,z3,z59,z4,z5,z159,z6]),(0,[z1,z2,z623,z3,z4,z5,z6])],[(0,[z2,z3,z38,z4,z5,z23,z6]),(0,[z1,z30,z227,z3,z4,z5,z6]),(0,[z1,z264,z2,z3,z4,z5,z23])],[(0,[z43,z119,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z624]),(0,[z1,z198,z30,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z625])],[(0,[z43,z2,z3,z4,z5,z6,z451]),(0,[z165,z1,z3,z59,z4,z5,z6]),(1,[z28,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z12,z58,z6])],[(0,[z1,z2,z229,z3,z4,z5,z6])],[(0,[z1,z3,z45,z4,z109,z5,z6]),(0,[z9,z1,z230,z3,z4,z5,z6])],[(0,[z1,z3,z45,z14,z4,z5,z6])],[(0,[z98,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z38,z35,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z626])],[(0,[z2,z66,z3,z38,z4,z5,z6]),(0,[z1,z30,z30,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z12,z5,z6])],[(0,[z627,z1,z2,z3,z4,z5,z6]),(1,[z440,z2,z3,z4,z5,z6])],[]],
   [[(0,[z1,z2,z3,z4,z5,z235,z6]),(0,[z335,z1,z3,z59,z4,z5,z6])],[(0,[z37,z43,z2,z3,z4,z5,z6]),(0,[z43,z1,z30,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z628,z5,z6])],[(0,[z1,z3,z4,z5,z445,z60,z6]),(1,[z1,z3,z4,z192,z5,z6]),(0,[z1,z2,z3,z4,z629,z5,z6])],[(0,[z1,z30,z3,z45,z4,z5,z6]),(0,[z1,z2,z630,z3,z4,z5,z6]),(0,[z631,z1,z2,z3,z4,z5,z6]),(0,[z68,z1,z2,z3,z4,z5,z97])],[(0,[z63,z1,z3,z45,z4,z5,z6]),(0,[z43,z43,z2,z3,z4,z5,z6]),(0,[z165,z1,z2,z3,z4,z71,z6]),(0,[z1,z3,z45,z4,z5,z298,z6]),(0,[z1,z2,z3,z4,z632,z5,z6]),(0,[z1,z2,z3,z4,z633,z5,z6])],[(0,[z17,z1,z30,z3,z4,z5,z6]),(0,[z1,z3,z14,z59,z4,z5,z6])],[(0,[z43,z2,z3,z4,z109,z5,z6]),(0,[z1,z2,z3,z634,z4,z5,z6]),(0,[z2,z3,z4,z5,z322,z58,z6])],[],[(0,[z635,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z176,z5,z6])],[(0,[z2,z3,z38,z4,z5,z60,z6]),(0,[z636,z1,z2,z3,z4,z5,z6])],[(0,[z1,z3,z45,z64,z4,z5,z6]),(0,[z122,z370,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z336,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z637,z6]),(0,[z1,z2,z3,z4,z638,z5,z6])],[(1,[z1,z248,z3,z4,z5,z6]),(0,[z1,z2,z3,z256,z4,z5,z6]),(0,[z43,z2,z3,z3,z4,z5,z6]),(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z17,z1,z3,z45,z4,z5,z6]),(0,[z68,z1,z3,z45,z4,z5,z6]),(0,[z9,z1,z3,z4,z4,z5,z6]),(0,[z1,z3,z512,z59,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z519,z6]),(0,[z1,z2,z3,z4,z5,z159,z6])],[(0,[z1,z2,z3,z4,z639,z5,z6])],[(0,[z1,z2,z493,z3,z4,z5,z6]),(1,[z1,z264,z3,z4,z5,z23])],[(0,[z1,z2,z640,z3,z4,z5,z6]),(0,[z1,z2,z3,z641,z4,z5,z6]),(0,[z1,z264,z2,z3,z4,z5,z6]),(1,[z370,z2,z3,z4,z5,z6]),(0,[z365,z2,z227,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z642,z6])]],
   [[(0,[z22,z1,z3,z45,z4,z5,z6])],[(0,[z643,z1,z2,z3,z4,z5,z6]),(0,[z245,z1,z2,z3,z38,z4,z5]),(0,[z122,z1,z30,z3,z4,z5,z6]),(0,[z1,z2,z644,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z86])],[(0,[z1,z2,z3,z4,z5,z6,z645]),(0,[z1,z2,z3,z166,z5,z58,z6]),(0,[z1,z2,z3,z4,z5,z216,z6])],[(0,[z1,z168,z3,z4,z5,z159,z6]),(0,[z90,z1,z30,z3,z4,z5,z6]),(0,[z9,z1,z2,z3,z59,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z646])],[(0,[z2,z95,z3,z38,z4,z5,z6]),(1,[z1,z3,z270,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z647]),(0,[z1,z2,z3,z4,z5,z6,z648])],[(0,[z1,z2,z3,z4,z649,z5,z6]),(0,[z1,z123,z2,z3,z4,z5,z6])],[(0,[z90,z43,z2,z3,z4,z5,z6]),(0,[z1,z2,z650,z3,z4,z5,z6]),(1,[z1,z30,z3,z4,z5,z6]),(0,[z1,z3,z634,z45,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z651])],[(0,[z1,z2,z3,z4,z652,z5,z6]),(0,[z2,z3,z67,z4,z5,z8,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z122,z1,z3,z45,z4,z5,z6]),(0,[z1,z2,z653,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z77,z6,z97])],[(0,[z654,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z655,z6]),(0,[z24,z2,z3,z67,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z242]),(0,[z1,z2,z3,z4,z656,z5,z6])],[(0,[z2,z11,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z657,z6]),(0,[z1,z264,z2,z3,z4,z5,z110])],[(1,[z1,z2,z3,z4,z5,z155]),(0,[z22,z1,z264,z3,z4,z5,z6]),(1,[z1,z2,z3,z166,z58,z6])],[(0,[z658,z1,z2,z3,z4,z5,z6]),(1,[z1,z3,z45,z4,z5,z6]),(0,[z659,z1,z2,z3,z4,z5,z6])],[(0,[z398,z1,z2,z3,z4,z5,z6]),(0,[z43,z2,z3,z4,z132,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z307]),(0,[z660,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z661])],[(0,[z1,z82,z30,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z176,z5,z6]),(0,[z1,z264,z3,z59,z4,z5,z6]),(0,[z392,z264,z2,z3,z4,z5,z6])],[(0,[z400,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z662,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z663]),(0,[z1,z2,z3,z4,z5,z6,z664]),(0,[z1,z2,z3,z4,z5,z6,z665]),(0,[z1,z2,z666,z3,z4,z5,z6])]],
   [[(0,[z41,z1,z30,z3,z4,z5,z6]),(0,[z1,z20,z30,z3,z4,z5,z6]),(0,[z667,z1,z2,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z5,z651])],[(0,[z1,z277,z30,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z276]),(1,[z2,z3,z474,z4,z5,z6]),(0,[z9,z1,z3,z4,z5,z159,z6]),(0,[z1,z2,z3,z4,z5,z6,z110]),(0,[z668,z1,z2,z3,z4,z5,z6])],[(0,[z2,z3,z38,z4,z5,z6,z163]),(0,[z41,z43,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z71,z5,z314])],[(0,[z63,z2,z3,z38,z4,z5,z6]),(0,[z1,z3,z45,z67,z4,z5,z6])],[(0,[z1,z3,z45,z4,z71,z5,z6]),(0,[z1,z476,z2,z3,z4,z5,z6])],[(0,[z1,z3,z45,z4,z5,z73,z6]),(0,[z1,z2,z669,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z670,z6]),(0,[z43,z2,z3,z166,z4,z5,z6])],[(1,[z43,z3,z59,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z97]),(0,[z1,z30,z3,z4,z5,z8,z6]),(0,[z9,z1,z3,z4,z5,z216,z6]),(0,[z1,z2,z3,z4,z5,z583,z6])],[(0,[z1,z2,z3,z4,z554,z5,z6]),(0,[z49,z43,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z67,z5,z6]),(0,[z165,z9,z1,z3,z4,z5,z6])],[(0,[z28,z1,z30,z3,z4,z5,z6]),(0,[z1,z30,z3,z4,z104,z5,z6]),(0,[z1,z20,z2,z3,z4,z159,z6]),(0,[z1,z2,z3,z399,z5,z23,z6])],[(0,[z17,z2,z3,z38,z4,z5,z6]),(0,[z68,z2,z3,z38,z4,z5,z6]),(0,[z24,z1,z2,z3,z4,z5,z97]),(0,[z9,z1,z3,z4,z649,z5,z6])],[(0,[z1,z30,z95,z3,z4,z5,z6]),(1,[z1,z3,z59,z4,z5,z307]),(0,[z2,z3,z4,z5,z6,z167,z18])],[(0,[z1,z3,z4,z143,z132,z5,z6]),(0,[z24,z1,z30,z3,z4,z5,z6])],[],[(0,[z165,z24,z2,z3,z4,z5,z6]),(0,[z158,z9,z1,z3,z4,z5,z6]),(0,[z667,z1,z3,z59,z4,z5,z6]),(0,[z1,z3,z59,z4,z69,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z402])]],
   [[(0,[z22,z2,z3,z38,z4,z5,z6]),(0,[z28,z1,z3,z45,z4,z5,z6])],[(0,[z22,z1,z19,z3,z4,z5,z6]),(0,[z43,z2,z3,z4,z71,z5,z6]),(1,[z1,z2,z3,z4,z287,z6])],[(0,[z43,z2,z3,z4,z5,z73,z6]),(0,[z1,z2,z3,z4,z5,z92,z216]),(0,[z1,z3,z4,z5,z6,z153,z97])],[(0,[z24,z1,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z651,z6]),(0,[z1,z2,z671,z3,z4,z5,z6]),(0,[z17,z1,z2,z3,z91,z5,z6])],[(0,[z1,z2,z3,z4,z672,z5,z6]),(0,[z1,z2,z3,z673,z4,z5,z6]),(0,[z1,z674,z2,z3,z4,z5,z6])],[(1,[z43,z2,z38,z4,z5,z6]),(0,[z99,z2,z3,z38,z4,z5,z6]),(1,[z249,z1,z3,z4,z5,z6]),(0,[z85,z125,z2,z3,z4,z5,z6]),(0,[z1,z2,z675,z3,z4,z5,z6])],[(1,[z98,z19,z3,z4,z5,z6]),(0,[z1,z2,z382,z3,z4,z5,z6])],[(0,[z122,z2,z3,z38,z4,z5,z6])],[(0,[z676,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z677,z3,z4,z5,z6]),(0,[z1,z2,z678,z3,z4,z5,z6])],[(0,[z679,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z680,z4,z5,z6]),(0,[z1,z30,z3,z80,z4,z5,z6]),(0,[z1,z119,z2,z3,z109,z5,z6])],[(1,[z9,z43,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z12,z6])],[(1,[z2,z3,z38,z4,z5,z6]),(0,[z9,z1,z20,z3,z4,z5,z6]),(0,[z611,z1,z3,z59,z4,z5,z6])],[(0,[z681,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z682,z6]),(0,[z1,z2,z683,z3,z4,z5,z6])],[(0,[z119,z2,z3,z38,z4,z5,z6]),(0,[z243,z1,z3,z4,z104,z5,z6])],[(0,[z2,z11,z3,z178,z4,z5,z6]),(0,[z17,z1,z2,z3,z4,z5,z18])]],
   [[(0,[z9,z290,z1,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z104,z5,z6]),(0,[z122,z1,z2,z3,z4,z5,z73])],[(0,[z2,z3,z38,z4,z5,z8,z6]),(0,[z1,z2,z3,z684,z4,z5,z6]),(0,[z1,z2,z3,z685,z4,z5,z6]),(0,[z37,z1,z30,z3,z4,z5,z6]),(1,[z9,z1,z3,z91,z5,z6]),(0,[z158,z1,z3,z59,z4,z5,z6])],[(0,[z1,z686,z2,z3,z4,z5,z6])],[(0,[z687,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z38,z4,z104,z5,z6]),(0,[z2,z3,z38,z4,z5,z233,z6])],[(0,[z22,z1,z2,z3,z4,z5,z18])],[(0,[z1,z2,z3,z4,z5,z688,z6]),(0,[z1,z2,z3,z689,z4,z5,z6])],[(0,[z1,z2,z3,z482,z4,z5,z6]),(1,[z1,z236,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z69,z5,z6])],[(0,[z37,z1,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z391,z6]),(0,[z1,z30,z3,z4,z109,z5,z6]),(0,[z690,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z510,z4,z5,z6])],[(0,[z1,z19,z3,z4,z5,z159,z6]),(0,[z43,z2,z3,z4,z5,z6,z97]),(0,[z1,z2,z3,z4,z691,z5,z6]),(0,[z1,z2,z3,z4,z5,z692,z6])],[(0,[z1,z2,z3,z345,z38,z4,z5]),(0,[z1,z2,z80,z4,z104,z5,z6]),(0,[z1,z2,z95,z3,z80,z5,z6]),(0,[z1,z2,z3,z4,z58,z77,z6]),(0,[z1,z2,z227,z3,z4,z5,z73])],[(0,[z452,z1,z2,z3,z4,z5,z6]),(0,[z43,z1,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z511,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z10]),(1,[z1,z2,z3,z4,z5,z347])],[(0,[z90,z1,z248,z3,z4,z5,z6]),(0,[z2,z3,z38,z4,z5,z58,z6])],[(1,[z245,z1,z2,z3,z4,z5]),(0,[z1,z30,z3,z3,z4,z5,z6])],[(0,[z1,z2,z3,z693,z4,z5,z6]),(1,[z1,z438,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z694]),(0,[z1,z2,z3,z4,z5,z6,z695]),(0,[z1,z696,z2,z3,z4,z5,z6])],[(0,[z1,z3,z59,z4,z33,z5,z6]),(0,[z1,z2,z3,z697,z4,z5,z6])]],
   [[(0,[z28,z2,z3,z38,z4,z5,z6]),(0,[z85,z1,z2,z95,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z698,z6]),(1,[z1,z161,z3,z4,z5,z6]),(1,[z1,z476,z3,z4,z5,z6])],[(0,[z137,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z6,z196]),(0,[z1,z3,z362,z59,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z699])],[(0,[z2,z3,z38,z80,z4,z5,z6]),(0,[z24,z2,z3,z38,z4,z5,z6]),(0,[z9,z1,z683,z3,z4,z5,z6]),(0,[z122,z1,z2,z3,z4,z5,z100]),(0,[z1,z3,z4,z5,z92,z6,z531])],[(0,[z1,z3,z45,z4,z132,z5,z6]),(0,[z1,z2,z3,z4,z700,z5,z6])],[(0,[z1,z2,z3,z4,z5,z701,z6])],[],[],[(0,[z1,z2,z3,z4,z5,z702,z6]),(0,[z356,z43,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z415,z5,z6]),(0,[z1,z2,z3,z4,z5,z703,z6]),(0,[z1,z2,z3,z4,z5,z6,z531])],[(0,[z98,z1,z30,z3,z4,z5,z6]),(0,[z1,z361,z30,z3,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z411,z6])],[(0,[z704,z1,z2,z3,z4,z5,z6])],[(0,[z63,z2,z168,z3,z4,z5,z6])],[(0,[z98,z43,z2,z3,z4,z5,z6]),(0,[z90,z1,z3,z45,z4,z5,z6]),(0,[z471,z1,z2,z3,z4,z5,z6]),(0,[z1,z119,z30,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z69,z5,z6]),(0,[z1,z2,z227,z3,z4,z5,z100])],[(0,[z43,z2,z3,z4,z5,z92,z6]),(0,[z149,z1,z3,z59,z4,z5,z6]),(0,[z165,z1,z326,z3,z4,z5,z6]),(0,[z24,z2,z3,z4,z71,z5,z6]),(0,[z705,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z42])],[(0,[z1,z3,z45,z166,z4,z5,z6])],[(0,[z2,z3,z38,z45,z4,z5,z6]),(0,[z1,z2,z3,z706,z4,z5,z6]),(0,[z164,z1,z2,z3,z4,z5,z6]),(0,[z380,z1,z2,z3,z4,z5,z6]),(0,[z1,z131,z2,z3,z4,z5,z6]),(0,[z252,z2,z3,z4,z5,z6,z97])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z369,z2,z3,z4,z5,z6]),(0,[z9,z28,z1,z3,z5,z18]),(0,[z1,z119,z3,z5,z6,z138]),(0,[z202,z3,z443,z4,z5,z6]),(0,[z1,z3,z59,z399,z5,z6]),(0,[z158,z1,z3,z4,z5,z120]),(0,[z1,z3,z707,z4,z5,z6])],[(0,[z1,z229,z3,z4,z5,z6]),(0,[z1,z30,z3,z4,z287,z6]),(0,[z68,z507,z1,z3,z4,z97])],[(0,[z708,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z709,z5,z6]),(0,[z346,z2,z3,z336,z5,z6]),(0,[z1,z710,z3,z4,z5,z6])],[(0,[z43,z2,z3,z4,z287,z6]),(0,[z1,z3,z59,z4,z379,z6]),(0,[z711,z2,z3,z4,z5,z6]),(0,[z1,z712,z3,z4,z5,z6]),(0,[z122,z1,z2,z289,z5,z100])],[(0,[z98,z135,z3,z4,z5,z6]),(0,[z245,z43,z2,z38,z4,z5]),(0,[z3,z38,z4,z5,z713,z6]),(0,[z1,z2,z3,z4,z12,z42]),(0,[z1,z714,z3,z4,z5,z6]),(0,[z1,z2,z3,z526,z4,z97])],[(0,[z1,z3,z715,z4,z5,z6]),(0,[z716,z1,z3,z4,z5,z6]),(0,[z1,z3,z45,z717,z5,z6]),(0,[z718,z1,z3,z4,z5,z6])],[(0,[z1,z3,z59,z162,z5,z6]),(0,[z2,z3,z38,z5,z6,z129]),(0,[z9,z245,z1,z3,z4,z5]),(0,[z9,z296,z3,z4,z5,z6]),(0,[z9,z134,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z539,z100])],[(0,[z719,z1,z3,z4,z5,z276]),(0,[z1,z95,z45,z80,z5,z6]),(0,[z1,z227,z45,z4,z5,z73]),(0,[z584,z1,z3,z59,z5,z6]),(0,[z1,z2,z3,z4,z5,z720]),(0,[z1,z3,z721,z4,z5,z6])],[(0,[z19,z133,z3,z4,z5,z6]),(0,[z290,z2,z3,z4,z328,z6]),(0,[z43,z2,z546,z4,z5,z6]),(0,[z507,z1,z3,z4,z5,z6]),(0,[z17,z1,z3,z5,z138,z18])],[(0,[z9,z440,z3,z4,z5,z6]),(0,[z480,z1,z2,z104,z5,z6]),(0,[z1,z2,z3,z722,z4,z5]),(1,[z1,z2,z4,z723,z6])],[(0,[z1,z724,z3,z4,z5,z6]),(0,[z28,z30,z3,z4,z5,z8]),(0,[z1,z3,z45,z5,z6,z725]),(0,[z2,z3,z4,z5,z726,z6]),(0,[z249,z1,z683,z4,z5,z6])],[(0,[z433,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z727]),(0,[z1,z3,z510,z4,z5,z6])],[(0,[z290,z3,z45,z4,z71,z6]),(0,[z94,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z728]),(0,[z729,z2,z3,z4,z5,z6])],[(0,[z22,z43,z3,z4,z5,z110]),(0,[z1,z2,z3,z4,z730,z6]),(0,[z9,z49,z1,z3,z35,z6]),(0,[z1,z3,z59,z4,z5,z731])],[(0,[z63,z493,z3,z4,z5,z6]),(0,[z2,z38,z4,z5,z657,z6]),(0,[z398,z382,z3,z4,z5,z6]),(0,[z369,z3,z59,z4,z5,z6]),(1,[z1,z3,z4,z5,z732]),(0,[z1,z3,z4,z5,z733,z6]),(0,[z1,z421,z2,z3,z5,z18])]],
   [[(0,[z1,z3,z734,z4,z5,z6]),(0,[z9,z369,z3,z4,z5,z6]),(0,[z1,z80,z4,z192,z5,z6]),(0,[z1,z3,z166,z59,z58,z6]),(0,[z85,z1,z2,z104,z5,z6]),(0,[z68,z252,z2,z3,z4,z97])],[(0,[z1,z2,z3,z4,z5,z735]),(0,[z90,z9,z38,z4,z5,z6]),(0,[z28,z3,z45,z4,z5,z8]),(0,[z30,z3,z474,z4,z5,z6]),(0,[z440,z30,z3,z4,z5,z6]),(0,[z708,z3,z59,z4,z5,z6]),(0,[z1,z236,z3,z4,z5,z86]),(0,[z1,z130,z3,z4,z287,z6])],[(0,[z2,z671,z38,z4,z5,z6]),(0,[z3,z96,z25,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z736])],[(0,[z93,z168,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z737])],[(0,[z2,z3,z38,z351,z5,z6]),(0,[z1,z3,z4,z738,z5,z6]),(0,[z1,z3,z4,z5,z6,z739]),(0,[z740,z2,z3,z4,z5,z6])],[(0,[z1,z3,z4,z741,z5,z6]),(0,[z1,z3,z4,z5,z742,z6]),(0,[z1,z66,z4,z192,z5,z6]),(0,[z2,z227,z53,z4,z5,z73])],[(0,[z743,z2,z3,z4,z5,z6]),(0,[z2,z3,z744,z4,z5,z6]),(0,[z369,z3,z292,z4,z5,z6]),(0,[z745,z2,z3,z4,z5,z6])],[(0,[z2,z678,z38,z4,z5,z6]),(0,[z440,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z746,z6]),(0,[z9,z222,z3,z4,z5,z6]),(0,[z2,z3,z747,z4,z5,z6]),(0,[z1,z2,z3,z4,z748,z6])],[(0,[z63,z3,z4,z652,z5,z6]),(0,[z1,z749,z3,z4,z5,z6]),(0,[z1,z3,z750,z4,z5,z6])],[(0,[z43,z236,z3,z4,z5,z6]),(0,[z751,z2,z3,z4,z5,z6]),(0,[z1,z236,z3,z4,z5,z242])],[(0,[z432,z168,z3,z4,z5,z6]),(0,[z1,z752,z3,z4,z5,z6]),(0,[z24,z2,z3,z53,z4,z5]),(0,[z158,z1,z3,z4,z753,z6]),(0,[z754,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z755,z4,z6]),(0,[z2,z3,z4,z71,z5,z155]),(0,[z1,z3,z756,z4,z5,z6]),(0,[z757,z1,z3,z4,z5,z6])],[(0,[z2,z3,z758,z4,z5,z6]),(0,[z1,z3,z4,z192,z5,z307])],[(0,[z43,z2,z3,z4,z5,z347]),(0,[z1,z759,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z531])],[(0,[z1,z30,z372,z4,z5,z6]),(0,[z1,z760,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z761,z6])],[(0,[z1,z3,z345,z762,z4,z5]),(0,[z9,z1,z3,z693,z5,z6]),(0,[z122,z1,z59,z4,z5,z100])]],
   [[(0,[z763,z2,z3,z38,z4,z6]),(0,[z43,z438,z3,z4,z5,z6]),(0,[z764,z1,z3,z4,z5,z6]),(0,[z24,z2,z3,z4,z5,z173])],[(0,[z1,z2,z3,z765,z5,z6]),(0,[z1,z766,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z767]),(0,[z9,z768,z3,z4,z5,z6]),(0,[z9,z1,z3,z5,z18,z97]),(0,[z769,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z770,z6])],[(0,[z1,z168,z3,z399,z5,z6]),(0,[z1,z3,z771,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z772]),(0,[z773,z2,z3,z4,z5,z6]),(1,[z1,z2,z774,z5,z6])],[(0,[z1,z775,z3,z4,z5,z6]),(0,[z776,z3,z38,z4,z5,z6]),(0,[z43,z161,z3,z4,z5,z6]),(0,[z43,z476,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z777,z6])],[(0,[z1,z2,z3,z778,z5,z6]),(0,[z331,z401,z3,z4,z5,z6]),(0,[z779,z9,z3,z4,z5,z6]),(0,[z780,z1,z3,z4,z5,z6])],[(0,[z9,z1,z3,z259,z5,z6]),(0,[z1,z2,z3,z781,z5,z6]),(0,[z743,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z80,z5,z242]),(0,[z1,z2,z3,z4,z5,z782]),(0,[z2,z3,z4,z5,z322,z783])],[(0,[z3,z38,z59,z4,z5,z120]),(0,[z1,z2,z3,z4,z5,z784]),(0,[z1,z3,z4,z5,z6,z785]),(0,[z1,z3,z4,z5,z6,z786]),(0,[z1,z787,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z788,z347]),(0,[z1,z3,z789,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z314])],[(0,[z165,z2,z3,z4,z50,z6]),(0,[z278,z168,z3,z4,z5,z6]),(0,[z2,z3,z38,z4,z5,z790]),(0,[z2,z95,z38,z80,z5,z6]),(0,[z2,z227,z38,z4,z5,z73]),(0,[z3,z38,z762,z4,z5,z6]),(0,[z791,z1,z3,z4,z5,z6]),(0,[z24,z2,z3,z4,z5,z196]),(0,[z370,z3,z45,z4,z5,z6]),(0,[z1,z161,z3,z351,z5,z6]),(0,[z565,z1,z2,z3,z4,z97])],[(0,[z1,z2,z4,z5,z792,z100])],[(0,[z1,z3,z45,z4,z5,z86]),(0,[z158,z1,z3,z399,z5,z6])],[(0,[z1,z3,z4,z176,z265,z6]),(0,[z30,z3,z38,z4,z5,z6]),(0,[z793,z1,z3,z4,z5,z6]),(0,[z1,z794,z3,z4,z5,z6]),(0,[z1,z2,z3,z795,z166,z6])],[(0,[z527,z9,z1,z3,z5,z6]),(0,[z9,z43,z3,z109,z5,z6]),(0,[z537,z43,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z796]),(0,[z1,z30,z3,z4,z5,z242]),(0,[z296,z161,z3,z4,z5,z6]),(0,[z408,z3,z4,z5,z6,z138])],[(0,[z797,z1,z3,z4,z5,z6]),(0,[z249,z43,z3,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z42]),(0,[z469,z2,z3,z16,z5,z6])],[(0,[z1,z2,z3,z4,z5,z798]),(0,[z130,z3,z38,z4,z5,z6]),(0,[z507,z3,z38,z4,z5,z6]),(0,[z799,z1,z3,z4,z5,z6]),(0,[z501,z1,z3,z4,z5,z110]),(0,[z1,z30,z3,z166,z58,z6])],[(1,[z800,z3,z4,z5,z6]),(0,[z1,z3,z45,z4,z5,z651]),(0,[z1,z2,z3,z4,z801,z6])]],
   [[(0,[z2,z3,z802,z4,z5,z6]),(0,[z43,z2,z3,z4,z5,z42]),(0,[z1,z3,z59,z497,z5,z6])],[(0,[z115,z19,z3,z4,z5,z6]),(0,[z433,z3,z38,z4,z5,z6]),(0,[z43,z2,z3,z166,z58,z6]),(0,[z1,z236,z3,z4,z287,z6]),(0,[z1,z803,z3,z4,z5,z6])],[(0,[z1,z3,z45,z4,z5,z242]),(0,[z804,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z805,z5,z6]),(0,[z1,z806,z3,z4,z5,z6])],[(0,[z2,z3,z4,z71,z6,z664]),(0,[z249,z1,z3,z91,z5,z6]),(0,[z1,z2,z3,z4,z5,z807]),(0,[z1,z2,z3,z4,z808,z6]),(0,[z809,z1,z3,z4,z5,z6])],[(0,[z43,z3,z14,z4,z5,z6]),(0,[z1,z810,z3,z4,z5,z6]),(0,[z1,z3,z45,z4,z5,z155]),(0,[z1,z3,z45,z166,z58,z6]),(0,[z654,z1,z2,z4,z77,z6]),(0,[z1,z2,z11,z4,z723,z6])],[(0,[z122,z2,z38,z4,z5,z100]),(0,[z81,z3,z38,z4,z5,z6]),(0,[z1,z3,z811,z4,z5,z6]),(0,[z1,z30,z3,z812,z5,z6]),(0,[z1,z2,z3,z813,z5,z6]),(0,[z1,z2,z3,z4,z5,z814]),(0,[z57,z3,z4,z5,z322,z6])],[(0,[z2,z3,z4,z5,z74,z6]),(0,[z3,z38,z385,z4,z5,z6]),(0,[z43,z3,z4,z5,z27,z6]),(0,[z1,z3,z59,z4,z5,z314]),(0,[z1,z3,z45,z4,z5,z307]),(0,[z9,z343,z3,z4,z5,z6]),(0,[z9,z1,z227,z4,z5,z73]),(0,[z222,z2,z3,z4,z379,z6])],[(0,[z63,z382,z3,z4,z5,z6]),(0,[z24,z3,z59,z4,z5,z196]),(0,[z815,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z289,z5,z6]),(0,[z1,z816,z3,z4,z5,z6]),(0,[z1,z817,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z818,z6]),(0,[z1,z2,z3,z819,z5,z6]),(0,[z199,z1,z3,z4,z649,z6]),(0,[z1,z3,z820,z336,z5,z6])],[],[(0,[z122,z1,z2,z685,z4,z5]),(0,[z9,z821,z3,z4,z5,z6]),(0,[z768,z2,z3,z4,z5,z6]),(0,[z9,z1,z3,z169,z5,z6]),(0,[z1,z3,z4,z5,z822,z6]),(0,[z1,z823,z3,z4,z5,z6])],[(0,[z237,z63,z3,z4,z5,z6]),(0,[z1,z2,z824,z4,z5,z6]),(0,[z1,z825,z3,z4,z5,z6])],[(0,[z2,z3,z345,z4,z5,z233]),(0,[z826,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z795,z4,z6])],[(0,[z3,z38,z4,z103,z5,z6]),(0,[z2,z3,z4,z5,z6,z827]),(0,[z828,z1,z3,z4,z5,z6])],[(0,[z1,z829,z3,z4,z5,z6]),(0,[z830,z2,z3,z4,z5,z6]),(0,[z22,z1,z3,z4,z5,z732]),(0,[z41,z1,z161,z4,z77,z6]),(0,[z831,z1,z3,z4,z5,z6]),(0,[z49,z1,z2,z3,z35,z6]),(0,[z3,z4,z5,z27,z322,z6])],[(0,[z1,z2,z3,z4,z5,z832]),(0,[z1,z2,z3,z4,z5,z833]),(0,[z834,z1,z3,z4,z5,z6]),(0,[z252,z3,z59,z4,z5,z6]),(0,[z1,z123,z3,z4,z539,z6]),(0,[z3,z53,z510,z4,z5,z6])]],
   [[(0,[z2,z3,z67,z5,z6,z557]),(0,[z263,z9,z1,z3,z5,z18]),(0,[z9,z1,z3,z183,z5,z6]),(0,[z835,z2,z3,z4,z5,z6]),(0,[z836,z2,z3,z4,z5,z6]),(0,[z837,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z838]),(1,[z1,z3,z839,z5,z6])],[(0,[z1,z257,z3,z4,z5,z92]),(0,[z1,z2,z3,z5,z6,z840]),(0,[z1,z3,z59,z4,z5,z807]),(0,[z17,z1,z3,z59,z5,z18])],[(0,[z90,z2,z841,z4,z5,z6]),(0,[z1,z842,z3,z4,z5,z6]),(0,[z165,z2,z3,z4,z60,z6]),(0,[z9,z170,z3,z4,z5,z6]),(0,[z9,z1,z3,z437,z5,z6]),(0,[z1,z2,z3,z4,z5,z843])],[(0,[z114,z168,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z844,z6]),(0,[z245,z43,z2,z3,z4,z5]),(0,[z2,z3,z38,z845,z4,z6]),(0,[z150,z1,z3,z104,z5,z6]),(0,[z3,z4,z5,z6,z138,z167])],[(0,[z158,z1,z3,z4,z411,z6]),(0,[z9,z1,z3,z59,z5,z6])],[(0,[z1,z464,z3,z4,z5,z6]),(0,[z1,z30,z262,z4,z5,z6]),(0,[z1,z3,z45,z4,z5,z846]),(0,[z1,z3,z59,z289,z5,z6]),(0,[z1,z3,z4,z176,z5,z120]),(0,[z122,z1,z2,z4,z539,z100]),(0,[z847,z2,z3,z4,z5,z6])],[(0,[z134,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z4,z287,z242])],[(0,[z43,z30,z38,z4,z5,z6]),(0,[z24,z2,z3,z4,z5,z251]),(0,[z1,z848,z3,z4,z5,z6])],[(0,[z245,z2,z3,z207,z4,z5]),(0,[z1,z30,z270,z4,z5,z6]),(0,[z849,z1,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z850]),(0,[z1,z3,z4,z5,z6,z851])],[(0,[z2,z3,z38,z4,z5,z86]),(0,[z165,z3,z4,z445,z60,z6]),(0,[z1,z3,z45,z4,z287,z6]),(0,[z1,z3,z4,z5,z852,z6]),(0,[z853,z2,z3,z4,z5,z6]),(0,[z68,z1,z2,z3,z4,z97])],[(0,[z9,z24,z3,z4,z5,z196])],[(0,[z245,z2,z168,z3,z4,z5]),(0,[z99,z245,z2,z3,z4,z5]),(0,[z30,z3,z4,z5,z6,z167]),(0,[z2,z3,z854,z4,z5,z6]),(0,[z343,z223,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z788])],[(0,[z1,z3,z855,z4,z5,z6]),(0,[z9,z1,z3,z4,z5,z728]),(0,[z1,z264,z3,z5,z23,z129]),(0,[z1,z2,z3,z4,z5,z856]),(0,[z1,z857,z3,z4,z5,z6])],[(0,[z63,z133,z3,z4,z5,z6]),(0,[z1,z3,z482,z4,z5,z6]),(0,[z858,z2,z3,z4,z5,z6]),(0,[z859,z1,z3,z4,z5,z6])],[(0,[z2,z3,z38,z4,z5,z651]),(0,[z17,z2,z3,z38,z5,z18]),(0,[z122,z9,z1,z4,z5,z100]),(0,[z49,z1,z2,z3,z795,z6])]],
   [[(0,[z125,z2,z3,z4,z5,z6]),(0,[z1,z860,z3,z4,z5,z6]),(0,[z30,z3,z178,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z861]),(0,[z1,z2,z3,z4,z862,z6])],[(0,[z1,z521,z3,z59,z5,z6]),(0,[z1,z30,z45,z4,z5,z6]),(0,[z1,z264,z3,z4,z5,z384]),(0,[z1,z2,z774,z104,z5,z6]),(0,[z863,z1,z3,z4,z5,z6])],[(0,[z2,z3,z38,z4,z5,z242]),(0,[z797,z3,z38,z4,z5,z6]),(0,[z165,z3,z59,z4,z60,z6]),(0,[z249,z1,z3,z218,z5,z6]),(0,[z1,z2,z3,z5,z6,z129])],[(0,[z280,z3,z38,z4,z5,z6]),(0,[z1,z864,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z8,z865])],[(0,[z1,z2,z3,z4,z5,z866]),(0,[z2,z3,z38,z4,z5,z155]),(0,[z364,z1,z2,z3,z5,z18])],[(0,[z1,z133,z3,z4,z5,z6]),(0,[z1,z724,z3,z345,z4,z5]),(0,[z1,z3,z270,z91,z5,z6])],[(0,[z2,z3,z38,z4,z5,z307]),(0,[z1,z3,z867,z4,z5,z6]),(0,[z868,z2,z3,z4,z5,z6]),(0,[z41,z1,z2,z4,z77,z6]),(0,[z480,z1,z2,z4,z77,z6]),(0,[z1,z2,z3,z4,z5,z869])],[(0,[z7,z2,z3,z4,z5,z235]),(0,[z85,z1,z45,z104,z5,z6]),(0,[z1,z270,z80,z4,z5,z6]),(0,[z158,z1,z3,z4,z431,z6]),(0,[z2,z3,z870,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z792]),(0,[z871,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z872,z5,z6]),(0,[z1,z3,z4,z5,z873,z6]),(0,[z1,z874,z3,z4,z5,z6])],[(0,[z875,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z876,z6]),(0,[z370,z123,z3,z4,z5,z6])],[(0,[z1,z877,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z878]),(0,[z30,z3,z53,z4,z5,z6])],[(0,[z343,z2,z3,z4,z5,z6]),(0,[z1,z879,z3,z4,z5,z6]),(0,[z9,z1,z3,z5,z100,z18]),(0,[z57,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z795,z5,z6])],[(0,[z1,z30,z3,z4,z5,z347]),(0,[z3,z59,z4,z5,z322,z6]),(0,[z1,z3,z4,z5,z6,z153])],[(0,[z165,z2,z3,z4,z880,z6]),(1,[z2,z3,z4,z5,z865]),(0,[z1,z881,z3,z4,z5,z6])],[(0,[z527,z2,z3,z132,z5,z6]),(0,[z1,z3,z882,z4,z5,z6]),(0,[z9,z408,z3,z5,z6,z18]),(0,[z125,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z351,z5,z6]),(0,[z1,z3,z883,z4,z5,z6])]],
   [[(0,[z365,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z884]),(0,[z1,z3,z4,z176,z753,z6])],[(0,[z2,z3,z38,z4,z5,z885]),(0,[z150,z1,z3,z109,z5,z6]),(0,[z249,z1,z3,z5,z6,z18]),(0,[z1,z3,z59,z5,z6,z129])],[(0,[z61,z168,z3,z4,z5,z6]),(0,[z341,z19,z3,z4,z5,z6]),(0,[z165,z2,z3,z4,z174,z6]),(0,[z1,z2,z3,z886,z5,z6]),(0,[z1,z2,z3,z166,z58,z347])],[(0,[z296,z2,z3,z4,z5,z6]),(0,[z43,z123,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z880,z6]),(0,[z1,z3,z45,z4,z5,z347]),(0,[z1,z3,z887,z4,z5,z6]),(0,[z1,z3,z888,z4,z5,z6]),(0,[z1,z161,z3,z4,z5,z651])],[(0,[z43,z38,z45,z4,z5,z6]),(0,[z43,z2,z3,z4,z5,z889]),(0,[z408,z2,z3,z4,z5,z6]),(0,[z1,z890,z45,z4,z5,z6]),(0,[z9,z432,z3,z4,z5,z6])],[(0,[z43,z3,z4,z5,z6,z138]),(0,[z1,z3,z4,z891,z5,z6]),(0,[z49,z1,z3,z45,z35,z6]),(0,[z868,z3,z59,z4,z5,z6])],[(0,[z3,z38,z4,z5,z445,z6]),(0,[z17,z1,z30,z3,z5,z18]),(0,[z1,z2,z3,z339,z58,z6])],[(0,[z98,z3,z4,z33,z5,z6]),(0,[z9,z1,z3,z4,z5,z314]),(0,[z84,z9,z1,z3,z5,z18]),(0,[z1,z892,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z6,z893])],[(0,[z158,z1,z3,z4,z477,z6]),(0,[z1,z3,z59,z4,z746,z6]),(0,[z2,z3,z4,z5,z894,z6])],[(0,[z9,z3,z38,z59,z5,z6]),(0,[z2,z3,z38,z4,z287,z6]),(0,[z43,z3,z4,z143,z5,z6]),(0,[z1,z3,z895,z4,z5,z6]),(0,[z1,z30,z11,z4,z12,z6]),(0,[z9,z1,z3,z5,z73,z18]),(0,[z896,z2,z3,z4,z5,z6])],[(0,[z1,z3,z25,z4,z5,z6]),(0,[z343,z3,z59,z4,z5,z6]),(0,[z751,z3,z59,z4,z5,z6])],[(0,[z2,z3,z4,z71,z702,z6]),(0,[z43,z3,z36,z4,z5,z6]),(0,[z2,z3,z67,z5,z595,z6]),(0,[z1,z3,z897,z4,z5,z6]),(0,[z1,z3,z4,z5,z23,z732])],[(0,[z161,z3,z38,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z898]),(0,[z43,z2,z11,z4,z12,z6]),(0,[z24,z2,z3,z4,z5,z314]),(0,[z2,z3,z4,z5,z899,z6]),(0,[z900,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z795,z58,z6])],[(0,[z2,z901,z3,z4,z5,z6]),(0,[z1,z3,z59,z351,z5,z6])],[(0,[z202,z168,z3,z4,z5,z6]),(0,[z1,z3,z345,z59,z4,z5]),(0,[z902,z2,z3,z4,z5,z6]),(0,[z365,z3,z59,z4,z5,z6])]],
   [[(0,[z492,z1,z45,z4,z5,z6]),(0,[z9,z1,z3,z378,z5,z6])],[(0,[z68,z1,z3,z45,z4,z97]),(0,[z1,z903,z3,z4,z5,z6])],[(0,[z170,z30,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z904]),(0,[z1,z2,z905,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z790]),(0,[z1,z277,z3,z4,z304,z6]),(0,[z1,z2,z3,z4,z5,z906]),(0,[z1,z3,z59,z4,z5,z767]),(0,[z408,z3,z59,z4,z5,z6])],[(0,[z2,z3,z4,z5,z322,z6]),(0,[z1,z2,z3,z4,z5,z907]),(0,[z29,z1,z3,z4,z5,z151]),(0,[z85,z1,z2,z104,z379,z6]),(0,[z346,z2,z3,z289,z5,z6]),(0,[z1,z3,z4,z5,z6,z908]),(0,[z909,z2,z3,z4,z5,z6])],[(0,[z90,z38,z59,z4,z5,z6]),(0,[z1,z3,z910,z4,z5,z6]),(1,[z2,z3,z4,z880,z6])],[(0,[z1,z3,z45,z4,z5,z42]),(0,[z9,z1,z3,z4,z539,z6]),(0,[z911,z2,z3,z4,z5,z6]),(0,[z912,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z913,z6]),(0,[z43,z20,z3,z4,z176,z6]),(0,[z9,z1,z3,z465,z5,z6]),(0,[z9,z914,z3,z4,z5,z6]),(0,[z9,z1,z3,z289,z5,z6])],[(0,[z290,z2,z3,z4,z71,z6])],[(0,[z9,z3,z345,z38,z4,z5]),(0,[z1,z2,z3,z4,z539,z6])],[(0,[z915,z1,z3,z4,z5,z6]),(0,[z916,z2,z3,z4,z5,z6]),(0,[z37,z1,z890,z4,z5,z6]),(0,[z9,z125,z3,z4,z5,z6]),(0,[z917,z2,z3,z4,z5,z6]),(0,[z1,z2,z95,z774,z5,z6])],[(0,[z9,z1,z3,z680,z5,z6]),(0,[z918,z1,z3,z4,z5,z6]),(0,[z9,z1,z3,z59,z5,z120]),(0,[z1,z3,z14,z4,z5,z307]),(0,[z343,z2,z95,z80,z5,z6])],[(0,[z1,z2,z3,z4,z5,z919]),(0,[z43,z30,z66,z4,z5,z6]),(0,[z9,z43,z3,z91,z5,z6]),(0,[z1,z3,z920,z4,z5,z6]),(0,[z1,z2,z3,z35,z795,z6])],[(0,[z1,z921,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z922]),(0,[z149,z359,z3,z67,z5,z6]),(0,[z1,z3,z4,z5,z923,z6]),(0,[z924,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z73,z792])],[(0,[z1,z2,z3,z4,z5,z925]),(0,[z1,z926,z3,z4,z5,z6]),(0,[z2,z38,z4,z253,z5,z6]),(0,[z1,z3,z927,z4,z5,z6]),(0,[z30,z134,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z928])]],
   [[(0,[z1,z30,z490,z4,z5,z6]),(0,[z149,z2,z3,z141,z5,z6]),(0,[z1,z11,z45,z4,z12,z6]),(0,[z9,z469,z3,z4,z5,z6]),(0,[z3,z4,z5,z6,z153,z402])],[(0,[z98,z3,z101,z4,z5,z6]),(0,[z1,z929,z3,z4,z5,z6]),(0,[z2,z38,z4,z5,z6,z260]),(0,[z57,z3,z38,z4,z5,z6])],[(0,[z2,z38,z262,z4,z5,z6]),(0,[z1,z30,z193,z4,z5,z6]),(0,[z1,z119,z2,z3,z5,z307]),(0,[z1,z227,z59,z4,z5,z73])],[(0,[z2,z3,z38,z4,z5,z347]),(0,[z1,z3,z270,z5,z6,z18]),(0,[z68,z2,z3,z4,z402,z97])],[(1,[z2,z3,z872,z5,z6]),(0,[z930,z2,z3,z4,z5,z6]),(0,[z1,z241,z45,z4,z5,z6]),(0,[z931,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z932])],[(0,[z359,z3,z38,z4,z5,z6]),(0,[z1,z933,z3,z4,z5,z6]),(0,[z1,z3,z4,z934,z5,z6]),(0,[z2,z3,z4,z5,z935,z6]),(0,[z1,z2,z3,z91,z5,z231]),(0,[z1,z3,z4,z5,z6,z936])],[(0,[z245,z98,z2,z3,z4,z5]),(0,[z43,z3,z4,z5,z937,z6]),(0,[z28,z136,z3,z4,z5,z8])],[(0,[z3,z474,z59,z4,z5,z6]),(0,[z938,z2,z3,z4,z5,z6]),(0,[z939,z1,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z940])],[(0,[z1,z3,z941,z4,z5,z6]),(0,[z1,z3,z4,z5,z942,z6]),(0,[z1,z45,z4,z5,z127,z6]),(0,[z1,z3,z4,z5,z6,z943]),(0,[z1,z3,z59,z4,z539,z6]),(0,[z85,z1,z236,z104,z5,z6]),(0,[z1,z944,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z945])],[(0,[z1,z2,z3,z946,z5,z6]),(0,[z1,z3,z45,z947,z4,z5])],[(0,[z1,z948,z3,z4,z5,z6]),(0,[z9,z245,z3,z38,z4,z5]),(0,[z2,z195,z38,z4,z5,z6]),(0,[z290,z2,z3,z4,z880,z6]),(0,[z3,z96,z45,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z949])],[(0,[z2,z3,z4,z5,z8,z276]),(0,[z1,z3,z14,z4,z5,z846]),(0,[z1,z2,z3,z950,z5,z6])],[(0,[z1,z3,z951,z4,z5,z6])],[(0,[z1,z952,z3,z4,z5,z6]),(0,[z43,z223,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z953]),(0,[z954,z1,z3,z4,z5,z6]),(0,[z1,z955,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z922])],[(0,[z1,z3,z59,z548,z5,z6]),(0,[z1,z3,z4,z5,z956,z6]),(0,[z1,z3,z327,z4,z5,z298]),(0,[z9,z1,z3,z91,z5,z18]),(0,[z1,z2,z4,z12,z723,z6])],[(0,[z1,z2,z3,z845,z4,z6]),(0,[z122,z43,z2,z4,z5,z100]),(0,[z2,z3,z957,z4,z5,z6])]],
   [[(0,[z3,z38,z958,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z959]),(0,[z1,z14,z4,z192,z5,z6]),(0,[z9,z1,z3,z547,z5,z6]),(0,[z960,z2,z3,z4,z5,z6])],[(0,[z43,z3,z4,z961,z5,z6]),(0,[z1,z962,z3,z4,z5,z6]),(0,[z963,z2,z3,z4,z5,z6])],[(0,[z136,z3,z4,z5,z8,z6]),(0,[z1,z45,z4,z5,z701,z6]),(0,[z9,z1,z3,z5,z6,z129]),(0,[z2,z964,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z965]),(0,[z1,z264,z3,z4,z5,z23]),(0,[z2,z95,z96,z80,z5,z6])],[(0,[z90,z2,z38,z4,z5,z6]),(0,[z1,z3,z966,z4,z5,z6]),(0,[z793,z3,z38,z4,z5,z6]),(0,[z370,z2,z3,z4,z5,z6]),(0,[z967,z2,z3,z4,z5,z6]),(0,[z2,z3,z968,z4,z5,z6])],[(0,[z158,z43,z3,z4,z159,z6]),(0,[z17,z1,z2,z3,z5,z969])],[(0,[z1,z2,z3,z5,z970,z6]),(0,[z2,z3,z345,z4,z5,z8]),(0,[z43,z2,z3,z4,z5,z235]),(0,[z1,z2,z3,z4,z971,z6]),(0,[z30,z3,z96,z4,z5,z6]),(0,[z972,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z86]),(0,[z1,z973,z3,z4,z5,z6]),(0,[z1,z294,z3,z4,z539,z6])],[(0,[z2,z3,z38,z4,z5,z42]),(0,[z1,z3,z59,z404,z5,z6]),(0,[z974,z2,z3,z4,z5,z6]),(0,[z1,z3,z975,z4,z5,z6]),(0,[z1,z294,z3,z289,z5,z6]),(0,[z1,z2,z3,z289,z295,z6]),(0,[z122,z1,z2,z4,z5,z792])],[(0,[z294,z3,z38,z4,z5,z6]),(0,[z2,z3,z38,z166,z58,z6]),(0,[z976,z2,z3,z4,z5,z6]),(0,[z1,z3,z977,z4,z5,z6])],[(0,[z245,z30,z3,z38,z4,z5]),(0,[z1,z978,z3,z4,z5,z6]),(0,[z1,z979,z3,z4,z5,z6]),(0,[z41,z1,z2,z16,z77,z6])],[(0,[z980,z1,z3,z45,z4,z5]),(0,[z85,z222,z2,z104,z5,z6])],[(0,[z1,z30,z3,z4,z5,z6]),(0,[z1,z3,z981,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z982]),(0,[z22,z1,z3,z4,z5,z110]),(0,[z1,z2,z3,z4,z5,z651])],[(0,[z1,z2,z3,z4,z5,z983]),(0,[z24,z133,z3,z4,z5,z6])],[(0,[z1,z200,z3,z4,z5,z23]),(0,[z37,z170,z45,z4,z5,z6]),(0,[z984,z2,z3,z4,z5,z6])],[(0,[z43,z2,z3,z4,z5,z6]),(0,[z41,z1,z45,z4,z77,z6]),(0,[z1,z264,z3,z4,z5,z732]),(0,[z1,z142,z3,z16,z5,z6]),(0,[z1,z3,z4,z985,z5,z6]),(0,[z17,z537,z1,z3,z5,z18])],[(0,[z1,z142,z3,z4,z5,z6]),(0,[z1,z30,z305,z4,z5,z6]),(0,[z529,z1,z4,z192,z5,z6]),(0,[z986,z1,z3,z289,z5,z6]),(0,[z987,z2,z3,z4,z5,z6])],[(0,[z3,z38,z510,z4,z5,z6]),(0,[z43,z81,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z155]),(0,[z9,z1,z3,z351,z5,z6])]],
   [[(0,[z2,z11,z38,z4,z12,z6]),(0,[z9,z1,z3,z4,z5,z884]),(0,[z158,z432,z3,z4,z5,z6])],[(0,[z2,z3,z988,z4,z5,z6]),(0,[z989,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z307]),(0,[z990,z1,z2,z4,z5,z6])],[(0,[z1,z359,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z991]),(0,[z992,z1,z2,z3,z4,z5]),(0,[z1,z993,z3,z4,z5,z6]),(0,[z815,z2,z3,z4,z5,z6]),(0,[z1,z30,z403,z4,z5,z6]),(0,[z9,z3,z4,z5,z6,z402]),(0,[z370,z3,z59,z4,z5,z6]),(0,[z530,z1,z3,z59,z5,z6])],[(0,[z2,z238,z38,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z994]),(0,[z995,z2,z3,z4,z5,z6])],[(0,[z440,z30,z66,z4,z5,z6]),(0,[z996,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z33,z5,z120]),(0,[z1,z3,z59,z4,z5,z86]),(0,[z1,z997,z3,z4,z5,z6])],[(0,[z9,z1,z3,z362,z5,z6]),(0,[z1,z3,z998,z4,z5,z6]),(0,[z296,z2,z3,z16,z5,z6])],[(0,[z1,z2,z3,z4,z5,z999]),(0,[z19,z800,z3,z4,z5,z6]),(0,[z7,z150,z1,z3,z5,z6]),(0,[z1,z3,z59,z4,z5,z866]),(0,[z1000,z2,z3,z4,z5,z6])],[(0,[z724,z3,z345,z38,z4,z5]),(0,[z43,z136,z3,z4,z5,z6]),(0,[z9,z1,z3,z5,z6,z138])],[(0,[z43,z2,z406,z4,z5,z6]),(0,[z43,z2,z3,z4,z5,z276]),(0,[z9,z1,z3,z118,z5,z6])],[(0,[z2,z841,z38,z4,z5,z6]),(0,[z2,z3,z38,z947,z4,z5]),(0,[z2,z3,z250,z4,z71,z6]),(0,[z7,z30,z3,z132,z5,z6]),(0,[z1,z2,z3,z1001,z5,z6]),(0,[z1,z2,z3,z4,z5,z1002]),(0,[z1,z3,z59,z4,z5,z651])],[(0,[z9,z43,z3,z5,z6,z18]),(0,[z1,z130,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z983]),(0,[z392,z2,z3,z4,z5,z92]),(0,[z1,z161,z3,z4,z5,z42]),(0,[z1,z2,z3,z487,z5,z18])],[(0,[z150,z43,z3,z4,z5,z6]),(0,[z1,z3,z45,z4,z5,z1003]),(0,[z249,z1,z270,z4,z5,z6]),(0,[z9,z1,z3,z368,z5,z6]),(0,[z432,z3,z4,z176,z5,z6]),(0,[z1,z3,z1004,z4,z5,z6]),(0,[z1,z3,z4,z5,z1005,z6])],[(0,[z43,z3,z59,z4,z5,z6]),(0,[z236,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z885]),(0,[z1,z3,z45,z4,z5,z1006]),(0,[z654,z1,z2,z4,z5,z100])],[(0,[z2,z800,z3,z4,z5,z6]),(0,[z1,z2,z3,z124,z4,z97])],[(0,[z43,z2,z416,z4,z5,z6]),(0,[z1,z2,z3,z4,z1007,z6]),(0,[z149,z2,z3,z872,z5,z6]),(0,[z1,z1008,z3,z4,z5,z6]),(0,[z1,z2,z3,z336,z539,z6]),(0,[z252,z2,z3,z4,z5,z92])],[(0,[z1009,z3,z38,z4,z5,z6]),(0,[z370,z2,z3,z4,z295,z6]),(0,[z1,z3,z4,z5,z6,z1010])]],
   [[(0,[z63,z674,z3,z4,z5,z6]),(0,[z2,z3,z38,z4,z5,z1011]),(0,[z3,z38,z4,z5,z6,z531]),(0,[z3,z45,z4,z5,z1012,z6]),(0,[z1,z3,z59,z4,z5,z307]),(0,[z1,z3,z72,z4,z5,z120]),(1,[z1,z3,z4,z753,z6]),(0,[z1,z3,z4,z5,z6,z1013])],[(0,[z1,z2,z3,z4,z5,z1014]),(0,[z150,z1,z3,z91,z5,z6]),(0,[z1,z2,z3,z4,z5,z846]),(0,[z1,z1015,z3,z4,z5,z6])],[(0,[z9,z1,z905,z4,z5,z6]),(0,[z2,z3,z4,z5,z1016,z6])],[(0,[z2,z3,z841,z4,z5,z6]),(0,[z43,z3,z292,z4,z5,z6]),(0,[z1017,z2,z3,z4,z5,z6]),(0,[z1,z3,z1018,z4,z5,z6]),(0,[z7,z3,z143,z132,z5,z6]),(0,[z290,z2,z3,z4,z71,z235])],[(0,[z326,z3,z38,z4,z5,z6]),(0,[z165,z2,z3,z4,z323,z6]),(0,[z1,z3,z1019,z4,z5,z6]),(0,[z2,z3,z4,z71,z880,z6]),(0,[z1,z2,z3,z717,z5,z6]),(0,[z1,z3,z4,z5,z120,z110]),(0,[z1,z2,z3,z348,z5,z18]),(0,[z125,z2,z3,z4,z379,z6]),(0,[z1,z2,z4,z774,z5,z6]),(0,[z2,z3,z4,z5,z1020,z6]),(0,[z1,z1021,z3,z4,z5,z6]),(0,[z2,z3,z1022,z4,z5,z6])],[(0,[z980,z1,z2,z3,z4,z5]),(0,[z1,z3,z1023,z4,z5,z6]),(0,[z1,z3,z482,z4,z5,z1024]),(0,[z296,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z4,z287,z6]),(0,[z1,z2,z3,z4,z6,z1025])],[(0,[z764,z1,z3,z4,z5,z314]),(0,[z346,z2,z3,z4,z539,z6])],[(0,[z165,z326,z3,z4,z60,z6]),(0,[z9,z408,z3,z4,z5,z6]),(0,[z1026,z1,z3,z4,z5,z6]),(0,[z1027,z2,z3,z4,z5,z6])],[(0,[z90,z245,z2,z38,z4,z5]),(0,[z9,z1,z3,z109,z5,z6]),(0,[z537,z1,z3,z4,z5,z6]),(0,[z2,z3,z722,z96,z4,z5])],[(0,[z43,z294,z3,z4,z5,z6]),(0,[z43,z2,z3,z4,z295,z6]),(0,[z149,z30,z3,z67,z5,z6]),(0,[z249,z1,z3,z4,z5,z6]),(0,[z1,z3,z1028,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z725]),(0,[z68,z1,z3,z59,z4,z97]),(0,[z931,z1,z3,z336,z5,z6]),(0,[z17,z408,z2,z3,z5,z18])],[(0,[z49,z2,z3,z38,z35,z6]),(0,[z150,z1,z3,z166,z5,z6]),(0,[z2,z3,z4,z5,z6,z1029])],[(0,[z2,z38,z4,z357,z5,z6]),(0,[z356,z2,z3,z4,z328,z6]),(0,[z170,z3,z45,z4,z5,z6]),(0,[z249,z1,z3,z482,z5,z6]),(0,[z1,z2,z3,z4,z1030,z6])],[(0,[z2,z3,z38,z4,z1031,z5]),(0,[z43,z2,z95,z80,z5,z6]),(0,[z914,z2,z3,z4,z5,z6])],[(0,[z1032,z1,z2,z3,z4,z5]),(0,[z9,z1,z264,z3,z5,z18])],[(0,[z1,z3,z4,z1033,z5,z6]),(0,[z43,z1034,z3,z4,z5,z6]),(0,[z149,z2,z3,z67,z5,z155])],[(0,[z22,z3,z38,z4,z5,z110]),(0,[z149,z3,z45,z67,z5,z6]),(0,[z28,z2,z3,z4,z5,z8]),(0,[z150,z1,z3,z80,z5,z6]),(0,[z1035,z2,z3,z4,z5,z6]),(0,[z1,z20,z3,z4,z649,z6]),(0,[z1,z2,z3,z5,z601,z18]),(0,[z1,z2,z3,z104,z379,z6])]],
   [[(0,[z2,z3,z4,z5,z1036,z6]),(0,[z9,z1,z3,z5,z6,z307]),(0,[z9,z1,z3,z397,z5,z6]),(0,[z1,z3,z59,z4,z5,z846])],[(0,[z1,z1037,z3,z4,z5,z6]),(0,[z2,z3,z67,z4,z5,z235]),(0,[z150,z1,z3,z14,z5,z6]),(0,[z1,z20,z3,z4,z753,z6])],[(0,[z1,z3,z1038,z4,z5,z6]),(0,[z2,z3,z67,z872,z5,z6]),(0,[z1,z66,z890,z4,z5,z6])],[(0,[z1,z1039,z3,z4,z5,z6]),(0,[z1,z2,z412,z4,z12,z6])],[(0,[z1,z2,z3,z4,z5,z1040])],[(0,[z440,z2,z3,z4,z5,z6]),(0,[z1,z3,z634,z59,z5,z6]),(0,[z1,z3,z1041,z4,z5,z6]),(0,[z1,z1042,z3,z4,z5,z6])],[(0,[z1043,z1,z3,z4,z5,z6]),(0,[z68,z2,z3,z38,z4,z97]),(0,[z1,z3,z4,z5,z6,z1044]),(0,[z9,z1,z3,z247,z5,z6]),(0,[z2,z3,z4,z5,z6,z1045])],[(0,[z501,z1,z3,z4,z5,z226]),(0,[z9,z3,z747,z4,z5,z6])],[(0,[z1046,z2,z3,z4,z5,z6]),(0,[z1,z119,z3,z839,z5,z6]),(0,[z1,z3,z4,z5,z1047,z6]),(0,[z370,z2,z3,z336,z5,z6])],[(0,[z1048,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z994,z314]),(0,[z1,z3,z4,z192,z5,z6])],[(0,[z98,z299,z3,z4,z5,z6]),(0,[z290,z3,z59,z4,z71,z6]),(0,[z28,z2,z3,z4,z5,z167]),(0,[z1,z3,z1049,z4,z5,z6]),(0,[z1,z236,z3,z4,z5,z6]),(0,[z1050,z2,z3,z4,z5,z6]),(0,[z507,z1,z3,z4,z5,z92])],[(0,[z9,z1,z3,z5,z6,z413])],[(0,[z9,z22,z1,z3,z5,z18]),(0,[z1,z2,z3,z4,z1051,z6])],[(0,[z3,z45,z4,z5,z6,z402])],[(0,[z28,z3,z59,z4,z5,z8])],[(0,[z1,z3,z1052,z4,z5,z6]),(0,[z41,z296,z2,z4,z77,z6]),(0,[z1053,z2,z3,z4,z5,z6])]],
   [[(0,[z245,z1,z2,z3,z4,z5]),(0,[z1,z1054,z3,z4,z5,z6]),(0,[z43,z257,z3,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z120]),(0,[z22,z1,z3,z4,z5,z531])],[(0,[z98,z3,z262,z4,z5,z6]),(0,[z24,z2,z3,z4,z5,z451]),(0,[z1055,z1,z3,z4,z5,z6]),(0,[z2,z3,z1056,z4,z5,z6])],[(0,[z1,z248,z3,z4,z5,z6]),(0,[z43,z2,z3,z336,z5,z6])],[(0,[z43,z2,z3,z4,z5,z120]),(0,[z1057,z1,z3,z4,z5,z6])],[(0,[z43,z2,z3,z4,z5,z1058]),(0,[z1,z476,z3,z4,z5,z6]),(0,[z440,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1059])],[(0,[z1,z1060,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1061]),(0,[z1,z30,z3,z4,z5,z235]),(0,[z1,z30,z3,z91,z5,z92]),(0,[z9,z1,z3,z4,z5,z86]),(0,[z1,z1062,z3,z4,z5,z6]),(0,[z1063,z2,z3,z96,z4,z5])],[(0,[z1,z3,z1064,z4,z5,z6]),(0,[z222,z2,z3,z4,z5,z86]),(0,[z2,z3,z1065,z4,z5,z6])],[(0,[z346,z30,z3,z4,z5,z6]),(0,[z1,z1066,z3,z4,z5,z6]),(0,[z49,z1,z2,z3,z697,z6])],[(0,[z43,z2,z3,z91,z5,z92]),(0,[z1,z2,z3,z4,z5,z1067]),(0,[z1,z3,z4,z1068,z5,z6]),(0,[z2,z3,z4,z5,z6,z1069])],[(0,[z1,z361,z3,z482,z5,z6]),(0,[z1,z2,z3,z4,z5,z1070]),(0,[z1,z2,z3,z4,z6,z1071]),(1,[z1,z2,z4,z5,z792]),(0,[z1,z3,z4,z5,z6,z1072])],[(0,[z9,z1,z3,z4,z5,z651])],[(0,[z464,z3,z38,z4,z5,z6]),(0,[z7,z9,z3,z132,z5,z6]),(0,[z1,z3,z45,z4,z5,z235]),(0,[z1,z3,z45,z1073,z4,z6]),(0,[z1,z3,z270,z4,z5,z6]),(0,[z222,z30,z3,z4,z5,z6]),(0,[z1,z3,z59,z5,z486,z6]),(0,[z1074,z2,z3,z4,z5,z6])],[(0,[z1,z30,z3,z16,z5,z6]),(0,[z1,z3,z1075,z4,z5,z6]),(0,[z1,z2,z3,z16,z5,z651])],[(0,[z9,z3,z38,z109,z5,z6]),(0,[z537,z3,z38,z4,z5,z6]),(0,[z1,z1076,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z5,z242]),(0,[z1077,z2,z3,z4,z5,z6])],[(0,[z43,z38,z59,z4,z5,z6]),(0,[z2,z3,z1078,z4,z5,z6]),(0,[z705,z1,z2,z3,z5,z18])],[(0,[z1,z2,z3,z1079,z5,z6]),(0,[z99,z2,z3,z4,z519,z6]),(0,[z7,z245,z2,z3,z4,z5]),(0,[z43,z2,z3,z16,z5,z6]),(0,[z9,z1,z3,z4,z5,z155]),(0,[z133,z3,z4,z5,z8,z6]),(0,[z150,z1,z3,z5,z6,z18]),(0,[z1,z30,z3,z4,z5,z366]),(0,[z1080,z2,z3,z4,z5,z6]),(0,[z1081,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z1082,z3,z4,z5,z6]),(0,[z1,z3,z1083,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z242]),(0,[z1084,z2,z3,z4,z5,z6]),(0,[z1085,z2,z3,z4,z5,z6])],[(0,[z3,z38,z482,z4,z5,z6]),(0,[z1,z1086,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z5,z307]),(0,[z1087,z2,z3,z4,z5,z6]),(0,[z1,z264,z3,z4,z5,z120]),(0,[z1,z2,z3,z4,z5,z42])],[(0,[z43,z3,z59,z4,z5,z120]),(0,[z43,z2,z3,z4,z5,z366]),(0,[z1,z3,z4,z5,z6,z1088]),(0,[z1,z2,z3,z166,z58,z6])],[(0,[z1,z3,z45,z4,z5,z6]),(0,[z1,z1089,z3,z4,z5,z6]),(0,[z85,z1,z103,z104,z5,z6])],[(0,[z1,z30,z3,z345,z4,z5]),(0,[z9,z1,z3,z218,z5,z6]),(0,[z1,z2,z3,z5,z6,z1090]),(0,[z1,z438,z11,z4,z12,z6])],[(0,[z142,z3,z38,z4,z5,z6]),(0,[z1,z3,z4,z1091,z5,z6]),(0,[z1,z45,z4,z5,z6,z187]),(0,[z1,z1092,z3,z4,z5,z6])],[(0,[z24,z2,z3,z4,z5,z395]),(0,[z1,z2,z3,z528,z5,z18]),(0,[z85,z1,z30,z104,z5,z6]),(0,[z9,z1,z3,z34,z5,z6]),(0,[z9,z1,z2,z3,z5,z307]),(0,[z9,z3,z4,z5,z74,z6])],[(0,[z43,z2,z3,z345,z4,z5]),(0,[z9,z149,z3,z67,z5,z6]),(0,[z1,z3,z4,z5,z27,z6]),(0,[z1,z3,z59,z4,z5,z1067]),(0,[z1,z3,z512,z4,z159,z6]),(0,[z1,z3,z998,z16,z5,z6])],[(0,[z1,z30,z406,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z276])],[(0,[z2,z3,z474,z4,z5,z6]),(0,[z1,z3,z1093,z4,z5,z6]),(0,[z1,z119,z3,z482,z5,z6]),(0,[z1,z2,z3,z812,z5,z6]),(0,[z779,z2,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z120,z531])],[(0,[z28,z2,z3,z4,z5,z70]),(0,[z222,z130,z3,z4,z5,z6])],[(1,[z9,z1,z3,z5,z307]),(0,[z1,z264,z3,z4,z5,z531]),(0,[z1094,z2,z3,z4,z5,z6]),(0,[z1,z1095,z3,z4,z5,z6]),(0,[z1,z2,z3,z1096,z5,z6])],[(0,[z63,z3,z64,z4,z5,z6]),(0,[z43,z119,z3,z59,z5,z6]),(0,[z2,z3,z4,z71,z281,z6]),(1,[z1,z890,z4,z5,z6]),(0,[z9,z1,z3,z396,z5,z6]),(0,[z1097,z1,z3,z4,z5,z6]),(0,[z1098,z2,z3,z178,z4,z5])],[(0,[z1,z20,z3,z4,z502,z6]),(0,[z1,z2,z3,z1099,z5,z6]),(0,[z1,z3,z45,z4,z5,z276]),(0,[z1,z3,z4,z5,z6,z1100])],[(0,[z1,z3,z4,z5,z1101,z6]),(0,[z1,z3,z5,z6,z1102,z18]),(0,[z1,z3,z59,z4,z5,z242]),(0,[z1,z2,z3,z1103,z5,z6]),(1,[z1,z2,z3,z5,z969])]],
   [[(0,[z3,z38,z4,z5,z6,z153]),(0,[z2,z3,z53,z4,z5,z6]),(0,[z432,z133,z3,z4,z5,z6]),(0,[z1,z20,z3,z4,z304,z6]),(0,[z1,z3,z59,z4,z5,z42])],[(0,[z19,z3,z416,z4,z5,z6]),(0,[z30,z3,z345,z38,z4,z5]),(0,[z245,z2,z3,z256,z4,z5]),(0,[z2,z38,z4,z339,z5,z6]),(0,[z43,z280,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z155]),(0,[z1,z2,z3,z5,z6,z1104]),(0,[z1,z3,z14,z4,z5,z1006]),(0,[z1,z119,z3,z59,z5,z307])],[(0,[z527,z9,z3,z38,z5,z6]),(0,[z43,z3,z385,z4,z5,z6]),(0,[z7,z3,z45,z132,z5,z6]),(0,[z28,z257,z3,z4,z5,z8]),(0,[z1,z264,z3,z399,z5,z23]),(0,[z1,z3,z1105,z351,z5,z6]),(0,[z370,z294,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z1106,z6]),(0,[z1,z1107,z3,z4,z5,z6]),(0,[z1108,z1,z3,z4,z5,z347])],[(0,[z1,z2,z3,z947,z4,z5]),(0,[z2,z3,z4,z5,z6,z1109]),(0,[z165,z245,z2,z3,z4,z5])],[(0,[z1,z1110,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z287,z6]),(0,[z1,z2,z267,z4,z12,z6])],[(0,[z117,z43,z3,z4,z5,z6]),(0,[z1,z1111,z3,z4,z5,z6])],[(0,[z245,z1,z3,z45,z4,z5]),(0,[z9,z94,z3,z4,z5,z6]),(0,[z17,z2,z3,z5,z167,z18]),(0,[z1,z2,z3,z4,z1112,z6])],[(0,[z1054,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z465,z5,z92]),(0,[z469,z142,z3,z4,z5,z6])],[(0,[z168,z3,z406,z4,z5,z6]),(0,[z43,z3,z4,z103,z5,z6]),(0,[z1,z3,z1113,z4,z5,z6]),(0,[z1,z30,z3,z4,z295,z6]),(0,[z1,z2,z3,z4,z379,z86])],[(0,[z1,z30,z505,z4,z5,z6]),(0,[z1,z30,z3,z399,z5,z6])],[(0,[z2,z3,z38,z1073,z4,z6]),(0,[z2,z3,z38,z4,z5,z235]),(0,[z1,z2,z3,z4,z5,z1011]),(0,[z28,z1,z2,z3,z289,z5]),(0,[z1114,z2,z3,z4,z5,z6])],[(0,[z43,z2,z38,z4,z5,z6]),(0,[z1,z1115,z3,z4,z5,z6]),(0,[z1116,z2,z3,z4,z5,z307]),(0,[z85,z125,z2,z104,z5,z6]),(0,[z469,z2,z3,z351,z5,z6]),(0,[z1,z3,z4,z5,z1117,z6]),(0,[z252,z3,z4,z5,z6,z153])],[(0,[z98,z19,z3,z4,z5,z6]),(0,[z43,z2,z3,z399,z5,z6]),(0,[z1,z1118,z3,z4,z5,z6]),(0,[z3,z178,z45,z4,z5,z6])],[(0,[z3,z38,z25,z4,z5,z6]),(0,[z1,z1119,z3,z4,z5,z6]),(0,[z1,z45,z4,z192,z5,z6]),(0,[z1,z1120,z3,z4,z5,z6]),(0,[z537,z3,z4,z5,z6,z167])],[(0,[z43,z2,z3,z4,z5,z1121]),(0,[z1,z2,z3,z1122,z5,z6]),(0,[z1,z3,z45,z4,z295,z6]),(0,[z1,z3,z4,z192,z5,z120]),(0,[z636,z1,z2,z3,z35,z6]),(0,[z2,z3,z1123,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z783])]],
   [[(0,[z223,z3,z38,z4,z5,z6]),(0,[z1,z1124,z3,z4,z5,z6])],[(0,[z43,z2,z3,z4,z379,z6])],[(0,[z9,z43,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z402,z314]),(0,[z197,z1,z3,z4,z159,z6]),(1,[z1,z2,z3,z795,z6])],[(0,[z2,z3,z38,z4,z5,z6])],[(0,[z438,z3,z38,z4,z5,z6]),(0,[z2,z3,z4,z5,z167,z276]),(0,[z2,z3,z1125,z4,z5,z6])],[(0,[z2,z38,z4,z5,z6,z367]),(0,[z243,z43,z3,z4,z5,z6]),(0,[z1,z1126,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z539]),(0,[z22,z1,z3,z4,z5,z10])],[(0,[z1127,z1,z3,z4,z5,z6]),(0,[z2,z3,z1128,z4,z5,z6]),(0,[z68,z1,z2,z3,z4,z1025])],[(0,[z1129,z1,z3,z4,z5,z6]),(0,[z43,z131,z3,z4,z5,z6]),(0,[z17,z9,z1,z3,z5,z18]),(0,[z1,z3,z59,z4,z287,z6]),(0,[z2,z3,z4,z5,z6,z1130])],[(0,[z43,z1131,z3,z4,z5,z6]),(0,[z9,z1,z3,z91,z5,z6]),(0,[z611,z1,z3,z4,z5,z307]),(0,[z3,z59,z4,z5,z6,z1132]),(0,[z1,z3,z362,z4,z5,z120]),(0,[z22,z134,z3,z4,z5,z6]),(0,[z2,z11,z178,z4,z12,z6]),(0,[z365,z2,z227,z4,z5,z73]),(0,[z1,z3,z1133,z4,z5,z6])],[(0,[z1134,z2,z3,z4,z5,z6]),(0,[z30,z1135,z3,z4,z5,z6])],[(0,[z1136,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1137,z6]),(0,[z2,z1138,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1139])],[(0,[z1,z3,z839,z109,z5,z6]),(0,[z1116,z3,z59,z4,z5,z307]),(0,[z222,z236,z3,z4,z5,z6]),(0,[z243,z1,z3,z91,z5,z6]),(0,[z1140,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z1141]),(0,[z1,z1142,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1143,z6])],[(0,[z43,z229,z3,z4,z5,z6]),(0,[z3,z59,z4,z5,z6,z167])],[(0,[z3,z38,z4,z1033,z5,z6]),(0,[z2,z3,z38,z4,z5,z276]),(0,[z111,z2,z3,z4,z5,z451]),(0,[z9,z1,z3,z4,z5,z347]),(0,[z1,z3,z4,z5,z753,z6]),(0,[z1,z130,z3,z4,z379,z6]),(0,[z1,z1144,z3,z4,z5,z6]),(0,[z1145,z2,z3,z4,z5,z6])],[(0,[z24,z2,z3,z4,z5,z522]),(0,[z1,z1146,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1147]),(0,[z1148,z1,z3,z351,z5,z6])]],
   [[(0,[z9,z24,z1,z3,z5,z18]),(0,[z1,z45,z4,z271,z5,z6])],[(0,[z43,z326,z3,z4,z5,z6]),(0,[z1,z2,z3,z1149,z5,z6]),(0,[z1,z1150,z3,z4,z5,z6]),(0,[z3,z45,z4,z5,z74,z6]),(0,[z85,z243,z1,z104,z5,z6]),(0,[z1,z2,z3,z4,z5,z347])],[(0,[z1,z3,z1151,z4,z5,z6]),(0,[z43,z1152,z3,z4,z5,z6]),(0,[z1,z1153,z3,z4,z5,z6]),(0,[z1,z1154,z3,z4,z5,z6]),(0,[z1,z30,z3,z336,z5,z6]),(0,[z1,z2,z3,z4,z1155,z6]),(0,[z2,z1156,z3,z4,z5,z6])],[(0,[z1,z3,z1157,z4,z5,z6]),(0,[z1,z3,z4,z1158,z5,z6])],[(0,[z1,z438,z3,z4,z5,z6]),(0,[z1,z30,z538,z4,z5,z6]),(0,[z49,z1,z30,z3,z35,z6]),(0,[z85,z1,z59,z104,z5,z6])],[(0,[z22,z1,z3,z4,z5,z160]),(0,[z1,z1159,z3,z4,z5,z6]),(0,[z1160,z2,z3,z4,z5,z6]),(0,[z43,z1161,z3,z4,z5,z6]),(0,[z1,z3,z1162,z4,z5,z6])],[(0,[z1,z1163,z3,z4,z5,z6]),(0,[z9,z290,z3,z4,z71,z6]),(0,[z2,z3,z4,z5,z8,z314]),(0,[z3,z53,z45,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z138])],[(0,[z82,z3,z256,z4,z5,z6]),(0,[z1,z161,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1006])],[(0,[z3,z345,z38,z762,z4,z5]),(0,[z37,z43,z45,z4,z5,z6]),(0,[z1,z3,z45,z336,z5,z6]),(0,[z1,z3,z482,z104,z5,z6]),(0,[z9,z1,z3,z499,z5,z6])],[(0,[z3,z38,z4,z192,z5,z6]),(0,[z1,z3,z45,z4,z5,z120])],[(0,[z1,z2,z3,z4,z1164,z6]),(0,[z30,z3,z4,z5,z6,z402])],[(0,[z1,z2,z3,z1165,z5,z6]),(0,[z1166,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1167]),(0,[z381,z1,z2,z104,z5,z6]),(0,[z122,z1,z2,z4,z5,z100])],[(0,[z245,z3,z38,z45,z4,z5]),(0,[z2,z3,z1168,z178,z4,z5])],[(0,[z9,z967,z3,z4,z5,z6]),(0,[z1,z3,z36,z4,z5,z6]),(0,[z2,z3,z1169,z4,z5,z6]),(0,[z1,z3,z1170,z4,z5,z6]),(0,[z507,z3,z4,z5,z6,z402])],[(0,[z992,z2,z3,z38,z4,z5]),(0,[z1,z3,z45,z91,z5,z92]),(0,[z1,z2,z11,z4,z12,z6]),(0,[z365,z3,z510,z4,z5,z6])],[(0,[z2,z3,z38,z4,z295,z6]),(0,[z1171,z1,z3,z4,z5,z6]),(0,[z9,z1,z3,z577,z5,z6]),(0,[z1172,z30,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1132]),(0,[z122,z1,z123,z4,z5,z100])]],
   [[(0,[z3,z345,z38,z45,z4,z5]),(0,[z346,z3,z45,z4,z5,z6]),(0,[z68,z1,z30,z3,z4,z97]),(0,[z1,z3,z1173,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z347]),(0,[z158,z1,z3,z4,z159,z6]),(0,[z172,z1,z2,z3,z4,z97]),(0,[z408,z2,z3,z4,z5,z216])],[(0,[z249,z3,z38,z4,z5,z6]),(0,[z1174,z1,z3,z4,z5,z6]),(0,[z24,z2,z3,z4,z5,z167]),(0,[z9,z1,z3,z4,z5,z42]),(0,[z1,z3,z59,z4,z1155,z6]),(0,[z222,z2,z3,z4,z5,z242]),(0,[z1175,z1,z3,z4,z5,z6]),(0,[z2,z3,z1176,z4,z5,z6])],[(0,[z1177,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z1178,z6]),(0,[z43,z3,z4,z5,z445,z6]),(0,[z1,z3,z45,z1179,z5,z6]),(0,[z1180,z1,z3,z4,z5,z6]),(0,[z9,z1,z3,z166,z58,z6]),(0,[z2,z3,z4,z5,z6,z1181])],[(0,[z245,z2,z3,z345,z4,z5]),(0,[z1,z3,z4,z5,z1182,z6]),(0,[z1,z1183,z3,z4,z5,z6]),(0,[z1,z2,z3,z16,z5,z42]),(0,[z1,z3,z1184,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z167]),(0,[z222,z3,z45,z4,z5,z6]),(0,[z9,z3,z4,z5,z322,z6]),(0,[z1185,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z553,z58,z6]),(0,[z1,z2,z3,z1186,z5,z6])],[(0,[z313,z19,z3,z4,z5,z6]),(0,[z2,z3,z38,z1187,z5,z6]),(0,[z1,z3,z45,z16,z5,z6]),(0,[z1188,z1,z3,z4,z5,z6]),(0,[z1189,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1190,z5,z6]),(0,[z122,z346,z2,z4,z5,z100])],[(0,[z170,z2,z3,z4,z5,z6]),(0,[z1,z1191,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z1059])],[(0,[z1,z2,z3,z4,z444,z97]),(0,[z1192,z1,z3,z4,z5,z6]),(0,[z1,z3,z45,z1193,z5,z6]),(0,[z1,z30,z890,z4,z5,z6]),(0,[z223,z3,z96,z4,z5,z6]),(0,[z2,z3,z1194,z4,z5,z6]),(0,[z1,z2,z3,z166,z58,z366])],[(0,[z2,z3,z178,z4,z5,z6]),(0,[z1,z3,z14,z4,z5,z6]),(0,[z1,z3,z45,z4,z5,z366]),(0,[z1,z20,z3,z4,z176,z6])],[(0,[z3,z270,z38,z4,z5,z6]),(0,[z1,z3,z1195,z4,z5,z6]),(0,[z9,z1,z3,z4,z1196,z6]),(0,[z1,z2,z3,z118,z5,z92]),(0,[z438,z3,z178,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1197])],[(0,[z85,z2,z38,z104,z5,z6]),(0,[z2,z38,z4,z5,z491,z6]),(0,[z2,z3,z96,z4,z5,z6]),(0,[z245,z2,z3,z4,z5,z196]),(0,[z1,z3,z1198,z4,z5,z6]),(0,[z1199,z1,z2,z3,z4,z5])],[(0,[z2,z3,z38,z1200,z4,z6]),(0,[z9,z1,z3,z348,z5,z6]),(0,[z1,z3,z4,z753,z159,z6]),(0,[z2,z3,z4,z5,z1201,z6])],[(0,[z1,z3,z4,z5,z727,z276]),(0,[z1,z2,z3,z4,z1196,z6]),(0,[z41,z1,z30,z4,z77,z6]),(0,[z1202,z2,z3,z4,z5,z6])],[(0,[z9,z3,z38,z91,z5,z6]),(0,[z1203,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1204]),(0,[z380,z30,z3,z4,z5,z6]),(0,[z392,z264,z3,z4,z5,z23]),(0,[z2,z3,z4,z5,z1205,z6])],[(0,[z63,z800,z3,z4,z5,z6]),(0,[z98,z800,z3,z4,z5,z6]),(0,[z1,z236,z3,z4,z379,z6])],[(0,[z1206,z1,z3,z4,z5,z6]),(0,[z1,z1207,z3,z4,z5,z6]),(0,[z1,z3,z1208,z4,z5,z6]),(0,[z1,z2,z3,z4,z1209,z6]),(0,[z1,z2,z3,z839,z5,z6])]],
   [[(0,[z245,z370,z2,z3,z4,z5]),(0,[z1,z3,z1210,z4,z5,z6]),(0,[z1211,z2,z3,z4,z5,z6])],[(0,[z980,z2,z3,z38,z4,z5]),(0,[z245,z2,z3,z4,z71,z5]),(0,[z9,z1,z3,z4,z1212,z6]),(0,[z9,z1,z3,z5,z216,z18]),(0,[z1,z227,z510,z4,z5,z73])],[(0,[z1213,z2,z3,z4,z5,z6]),(0,[z380,z2,z3,z166,z58,z6]),(0,[z1,z131,z3,z91,z5,z6])],[(0,[z1,z1214,z3,z4,z5,z6]),(0,[z380,z3,z45,z4,z5,z6]),(0,[z84,z1,z2,z3,z5,z18])],[(0,[z1,z2,z3,z4,z1212,z6]),(0,[z1215,z2,z3,z4,z5,z6])],[(0,[z1,z800,z3,z4,z5,z6]),(0,[z432,z30,z3,z4,z5,z6]),(0,[z392,z30,z3,z4,z5,z6]),(0,[z1,z1216,z3,z4,z5,z6]),(0,[z1,z1217,z3,z4,z5,z6])],[(0,[z2,z3,z83,z67,z5,z6]),(0,[z9,z1,z3,z5,z6,z18]),(0,[z1,z264,z3,z4,z5,z310]),(0,[z343,z3,z25,z4,z5,z6])],[(0,[z9,z1,z3,z83,z5,z6]),(0,[z1,z3,z4,z5,z937,z6]),(0,[z1,z2,z3,z4,z5,z1218]),(0,[z150,z1,z3,z4,z5,z6]),(0,[z469,z30,z3,z4,z5,z6]),(0,[z469,z2,z3,z4,z5,z651])],[(0,[z401,z19,z3,z4,z5,z6]),(0,[z2,z3,z38,z336,z5,z6]),(0,[z1,z1219,z3,z4,z5,z6]),(0,[z165,z117,z3,z4,z60,z6]),(0,[z40,z1,z45,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1220])],[(0,[z2,z3,z38,z4,z5,z120]),(0,[z1032,z2,z3,z38,z4,z5]),(0,[z1,z45,z4,z339,z5,z6]),(0,[z252,z30,z3,z4,z5,z6]),(0,[z222,z2,z3,z4,z287,z6]),(0,[z243,z1,z3,z5,z6,z18])],[(0,[z168,z3,z4,z5,z562,z6]),(0,[z800,z168,z3,z4,z5,z6]),(0,[z1,z19,z3,z4,z5,z120]),(0,[z1,z2,z3,z1221,z5,z6]),(0,[z1,z2,z3,z80,z379,z6]),(0,[z1,z1222,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1223,z5,z6]),(0,[z392,z3,z45,z4,z5,z6]),(0,[z9,z365,z3,z4,z5,z6])],[],[(0,[z197,z1,z3,z4,z391,z6]),(0,[z9,z1185,z3,z4,z5,z6]),(0,[z1,z11,z59,z4,z12,z6]),(0,[z1,z1224,z3,z4,z5,z6])],[(0,[z2,z3,z38,z91,z5,z92]),(0,[z1,z3,z59,z839,z5,z6])],[(0,[z1,z3,z4,z176,z583,z6]),(0,[z22,z1,z3,z4,z5,z244]),(0,[z1,z1225,z3,z4,z5,z6]),(0,[z2,z3,z1226,z4,z5,z6])]],
   [[(0,[z1,z1227,z3,z4,z5,z6]),(0,[z1228,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z732])],[(0,[z1,z500,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1229]),(0,[z119,z3,z38,z59,z5,z6]),(0,[z7,z2,z3,z378,z5,z6]),(0,[z1,z30,z3,z4,z379,z6]),(0,[z1,z3,z166,z27,z58,z6])],[(0,[z1,z30,z227,z4,z5,z73]),(0,[z1,z3,z4,z5,z6,z1230]),(0,[z1,z1231,z3,z4,z5,z6])],[(0,[z492,z2,z38,z4,z5,z6]),(0,[z3,z38,z59,z4,z5,z307]),(0,[z1,z3,z45,z399,z5,z6]),(0,[z1232,z1,z3,z4,z5,z6]),(0,[z9,z1233,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1234,z5,z6]),(0,[z1,z30,z3,z4,z5,z1024]),(0,[z85,z9,z1,z104,z5,z6]),(0,[z1,z2,z3,z4,z379,z242]),(0,[z1,z11,z292,z4,z12,z6])],[(0,[z2,z3,z38,z16,z5,z6]),(0,[z43,z2,z227,z4,z5,z73]),(0,[z1,z45,z4,z5,z6,z354]),(0,[z1235,z1,z3,z4,z5,z6]),(0,[z1236,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1073,z4,z6]),(0,[z98,z3,z4,z5,z434,z6]),(0,[z1,z1237,z3,z4,z5,z6]),(0,[z1,z3,z1238,z4,z5,z6])],[(0,[z2,z3,z38,z1193,z5,z6]),(0,[z17,z43,z2,z3,z5,z18]),(0,[z1,z1239,z3,z4,z5,z6]),(0,[z1,z3,z45,z4,z379,z6]),(0,[z3,z96,z59,z4,z5,z6]),(0,[z1,z1240,z3,z4,z5,z6]),(0,[z1,z2,z3,z247,z5,z92])],[(0,[z90,z464,z38,z4,z5,z6]),(0,[z2,z3,z38,z4,z5,z366]),(0,[z9,z1,z3,z5,z6,z557]),(0,[z41,z469,z2,z4,z77,z6])],[(0,[z1241,z1,z3,z4,z5,z6]),(0,[z1242,z2,z3,z4,z5,z6])],[(0,[z1,z1243,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1031,z5]),(0,[z43,z829,z3,z4,z5,z6]),(0,[z165,z133,z3,z4,z60,z6]),(0,[z1,z257,z3,z4,z5,z18]),(0,[z94,z30,z3,z4,z5,z6]),(0,[z2,z3,z1244,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1245]),(0,[z1,z2,z4,z5,z6,z792]),(0,[z1,z1246,z3,z4,z5,z6]),(0,[z2,z1247,z3,z4,z5,z6])],[(0,[z452,z2,z3,z141,z5,z6]),(0,[z1,z1248,z3,z4,z5,z6]),(0,[z9,z1,z3,z5,z6,z1102]),(0,[z1,z2,z80,z774,z5,z6])],[(0,[z75,z19,z3,z4,z5,z6]),(0,[z245,z2,z3,z38,z4,z5]),(0,[z1,z3,z511,z4,z176,z6]),(0,[z369,z30,z3,z4,z5,z6])],[(0,[z1,z1249,z3,z4,z5,z6]),(0,[z9,z1,z3,z482,z5,z6]),(0,[z2,z3,z4,z5,z6,z1250])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1251,z5,z6]),(0,[z1,z264,z3,z399,z5,z6]),(0,[z1252,z1,z3,z4,z5,z6])],[(0,[z3,z45,z4,z5,z322,z6]),(0,[z1,z2,z3,z4,z5,z1253])]],
   [[(0,[z43,z2,z266,z4,z5,z6]),(0,[z1,z1254,z3,z4,z5,z6]),(0,[z37,z94,z45,z4,z5,z6]),(0,[z1,z81,z3,z4,z5,z6])],[(0,[z98,z82,z3,z4,z5,z6]),(0,[z188,z2,z3,z4,z323,z6]),(0,[z290,z2,z3,z4,z71,z314]),(0,[z1199,z1,z3,z45,z4,z5]),(0,[z1255,z2,z3,z4,z5,z6]),(0,[z1256,z2,z3,z4,z5,z6])],[(0,[z43,z464,z3,z4,z5,z6]),(0,[z495,z2,z38,z4,z5,z6]),(0,[z24,z1,z2,z3,z289,z5]),(0,[z1,z2,z3,z91,z5,z969])],[(0,[z1,z2,z3,z4,z5,z1257]),(0,[z1,z3,z1258,z4,z5,z6]),(0,[z28,z2,z3,z4,z5,z865]),(0,[z1259,z2,z3,z4,z5,z6]),(0,[z1260,z2,z3,z4,z5,z6]),(0,[z9,z1136,z3,z4,z5,z6]),(0,[z1,z2,z3,z91,z5,z310])],[(0,[z1,z3,z327,z4,z5,z23]),(0,[z1261,z2,z3,z4,z5,z6]),(0,[z1,z270,z4,z5,z77,z6]),(0,[z1,z11,z270,z4,z5,z6]),(0,[z9,z252,z3,z4,z5,z6]),(0,[z125,z2,z3,z4,z5,z86]),(0,[z1,z2,z3,z4,z5,z1262]),(0,[z1,z2,z3,z547,z5,z92])],[(0,[z89,z1,z3,z59,z5,z6]),(0,[z1,z2,z3,z4,z1263,z6]),(0,[z1264,z1,z3,z4,z5,z6]),(0,[z1,z3,z1265,z4,z5,z6]),(0,[z28,z2,z3,z4,z5,z402]),(0,[z1,z3,z634,z14,z5,z6]),(0,[z9,z346,z3,z4,z5,z6]),(0,[z1266,z2,z3,z4,z5,z6]),(0,[z1267,z2,z3,z4,z5,z6])],[(0,[z1,z1268,z3,z4,z5,z6]),(0,[z1269,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1270]),(0,[z1,z1271,z3,z4,z5,z6])],[(0,[z2,z134,z3,z4,z5,z6]),(0,[z1272,z1,z2,z3,z5,z6]),(0,[z2,z490,z38,z4,z5,z6]),(0,[z1,z123,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z23,z208]),(0,[z85,z1,z2,z104,z5,z86]),(0,[z1273,z2,z3,z4,z5,z6]),(0,[z2,z3,z1274,z4,z5,z6])],[(0,[z9,z1,z3,z449,z5,z6]),(0,[z1,z136,z3,z4,z5,z6]),(0,[z99,z2,z3,z4,z60,z6]),(0,[z136,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z889])],[(0,[z90,z2,z345,z38,z4,z5]),(0,[z1,z2,z3,z4,z5,z1003]),(0,[z125,z30,z3,z4,z5,z6]),(0,[z1,z161,z3,z16,z5,z6]),(0,[z1,z2,z3,z5,z92,z969])],[(0,[z43,z2,z602,z4,z5,z6]),(0,[z43,z3,z482,z4,z5,z6]),(0,[z1275,z1,z3,z4,z5,z6]),(0,[z41,z1,z59,z4,z77,z6]),(0,[z1276,z2,z3,z4,z5,z6]),(0,[z1277,z1,z3,z4,z5,z6])],[(0,[z9,z3,z38,z5,z6,z18]),(0,[z257,z3,z38,z4,z5,z6]),(0,[z43,z3,z510,z4,z5,z6]),(0,[z1,z1278,z3,z4,z5,z6]),(0,[z1,z2,z3,z1279,z5,z6])],[(0,[z432,z19,z3,z4,z5,z6]),(0,[z24,z1,z2,z3,z4,z539]),(0,[z1,z3,z399,z5,z6,z110])],[(0,[z1,z30,z3,z4,z5,z735]),(0,[z30,z66,z474,z4,z5,z6]),(0,[z1280,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z723,z6]),(0,[z380,z57,z3,z4,z5,z6])],[(0,[z1,z3,z4,z143,z5,z6]),(0,[z2,z3,z250,z4,z554,z6]),(0,[z1281,z1,z3,z4,z5,z6]),(0,[z30,z3,z4,z5,z74,z6]),(0,[z9,z1,z11,z4,z12,z6]),(0,[z1,z3,z14,z4,z5,z120]),(0,[z1282,z2,z3,z4,z5,z6])],[(0,[z1,z605,z45,z4,z5,z6]),(0,[z380,z9,z3,z4,z5,z6]),(0,[z85,z1,z2,z104,z5,z242])]],
   [[(0,[z1,z2,z3,z1283,z5,z6]),(0,[z9,z3,z4,z5,z899,z6]),(0,[z1,z131,z3,z5,z6,z18])],[(0,[z2,z500,z38,z4,z5,z6]),(0,[z9,z43,z38,z4,z5,z6]),(0,[z245,z2,z3,z4,z5,z163]),(0,[z7,z2,z3,z422,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1284]),(0,[z1,z3,z1285,z4,z5,z6]),(0,[z1286,z1,z3,z4,z5,z6]),(0,[z122,z1,z45,z4,z5,z100]),(0,[z85,z1,z130,z104,z5,z6]),(0,[z1,z2,z3,z289,z539,z6]),(0,[z1,z2,z3,z55,z5,z18])],[(0,[z2,z3,z38,z399,z5,z6]),(0,[z43,z147,z45,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z1287])],[(0,[z1,z19,z3,z399,z5,z6]),(0,[z245,z2,z3,z64,z4,z5]),(0,[z1,z2,z3,z4,z5,z865]),(0,[z1288,z2,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z1263,z6]),(0,[z134,z3,z4,z5,z23,z6]),(0,[z1289,z2,z3,z4,z5,z6]),(0,[z2,z3,z1290,z4,z5,z6])],[(0,[z1291,z2,z3,z4,z5,z6])],[(0,[z19,z3,z4,z5,z615,z6]),(0,[z1,z3,z482,z4,z5,z1002])],[(0,[z2,z3,z38,z4,z379,z6]),(0,[z24,z2,z3,z4,z5,z865]),(0,[z1,z139,z45,z4,z5,z6]),(0,[z137,z230,z3,z4,z5,z6]),(0,[z41,z1,z2,z351,z77,z6]),(0,[z1188,z1,z3,z16,z5,z6])],[(0,[z1,z1292,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z6,z1293]),(0,[z165,z117,z3,z4,z5,z6]),(0,[z1,z1294,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z1006]),(0,[z1295,z2,z3,z4,z5,z6]),(0,[z125,z130,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z865]),(0,[z9,z1,z3,z5,z6,z647]),(0,[z1296,z1,z3,z4,z5,z6]),(0,[z1,z1297,z3,z4,z5,z6])],[(0,[z1298,z1,z3,z4,z5,z6])],[(0,[z43,z3,z4,z5,z6,z531]),(0,[z1,z30,z194,z4,z5,z6]),(0,[z1,z142,z3,z351,z5,z6])],[(0,[z149,z2,z3,z67,z5,z6]),(0,[z1,z3,z1299,z4,z5,z6])],[(0,[z117,z3,z4,z71,z5,z6]),(0,[z2,z3,z4,z5,z865,z196]),(0,[z2,z3,z1300,z4,z5,z6])],[(0,[z1,z1301,z3,z4,z5,z6]),(0,[z9,z1,z3,z839,z5,z6]),(0,[z392,z2,z3,z4,z5,z18]),(0,[z1,z3,z4,z5,z6,z1302]),(0,[z1,z3,z1303,z4,z5,z6])]],
   [[(0,[z264,z3,z38,z4,z5,z23]),(0,[z41,z2,z38,z4,z77,z6]),(0,[z1,z2,z3,z1187,z5,z6]),(0,[z1,z30,z66,z4,z5,z6]),(0,[z255,z3,z4,z33,z5,z6])],[(0,[z1,z3,z1304,z4,z5,z6]),(0,[z1305,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z1306,z5,z6]),(0,[z1307,z2,z3,z4,z5,z6]),(0,[z1308,z2,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z713,z6]),(0,[z1,z3,z1309,z4,z5,z6])],[(0,[z1,z30,z3,z4,z5,z314]),(0,[z1,z3,z1310,z4,z5,z6]),(0,[z85,z1,z4,z192,z5,z6]),(0,[z1,z2,z3,z1168,z4,z5]),(0,[z1,z123,z3,z4,z295,z6]),(0,[z1108,z1,z3,z4,z5,z6])],[(0,[z527,z2,z3,z126,z5,z6]),(0,[z9,z1,z3,z5,z595,z6]),(0,[z24,z30,z3,z4,z5,z196]),(0,[z1,z3,z1311,z4,z5,z6]),(0,[z296,z2,z3,z351,z5,z6]),(0,[z1,z2,z3,z4,z5,z1312])],[(0,[z1313,z2,z3,z4,z5,z6]),(0,[z1,z3,z1314,z4,z5,z6]),(0,[z1,z3,z362,z399,z5,z6]),(0,[z1,z2,z3,z351,z77,z6])],[(0,[z3,z38,z45,z4,z5,z6]),(0,[z1,z2,z3,z1200,z4,z6]),(0,[z43,z2,z3,z4,z5,z314]),(0,[z30,z3,z4,z5,z726,z6]),(0,[z1315,z2,z3,z4,z5,z347])],[(0,[z30,z66,z38,z4,z5,z6]),(0,[z1,z2,z3,z1316,z5,z6]),(0,[z3,z178,z59,z4,z5,z6]),(0,[z1,z3,z221,z59,z5,z6]),(0,[z85,z1,z2,z104,z287,z6]),(0,[z1,z2,z3,z4,z1317,z6]),(0,[z1318,z2,z3,z4,z5,z6]),(0,[z1,z1319,z3,z4,z5,z6]),(0,[z1,z1320,z3,z4,z5,z6]),(0,[z2,z3,z1321,z4,z5,z6])],[(0,[z3,z38,z14,z4,z5,z6]),(0,[z149,z2,z3,z67,z5,z276]),(0,[z170,z3,z59,z4,z5,z6]),(0,[z1322,z3,z45,z4,z5,z6]),(0,[z408,z537,z3,z4,z5,z6])],[(0,[z24,z2,z3,z4,z5,z626]),(0,[z1,z2,z227,z32,z4,z5]),(0,[z313,z82,z3,z4,z5,z6])],[(0,[z2,z3,z38,z4,z5,z1323]),(0,[z3,z38,z4,z5,z27,z6]),(0,[z24,z3,z45,z4,z5,z196]),(0,[z41,z1,z2,z4,z723,z6]),(0,[z122,z1,z2,z4,z295,z100]),(0,[z380,z3,z4,z5,z27,z6]),(0,[z1,z1324,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z880,z6]),(0,[z370,z2,z3,z4,z539,z6]),(0,[z122,z370,z2,z4,z5,z100])],[(0,[z115,z135,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1325]),(0,[z149,z3,z59,z67,z5,z6]),(0,[z1,z3,z1326,z4,z5,z6]),(0,[z370,z2,z3,z289,z5,z6]),(0,[z1,z476,z227,z4,z5,z73]),(0,[z1,z3,z1327,z4,z5,z6])],[(0,[z507,z43,z3,z4,z5,z6]),(0,[z1328,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1329])],[(0,[z158,z1,z3,z4,z50,z6]),(0,[z1272,z1,z3,z45,z5,z6]),(0,[z432,z3,z45,z4,z5,z6]),(0,[z9,z1,z3,z91,z5,z10]),(0,[z1,z3,z4,z1330,z5,z6]),(0,[z68,z9,z1,z3,z4,z97]),(0,[z469,z2,z3,z4,z5,z42])],[(0,[z158,z3,z4,z74,z159,z6]),(0,[z1,z3,z4,z5,z732,z110])]],
   [[(0,[z433,z43,z3,z4,z5,z6]),(0,[z469,z3,z45,z4,z5,z6]),(0,[z9,z1,z1331,z4,z5,z6]),(0,[z1,z3,z977,z289,z5,z6])],[(0,[z1,z257,z3,z4,z5,z6]),(0,[z1,z223,z3,z4,z5,z6]),(0,[z1332,z2,z3,z4,z5,z6])],[(0,[z117,z1,z3,z4,z5,z6]),(0,[z245,z1,z3,z59,z4,z5]),(0,[z1,z3,z1333,z4,z5,z6]),(0,[z252,z3,z45,z4,z5,z6]),(0,[z2,z3,z1334,z4,z5,z6])],[(0,[z63,z500,z3,z4,z5,z6]),(0,[z1,z30,z3,z289,z5,z6]),(0,[z1,z2,z1331,z4,z5,z6]),(0,[z1,z2,z3,z351,z12,z6]),(0,[z369,z438,z3,z4,z5,z6])],[(0,[z19,z3,z256,z4,z5,z6]),(0,[z9,z3,z83,z38,z5,z6]),(0,[z85,z43,z2,z104,z5,z6]),(0,[z1,z2,z3,z4,z5,z1335]),(0,[z1,z2,z3,z4,z5,z1336]),(0,[z1,z2,z3,z4,z5,z120]),(0,[z2,z3,z4,z5,z6,z1337]),(0,[z1,z2,z227,z4,z5,z792])],[(0,[z43,z2,z3,z4,z539,z6]),(0,[z1,z3,z4,z961,z5,z6]),(0,[z1,z2,z3,z4,z5,z1058]),(0,[z1338,z1,z3,z4,z5,z6]),(0,[z85,z1,z270,z4,z5,z6]),(0,[z1,z3,z399,z176,z5,z6]),(0,[z1,z3,z91,z5,z92,z531])],[(0,[z43,z2,z3,z289,z5,z6]),(0,[z9,z1,z3,z4,z5,z235]),(0,[z659,z1,z45,z4,z5,z6]),(0,[z9,z1,z3,z616,z5,z6]),(0,[z22,z1,z3,z4,z5,z138])],[(0,[z2,z3,z1339,z4,z5,z6]),(0,[z1,z2,z623,z80,z5,z6])],[(0,[z158,z3,z38,z4,z159,z6]),(0,[z1,z30,z182,z4,z5,z6]),(0,[z1,z3,z59,z261,z5,z6])],[(0,[z1,z2,z3,z4,z5,z235]),(0,[z1,z3,z443,z4,z5,z120]),(0,[z125,z236,z3,z4,z5,z6]),(0,[z1,z2,z3,z91,z5,z92])],[(0,[z1,z30,z593,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1340]),(0,[z1,z2,z3,z872,z5,z6]),(0,[z1,z3,z45,z819,z5,z6]),(0,[z134,z3,z45,z4,z5,z6]),(0,[z41,z9,z1,z4,z77,z6]),(0,[z49,z1,z3,z35,z59,z6])],[(0,[z346,z2,z3,z4,z5,z6]),(0,[z20,z3,z38,z4,z176,z6])],[(0,[z248,z3,z38,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1341]),(0,[z1,z123,z3,z336,z5,z6]),(0,[z476,z3,z53,z4,z5,z6])],[(0,[z43,z2,z593,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1342]),(0,[z1,z3,z1343,z4,z5,z6])],[(0,[z9,z1,z3,z4,z5,z6]),(0,[z2,z3,z83,z207,z5,z6]),(0,[z1,z1344,z3,z4,z5,z6]),(0,[z1,z30,z3,z5,z6,z840]),(0,[z1,z2,z3,z1345,z5,z6])],[(0,[z222,z2,z3,z4,z5,z6]),(0,[z123,z3,z38,z4,z5,z6]),(0,[z165,z30,z3,z4,z60,z6]),(0,[z1,z3,z1346,z4,z5,z6]),(0,[z1347,z1,z2,z3,z4,z5]),(0,[z1,z3,z4,z1348,z5,z6]),(0,[z49,z1,z3,z35,z36,z6])]],
   [[(0,[z157,z1,z45,z4,z5,z6]),(0,[z1,z2,z3,z16,z5,z6]),(0,[z1,z95,z25,z80,z5,z6]),(0,[z1349,z2,z3,z4,z5,z6])],[(0,[z43,z933,z3,z4,z5,z6]),(0,[z243,z1,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z1012,z6]),(0,[z41,z1,z142,z4,z77,z6]),(0,[z1098,z1,z2,z3,z4,z5]),(0,[z1350,z2,z3,z4,z5,z6])],[(0,[z398,z168,z3,z4,z5,z6]),(0,[z94,z3,z45,z4,z5,z6]),(0,[z1,z3,z482,z80,z5,z6]),(0,[z9,z1,z3,z4,z5,z1257]),(0,[z9,z1,z3,z91,z5,z310]),(0,[z122,z1,z2,z336,z5,z100]),(0,[z1,z2,z3,z4,z5,z366])],[(0,[z1,z198,z3,z4,z5,z384]),(0,[z346,z123,z3,z4,z5,z6]),(0,[z1,z1351,z3,z4,z5,z6])],[(0,[z165,z3,z45,z4,z60,z6]),(0,[z369,z3,z45,z4,z5,z6]),(0,[z2,z3,z1352,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1353]),(0,[z1,z1354,z3,z4,z5,z6]),(0,[z1,z2,z1355,z4,z5,z6]),(0,[z1356,z1,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z5,z1270])],[(0,[z1,z2,z3,z4,z5,z1357]),(0,[z1,z2,z3,z4,z5,z1025])],[(0,[z1,z2,z3,z345,z4,z5]),(0,[z1,z3,z59,z4,z5,z235]),(0,[z9,z1,z3,z59,z5,z307]),(0,[z3,z59,z4,z5,z6,z402]),(0,[z85,z1,z2,z774,z5,z6]),(0,[z578,z1,z2,z3,z4,z97]),(0,[z1,z3,z1358,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1359]),(0,[z2,z3,z345,z53,z4,z5]),(0,[z43,z2,z3,z4,z5,z953]),(0,[z9,z1,z3,z4,z5,z276]),(0,[z1360,z1,z3,z4,z5,z6]),(0,[z9,z3,z474,z4,z5,z6]),(0,[z514,z1,z270,z4,z5,z6])],[(0,[z1,z3,z4,z1361,z5,z6]),(0,[z1,z1362,z3,z4,z5,z6]),(0,[z150,z1,z3,z415,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1363]),(0,[z164,z1,z3,z4,z477,z6]),(0,[z9,z1,z3,z629,z5,z6]),(0,[z1,z2,z622,z80,z5,z6]),(0,[z1,z2,z666,z4,z5,z73])],[(0,[z791,z43,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z276]),(0,[z821,z2,z3,z4,z5,z6]),(0,[z37,z1,z270,z4,z5,z6]),(0,[z30,z3,z4,z5,z322,z6]),(0,[z2,z3,z1364,z4,z5,z6]),(0,[z1,z2,z3,z269,z58,z6])],[(0,[z1,z2,z3,z1365,z5,z6]),(0,[z278,z3,z64,z4,z5,z6]),(0,[z1,z1366,z3,z4,z5,z6]),(0,[z1,z2,z1367,z4,z5,z6]),(0,[z165,z2,z3,z4,z599,z6])],[(0,[z527,z245,z2,z3,z4,z5]),(0,[z24,z136,z3,z4,z5,z6]),(0,[z1,z1368,z3,z4,z5,z6]),(0,[z2,z1135,z3,z4,z5,z6]),(0,[z1,z30,z3,z5,z6,z129]),(0,[z1,z119,z3,z59,z5,z6])],[(0,[z150,z3,z38,z4,z5,z6]),(0,[z476,z3,z38,z4,z5,z6]),(0,[z1369,z1,z3,z4,z5,z6]),(0,[z24,z2,z3,z4,z5,z276]),(0,[z1,z3,z59,z16,z5,z6]),(0,[z125,z2,z3,z4,z5,z242])]],
   [[(0,[z1,z3,z59,z4,z5,z6]),(0,[z1,z2,z841,z4,z5,z6]),(0,[z43,z30,z45,z4,z5,z6]),(0,[z7,z2,z3,z132,z5,z6]),(0,[z1,z2,z3,z4,z5,z1370]),(0,[z2,z3,z1371,z4,z5,z6]),(0,[z1,z2,z3,z774,z5,z6]),(0,[z1,z223,z95,z80,z5,z6])],[(0,[z43,z2,z3,z5,z6,z129]),(0,[z1372,z2,z3,z4,z5,z6])],[(0,[z1,z776,z3,z4,z5,z6]),(0,[z799,z43,z3,z4,z5,z6]),(0,[z1,z3,z4,z1373,z5,z6]),(0,[z125,z3,z45,z4,z5,z6]),(0,[z41,z1,z2,z4,z77,z651]),(0,[z1,z1374,z3,z4,z5,z6])],[(0,[z1375,z1,z3,z4,z5,z6]),(0,[z9,z3,z5,z6,z167,z18])],[(0,[z763,z1,z2,z3,z4,z6]),(0,[z43,z133,z3,z4,z5,z6]),(0,[z37,z1,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1376])],[(0,[z1377,z2,z3,z4,z5,z6]),(0,[z1378,z2,z3,z4,z5,z6]),(0,[z133,z3,z38,z4,z5,z6]),(0,[z22,z1,z3,z4,z5,z151]),(0,[z1,z2,z3,z4,z5,z1379]),(0,[z1380,z2,z3,z4,z5,z6])],[(0,[z245,z1,z30,z3,z4,z5]),(0,[z1381,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1382]),(0,[z1,z3,z59,z4,z5,z1357])],[(0,[z245,z3,z38,z59,z4,z5]),(0,[z117,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z1383,z5,z6]),(0,[z1,z3,z292,z4,z5,z6]),(0,[z1,z142,z3,z4,z5,z651]),(0,[z1384,z2,z3,z4,z5,z6])],[(0,[z542,z2,z38,z4,z5,z6]),(0,[z7,z2,z3,z44,z5,z6]),(0,[z1,z1385,z3,z4,z5,z6]),(0,[z343,z30,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1386])],[(0,[z3,z38,z4,z5,z6,z138]),(0,[z1,z3,z72,z4,z583,z6]),(0,[z1116,z2,z3,z4,z5,z6]),(0,[z1,z3,z1387,z4,z5,z6])],[(0,[z43,z142,z3,z4,z5,z6]),(0,[z1,z1388,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z295,z6]),(0,[z1,z2,z3,z104,z5,z242])],[(0,[z3,z345,z38,z59,z4,z5]),(0,[z150,z149,z1,z3,z5,z6]),(0,[z1,z3,z59,z4,z5,z276]),(0,[z1,z30,z3,z351,z5,z6]),(0,[z1,z2,z3,z351,z5,z651]),(0,[z1,z3,z1389,z4,z5,z6]),(0,[z1390,z2,z3,z4,z5,z6]),(0,[z1391,z2,z3,z4,z5,z6])],[(0,[z43,z3,z4,z5,z6,z153]),(0,[z24,z2,z3,z4,z5,z402]),(0,[z3,z45,z1056,z4,z5,z6]),(0,[z365,z30,z3,z4,z5,z6]),(0,[z1,z139,z14,z4,z5,z6]),(0,[z1392,z1,z3,z4,z5,z6])],[(0,[z1393,z2,z3,z4,z5,z6]),(0,[z1,z294,z3,z4,z5,z6]),(0,[z9,z1,z95,z80,z5,z6]),(0,[z9,z1,z3,z5,z6,z648]),(0,[z1,z2,z3,z4,z295,z6]),(0,[z1,z3,z4,z1394,z5,z6])],[(0,[z2,z3,z38,z1395,z5,z6]),(0,[z3,z38,z4,z143,z5,z6]),(0,[z245,z2,z3,z67,z4,z5]),(0,[z43,z2,z3,z351,z5,z6]),(0,[z43,z359,z3,z4,z5,z6]),(0,[z1,z3,z1396,z4,z5,z6]),(0,[z343,z3,z45,z4,z5,z6]),(0,[z1,z130,z3,z4,z5,z86]),(0,[z2,z3,z4,z5,z322,z945])],[(0,[z2,z200,z3,z4,z5,z8]),(0,[z2,z3,z1397,z4,z5,z6]),(0,[z7,z3,z59,z132,z5,z6]),(0,[z2,z3,z4,z5,z6,z402]),(0,[z425,z1,z3,z4,z411,z6]),(0,[z296,z30,z3,z4,z5,z6]),(0,[z296,z2,z3,z4,z5,z651])]],
   [[(0,[z3,z38,z36,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1398]),(0,[z1399,z2,z3,z4,z5,z6]),(0,[z408,z30,z3,z4,z5,z6]),(0,[z3,z744,z59,z4,z5,z6]),(0,[z1,z2,z95,z80,z5,z6])],[(0,[z1400,z1,z2,z3,z5,z6]),(0,[z2,z3,z38,z4,z5,z833]),(0,[z2,z3,z4,z872,z5,z6]),(0,[z1,z1401,z3,z4,z5,z6])],[(0,[z2,z590,z38,z4,z5,z6]),(0,[z49,z43,z2,z3,z35,z6]),(0,[z1,z1034,z3,z4,z5,z6]),(0,[z1,z1402,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1403]),(0,[z1,z3,z1404,z4,z5,z6]),(0,[z365,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z289,z5,z73])],[(0,[z9,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1405]),(0,[z1,z2,z3,z4,z5,z1406]),(0,[z296,z142,z3,z4,z5,z6])],[(0,[z469,z161,z3,z4,z5,z6])],[(0,[z115,z3,z101,z4,z5,z6]),(0,[z986,z1,z3,z4,z5,z6]),(0,[z1,z3,z1407,z4,z5,z6])],[(0,[z243,z3,z38,z4,z5,z6]),(0,[z43,z130,z3,z4,z5,z6]),(0,[z1,z2,z1408,z4,z5,z6]),(0,[z2,z3,z4,z880,z60,z6]),(0,[z2,z3,z4,z5,z6,z1409]),(0,[z252,z2,z3,z4,z5,z18])],[(0,[z229,z3,z38,z4,z5,z6]),(0,[z17,z1,z3,z45,z5,z18]),(0,[z125,z2,z3,z4,z287,z6]),(0,[z49,z1,z81,z3,z35,z6]),(0,[z1,z2,z3,z5,z6,z969])],[(0,[z1,z131,z3,z4,z5,z6]),(0,[z1116,z3,z59,z4,z5,z6]),(0,[z1410,z2,z3,z4,z5,z6])],[(0,[z9,z43,z3,z59,z5,z6]),(0,[z1,z1131,z3,z4,z5,z6]),(0,[z1,z3,z890,z4,z5,z6]),(0,[z114,z3,z64,z4,z5,z6]),(0,[z22,z1,z2,z3,z5,z129]),(0,[z1,z3,z1411,z4,z5,z6])],[(0,[z43,z2,z685,z4,z5,z6]),(0,[z400,z2,z3,z4,z5,z70]),(0,[z43,z3,z25,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1102])],[(0,[z63,z168,z3,z4,z5,z6]),(0,[z1,z1412,z3,z4,z5,z6])],[(0,[z1,z3,z45,z4,z5,z314]),(0,[z1,z2,z3,z4,z5,z1413]),(0,[z1414,z1,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z295,z6])],[(0,[z1,z3,z1415,z4,z5,z6])],[(0,[z43,z2,z689,z4,z5,z6]),(0,[z68,z43,z2,z3,z4,z97]),(0,[z1,z1416,z3,z4,z5,z6]),(0,[z1063,z1,z2,z3,z4,z5]),(0,[z1417,z1,z3,z4,z5,z6])],[(0,[z1,z3,z1418,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z790]),(0,[z9,z1,z3,z4,z5,z1419]),(0,[z1,z3,z4,z5,z908,z347]),(0,[z1,z2,z3,z5,z969,z18])]],
   [[(0,[z1,z3,z820,z4,z5,z6])],[(0,[z165,z9,z3,z4,z60,z6]),(0,[z9,z392,z3,z4,z5,z6]),(0,[z3,z178,z292,z4,z5,z6])],[(0,[z1,z326,z3,z4,z5,z6]),(0,[z237,z1,z3,z4,z159,z6]),(0,[z43,z2,z345,z38,z4,z5]),(0,[z1,z2,z3,z4,z5,z1419])],[(0,[z1,z1152,z3,z4,z5,z6]),(0,[z28,z2,z3,z53,z4,z5]),(0,[z9,z1,z3,z336,z5,z6])],[(0,[z1,z1009,z3,z4,z5,z6]),(0,[z290,z30,z3,z4,z71,z6]),(0,[z9,z1,z3,z4,z5,z120]),(0,[z264,z134,z3,z4,z5,z23])],[(0,[z1,z2,z3,z4,z5,z1323]),(0,[z165,z2,z3,z4,z5,z155]),(0,[z1,z30,z3,z4,z539,z6]),(0,[z2,z3,z1420,z4,z5,z6]),(0,[z1,z2,z3,z289,z5,z100]),(0,[z2,z3,z166,z322,z58,z6])],[(0,[z2,z3,z38,z4,z5,z735]),(0,[z1,z1161,z3,z4,z5,z6]),(0,[z1,z1421,z3,z4,z5,z6]),(0,[z1,z2,z3,z336,z5,z6]),(0,[z1422,z1,z3,z4,z5,z6])],[(0,[z1,z3,z512,z4,z5,z120])],[(0,[z150,z1,z3,z35,z5,z6])],[(0,[z2,z3,z345,z38,z4,z5]),(0,[z1,z1423,z3,z4,z5,z6]),(0,[z1424,z2,z3,z4,z5,z6]),(0,[z263,z1,z3,z4,z5,z310]),(0,[z9,z1,z3,z91,z5,z92]),(0,[z1,z294,z3,z4,z295,z6])],[(0,[z41,z43,z2,z4,z77,z6]),(0,[z2,z3,z872,z132,z5,z6]),(0,[z7,z433,z3,z132,z5,z6]),(0,[z3,z474,z45,z4,z5,z6]),(0,[z1,z1425,z3,z4,z5,z6])],[(0,[z763,z1,z3,z45,z4,z6]),(0,[z1,z3,z45,z4,z539,z6]),(0,[z9,z1,z3,z269,z5,z6]),(0,[z1,z2,z3,z4,z723,z6])],[(0,[z1,z2,z3,z4,z1426,z6]),(0,[z1,z3,z45,z289,z5,z6]),(0,[z1,z2,z3,z4,z1427,z6])],[(0,[z478,z168,z3,z4,z5,z6]),(0,[z1428,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z23,z307])],[(0,[z1,z3,z4,z5,z138,z307]),(0,[z1429,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z732])],[(0,[z1,z2,z3,z4,z5,z1430]),(0,[z2,z1431,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1432,z6])]],
   [[(0,[z57,z43,z3,z4,z5,z6]),(0,[z1,z2,z3,z1179,z5,z6]),(0,[z9,z1,z3,z16,z5,z6]),(0,[z9,z1,z3,z302,z5,z6]),(0,[z369,z2,z11,z4,z12,z6])],[(0,[z1433,z1,z3,z4,z5,z6]),(0,[z1,z1434,z3,z4,z5,z6]),(0,[z1,z3,z5,z6,z138,z129])],[(0,[z1,z3,z1435,z4,z5,z6]),(0,[z1436,z1,z3,z4,z5,z6]),(0,[z1437,z2,z3,z4,z5,z6]),(0,[z507,z1,z3,z4,z5,z18]),(0,[z1,z3,z1438,z4,z5,z6])],[(0,[z1,z3,z4,z5,z445,z6]),(0,[z1,z416,z45,z4,z5,z6]),(0,[z1272,z2,z3,z38,z5,z6]),(0,[z1172,z2,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z5,z366]),(0,[z3,z53,z59,z4,z5,z6]),(0,[z1,z1439,z3,z4,z5,z6]),(0,[z17,z1,z2,z3,z5,z18]),(0,[z68,z1,z3,z4,z153,z97])],[(0,[z90,z248,z38,z4,z5,z6]),(0,[z1,z3,z1440,z4,z5,z6]),(0,[z9,z3,z4,z5,z6,z167]),(0,[z1,z119,z3,z59,z5,z120]),(0,[z2,z3,z4,z5,z1441,z6])],[(0,[z1,z2,z3,z1193,z5,z6]),(0,[z43,z3,z4,z192,z5,z6]),(0,[z9,z51,z1,z3,z5,z6]),(0,[z2,z3,z1442,z4,z5,z6]),(0,[z1,z3,z59,z336,z5,z6]),(0,[z1,z3,z59,z5,z6,z56]),(0,[z1443,z2,z3,z4,z5,z6]),(0,[z1,z264,z2,z3,z5,z129]),(0,[z1,z2,z3,z1444,z4,z6]),(0,[z2,z3,z1445,z4,z5,z6])],[(0,[z2,z526,z38,z4,z5,z6]),(0,[z1,z653,z45,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z120]),(0,[z435,z1,z2,z3,z5,z18])],[(0,[z28,z370,z2,z3,z4,z5]),(0,[z1,z30,z15,z4,z5,z6]),(0,[z1446,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1025,z97])],[(0,[z504,z2,z38,z4,z5,z6]),(0,[z9,z1,z3,z345,z4,z5]),(0,[z1,z3,z762,z4,z5,z6]),(0,[z1,z1447,z3,z4,z5,z6]),(0,[z9,z1,z3,z436,z5,z6]),(0,[z9,z3,z178,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z969])],[(0,[z2,z3,z1448,z4,z5,z6]),(0,[z131,z3,z38,z4,z5,z6]),(0,[z9,z1,z3,z4,z5,z1359]),(0,[z1449,z1,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z1450,z6]),(0,[z9,z3,z96,z4,z5,z6]),(0,[z1,z3,z1451,z4,z5,z6])],[(0,[z43,z2,z21,z4,z5,z6]),(0,[z1,z2,z890,z4,z5,z6]),(0,[z84,z1,z3,z4,z5,z10]),(0,[z1,z3,z59,z91,z5,z92]),(0,[z1,z2,z3,z1452,z5,z6]),(0,[z1,z3,z4,z1453,z5,z6])],[(0,[z2,z3,z38,z4,z5,z314]),(0,[z3,z59,z4,z5,z74,z6])],[(0,[z2,z3,z1454,z4,z5,z6]),(0,[z43,z2,z640,z4,z5,z6]),(0,[z1,z1455,z3,z4,z5,z6]),(0,[z149,z229,z3,z67,z5,z6]),(0,[z1,z3,z1456,z4,z5,z6]),(0,[z346,z3,z59,z4,z5,z6]),(0,[z3,z59,z4,z5,z1132,z307]),(0,[z1,z2,z4,z723,z77,z6])],[(0,[z9,z1,z3,z112,z5,z6]),(0,[z43,z248,z3,z4,z5,z6]),(0,[z24,z2,z3,z345,z4,z5]),(0,[z1233,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z839,z5,z6])],[(0,[z90,z30,z38,z4,z5,z6]),(0,[z37,z38,z45,z4,z5,z6]),(0,[z43,z2,z32,z4,z5,z6]),(0,[z1,z2,z3,z4,z1457,z6]),(0,[z370,z30,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1458]),(0,[z2,z3,z1459,z4,z5,z6]),(0,[z381,z1,z2,z4,z5,z100])]],
   [[(0,[z1460,z1,z3,z4,z5,z6]),(0,[z1,z3,z1461,z4,z5,z6])],[(0,[z724,z3,z38,z4,z5,z6]),(0,[z43,z264,z3,z4,z5,z23]),(0,[z1,z2,z3,z4,z1462,z6]),(0,[z1,z1463,z3,z4,z5,z6]),(0,[z380,z2,z3,z4,z5,z6]),(0,[z972,z30,z3,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z86]),(0,[z222,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z4,z753,z6]),(0,[z1,z2,z3,z4,z5,z1464]),(0,[z1,z3,z1105,z4,z5,z6]),(0,[z1,z2,z567,z4,z5,z73]),(0,[z1,z1465,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z1466,z6]),(0,[z22,z1,z3,z4,z5,z307]),(0,[z1,z294,z3,z336,z5,z6]),(0,[z1,z2,z3,z336,z295,z6])],[(0,[z1,z1467,z3,z4,z5,z6]),(0,[z1,z1468,z3,z4,z5,z6]),(0,[z1322,z2,z3,z4,z5,z6]),(0,[z9,z3,z53,z4,z5,z6])],[(0,[z1,z3,z345,z45,z4,z5]),(0,[z43,z2,z3,z4,z5,z86]),(0,[z1,z1469,z3,z4,z5,z6]),(0,[z1443,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z1470,z5,z6]),(0,[z1,z1471,z3,z4,z5,z6]),(0,[z1,z3,z1472,z4,z5,z6])],[(0,[z1,z280,z3,z4,z5,z6]),(0,[z63,z230,z3,z4,z5,z6]),(0,[z1,z3,z59,z4,z5,z366]),(0,[z1,z264,z3,z4,z5,z138])],[(0,[z1,z3,z385,z4,z5,z6]),(0,[z245,z2,z3,z4,z554,z5]),(0,[z9,z28,z3,z4,z5,z8]),(0,[z1,z30,z3,z4,z5,z651]),(0,[z1473,z1,z3,z4,z5,z6]),(0,[z365,z476,z3,z4,z5,z6])],[(0,[z43,z3,z270,z4,z5,z6]),(0,[z1,z3,z45,z5,z6,z129]),(0,[z398,z493,z3,z4,z5,z6]),(0,[z1,z3,z1474,z4,z5,z6]),(0,[z1,z1475,z3,z4,z5,z6]),(0,[z1,z2,z3,z1476,z5,z6])],[(0,[z1,z2,z3,z4,z1477,z6]),(0,[z2,z3,z4,z5,z6,z1478]),(0,[z1,z3,z1479,z4,z5,z6])],[(0,[z432,z2,z3,z4,z5,z6]),(0,[z392,z2,z3,z4,z5,z6]),(0,[z43,z30,z3,z4,z5,z6]),(0,[z245,z28,z2,z3,z4,z5]),(0,[z471,z2,z3,z44,z5,z6]),(0,[z43,z2,z3,z4,z5,z651]),(0,[z41,z1,z2,z4,z77,z42])],[(0,[z667,z1,z3,z512,z4,z6]),(0,[z346,z294,z3,z4,z5,z6]),(0,[z346,z2,z3,z4,z295,z6])],[(0,[z469,z2,z3,z4,z5,z6]),(0,[z2,z3,z38,z4,z539,z6]),(0,[z1,z30,z3,z4,z5,z155]),(0,[z24,z370,z2,z3,z4,z5])],[(0,[z1480,z2,z3,z4,z5,z6]),(0,[z2,z3,z38,z289,z5,z6]),(0,[z43,z2,z3,z4,z5,z242]),(0,[z1,z30,z683,z4,z5,z6]),(0,[z1481,z1,z3,z4,z5,z6])],[(0,[z252,z2,z3,z4,z5,z6]),(0,[z1,z3,z1482,z4,z5,z6]),(0,[z1,z3,z4,z103,z5,z6]),(0,[z1,z30,z3,z4,z5,z307]),(0,[z1,z2,z3,z1483,z5,z6]),(0,[z1,z1484,z3,z4,z5,z6])],[(0,[z2,z3,z38,z4,z5,z919]),(0,[z43,z2,z3,z4,z5,z155]),(0,[z150,z1,z3,z59,z5,z6]),(0,[z9,z1,z3,z399,z5,z6]),(0,[z9,z370,z3,z4,z5,z6]),(0,[z1485,z2,z3,z4,z5,z6]),(0,[z1,z142,z3,z4,z5,z42]),(0,[z252,z507,z3,z4,z5,z6])],[(0,[z43,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1486])]],
   [[(0,[z3,z38,z59,z4,z5,z6]),(0,[z43,z2,z3,z4,z5,z307]),(0,[z1487,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z1488,z5,z6]),(0,[z1,z3,z1489,z4,z5,z6]),(0,[z380,z3,z59,z4,z5,z6]),(0,[z1490,z1,z3,z4,z5,z6]),(0,[z57,z1,z3,z166,z58,z6])],[(0,[z1,z30,z88,z4,z5,z6]),(0,[z122,z1,z30,z4,z5,z100]),(0,[z1,z2,z3,z399,z5,z6]),(0,[z1491,z2,z3,z4,z5,z6]),(0,[z1,z1492,z3,z4,z5,z6]),(0,[z408,z2,z3,z4,z5,z97])],[(0,[z1,z1493,z3,z4,z5,z6]),(0,[z1,z671,z45,z4,z5,z6]),(0,[z9,z1,z3,z4,z379,z6]),(0,[z1,z2,z3,z351,z5,z42]),(0,[z122,z1,z294,z4,z5,z100]),(0,[z1,z1494,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1121]),(0,[z1,z3,z1495,z4,z5,z6]),(0,[z1,z2,z3,z342,z58,z6]),(0,[z1,z131,z3,z91,z5,z92])],[(0,[z1,z3,z45,z351,z5,z6]),(0,[z2,z3,z4,z5,z1132,z307]),(0,[z1,z1496,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z539,z73])],[(0,[z1,z3,z4,z1497,z5,z6]),(0,[z1,z3,z511,z4,z318,z6]),(0,[z1,z30,z3,z4,z5,z1002]),(0,[z1,z2,z3,z4,z379,z6])],[(0,[z1,z3,z1498,z4,z5,z6]),(0,[z158,z432,z3,z4,z159,z6]),(0,[z296,z2,z3,z4,z5,z42]),(0,[z1,z2,z227,z4,z5,z73]),(0,[z1315,z2,z3,z4,z5,z6])],[(0,[z3,z38,z292,z4,z5,z6]),(0,[z1,z2,z3,z4,z77,z42])],[(0,[z1,z168,z3,z4,z5,z120]),(0,[z30,z38,z45,z4,z5,z6]),(0,[z296,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1024]),(0,[z1,z3,z755,z59,z4,z6]),(0,[z432,z3,z59,z4,z5,z6]),(0,[z392,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1499])],[(0,[z1,z2,z3,z1395,z5,z6]),(0,[z1,z2,z3,z4,z6,z1500]),(0,[z408,z3,z45,z4,z5,z6]),(0,[z1,z3,z1501,z4,z5,z6]),(0,[z1,z130,z3,z4,z5,z242])],[(0,[z1502,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z1503,z6]),(0,[z469,z3,z59,z4,z5,z6])],[(0,[z90,z38,z45,z4,z5,z6]),(0,[z1504,z1,z3,z4,z5,z6])],[(0,[z43,z2,z106,z4,z5,z6]),(0,[z2,z3,z1505,z4,z5,z6]),(0,[z1,z3,z4,z5,z120,z307]),(0,[z1,z2,z3,z4,z287,z86])],[(0,[z1,z1506,z3,z4,z5,z6]),(0,[z1,z3,z958,z4,z5,z6]),(0,[z719,z1,z3,z4,z5,z6]),(0,[z1507,z2,z3,z4,z5,z6]),(0,[z1,z123,z3,z289,z5,z6])],[(0,[z94,z2,z3,z4,z5,z6]),(0,[z1,z1508,z3,z4,z5,z6]),(0,[z1,z3,z1509,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z861]),(0,[z1,z3,z4,z176,z6,z177]),(0,[z1148,z1,z3,z4,z5,z6])],[(0,[z43,z3,z59,z4,z5,z307]),(0,[z1510,z1,z3,z4,z5,z6]),(0,[z1,z1511,z3,z4,z5,z6]),(0,[z3,z45,z4,z5,z6,z167]),(0,[z1,z2,z3,z4,z5,z731])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 489) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 489).take 485) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 974).take 486) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1460).take 136) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1596)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [489, 485, 486, 136] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 122).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 122).take 120).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 242).take 123).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 365).take 112).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 477).take 35).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [122, 120, 123, 112, 35] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38591

theorem PEqualNP.Outside.L_meta_38591 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677352 * 2 ^ 32 + 4008225448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677352 * 2 ^ 32 + 4008225448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38591.solve