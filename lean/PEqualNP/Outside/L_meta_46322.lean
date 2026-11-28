import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46322

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
  Nat.testBit (4278124266 * 2 ^ 32 + 4276809440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00400000a0052310#64 ++ 0x600400000a005231#64 ++ 0xbbb20413e09f673f#64 ++ 0x7bbb20413e09f673#64 : BitVec 256),
   (0x28801825812c2940#64 ++ 0x428801825812c294#64 ++ 0x7774386d836cb9ce#64 ++ 0xf7774386d836cb9c#64 : BitVec 256),
   (0x4300c18a0c50c0a4#64 ++ 0x84300c18a0c50c0a#64 ++ 0xeee9c38e1c70c1fd#64 ++ 0xeeee9c38e1c70c1f#64 : BitVec 256),
   (0x920e02d01680d401#64 ++ 0x1920e02d01680d40#64 ++ 0xe1fe03f01f80fe0b#64 ++ 0xde1fe03f01f80fe0#64 : BitVec 256),
   (0x1c0f6c001bfa0006#64 ++ 0x11c0f6c001bfa000#64 ++ 0x1feffc001fff0007#64 ++ 0xc1feffc001fff000#64 : BitVec 256),
   (0xe00fb77f40000008#64 ++ 0x1e00fb77f4000000#64 ++ 0xffefffffe0000000#64 ++ 0x3ffefffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x8082001000804601 0x0808200100080460

def z1 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbbb20413e09f673f 0x7bbb20413e09f673

def z2 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1feffc001fff0007 0xc1feffc001fff000

def z3 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7774386d836cb9ce 0xf7774386d836cb9c

def z4 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeee9c38e1c70c1fd 0xeeee9c38e1c70c1f

def z5 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe1fe03f01f80fe0b 0xde1fe03f01f80fe0

def z6 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe0000000 0x3ffefffffe000000

def z7 : W := mkw 0x0040000020010210 0x2004000002001021 0x8882041260934631 0x0888204126093463

def z8 : W := mkw 0x00400000a0052310 0x600400000a005231 0x1a000403e01f0134 0x21a000403e01f013

def z9 : W := mkw 0x0000400008500004 0x0000040000850000 0x0ee9c0001c700005 0xc0ee9c0001c70000

def z10 : W := mkw 0x5f0fed8a1ffac0a6 0x95f0fed8a1ffac0a 0xffefff8e1fffc1ff 0xeffefff8e1fffc1f

def z11 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000009f0007 0x400000000009f000

def z12 : W := mkw 0x4140c10aa85523b4 0xe4140c10aa85523b 0x1e01c40fe07f01f4 0x21e01c40fe07f01f

def z13 : W := mkw 0x4100c10a085000a4 0x84100c10a085000a 0x0401c00c006000c0 0x00401c00c006000c

def z14 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x7f743c6fe37fb9fe 0xf7f743c6fe37fb9f

def z15 : W := mkw 0x3c8f7c259bfe2946 0x53c8f7c259bfe294 0x7ffffc6d9fffb9cf 0xf7ffffc6d9fffb9c

def z16 : W := mkw 0x9e0f6ed01ffad407 0x19e0f6ed01ffad40 0xfffffff01ffffe0f 0xdfffffff01ffffe0

def z17 : W := mkw 0x00400000a0052310 0x600400000a005231 0xb1120413e08f673a 0x3b1120413e08f673

def z18 : W := mkw 0x08800800812c2940 0x408800800812c294 0x17743800036cb9ce 0xc17743800036cb9c

def z19 : W := mkw 0x924e02d0b685f711 0x7924e02d0b685f71 0xfbfe07f3ff9fff3f 0xffbfe07f3ff9fff3

def z20 : W := mkw 0x800e025000000000 0x1800e02500000000 0xe1fe03f00080660b 0x5e1fe03f00080660

def z21 : W := mkw 0x00400000a0052310 0x600400000a005231 0x33300001809f673f 0x733300001809f673

def z22 : W := mkw 0x9c0f6e501bfa1407 0x19c0f6e501bfa140 0x1ffffc701fff3e07 0xd1ffffc701fff3e0

def z23 : W := mkw 0x00400000a0052310 0x600400000a005231 0xa0100013e0006738 0x3a0100013e000673

def z24 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xf774387fe36cfffe 0xff774387fe36cfff

def z25 : W := mkw 0x0040000020010210 0x2004000002001021 0x0000000000934631 0x0000000000093463

def z26 : W := mkw 0x0000000000000000 0x0000000000000000 0xbba20413e0000000 0x3bba20413e000000

def z27 : W := mkw 0x00400000a0052310 0x600400000a005231 0x00100000009f673f 0x400100000009f673

def z28 : W := mkw 0x2000102500000000 0x0200010250000000 0x6000006d80000000 0x36000006d8000000

def z29 : W := mkw 0xfc8fff7fdbfe294e 0x5fc8fff7fdbfe294 0xffffffffffffb9cf 0xfffffffffffffb9c

def z30 : W := mkw 0xe000937f40000008 0x0e000937f4000000 0xeee9c3ffe0000000 0x3eee9c3ffe000000

def z31 : W := mkw 0xe20fb7ff4400d409 0x1e20fb7ff4400d40 0xffffffffe000fe08 0x3ffffffffe000fe0

def z32 : W := mkw 0x2880182501280840 0x0288018250128084 0x5764386c036c98c6 0xc5764386c036c98c

def z33 : W := mkw 0x920e02d09684f501 0x5920e02d09684f50 0xf3fe03f19f8cff0f 0xff3fe03f19f8cff0

def z34 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xfff63c7fe3ffffff 0xffff63c7fe3fffff

def z35 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x808a03901c804601 0x0808a03901c80460

def z36 : W := mkw 0x0000400008500004 0x0000040000850000 0x0e01c00000700004 0x00e01c0000070000

def z37 : W := mkw 0x100e000012800000 0x1100e00001280000 0x01ee00001f800003 0xc01ee00001f80000

def z38 : W := mkw 0x6b80d9af8d7ce9e4 0xc6b80d9af8d7ce9e 0xfee9fb8f9c7cc1fd 0xefee9fb8f9c7cc1f

def z39 : W := mkw 0x4000810a00000000 0x04000810a0000000 0x0e01c00e00000000 0x20e01c00e0000000

def z40 : W := mkw 0x0c016c00097a0006 0x00c016c00097a000 0x1ee9fc001c7f0005 0xc1ee9fc001c7f000

def z41 : W := mkw 0x1c0048001bfa0006 0x01c0048001bfa000 0x000000001fff0007 0xc000000001fff000

def z42 : W := mkw 0x4000810a00000000 0x04000810a0000000 0xffebc79fe0000000 0x3ffebc79fe000000

def z43 : W := mkw 0x28801825812c2940 0x428801825812c294 0x11143861830c3802 0x111143861830c380

def z44 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x8889c3821c104031 0x08889c3821c10403

def z45 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe010413d 0x7ffefffffe010413

def z46 : W := mkw 0x0c016c00097a0006 0x00c016c00097a000 0x1e01fc00007f0004 0x01e01fc00007f000

def z47 : W := mkw 0xe00fb77fc0042108 0x5e00fb77fc004210 0xffffffffe00c210e 0x7ffffffffe00c210

def z48 : W := mkw 0x0800080001280000 0x0080008000128000 0x11043800030c0002 0x011043800030c000

def z49 : W := mkw 0x0000000080042100 0x4000000008004210 0x3bb20401809f210f 0x73bb20401809f210

def z50 : W := mkw 0x000f240000000000 0x1000f24000000000 0x1feffc0000000000 0x01feffc000000000

def z51 : W := mkw 0xfc0fff7f5bfa000e 0x1fc0fff7f5bfa000 0xffefffffffff0007 0xfffefffffffff000

def z52 : W := mkw 0x00400000a0052310 0x600400000a005231 0xfff2041fe0ffe7ff 0xffff2041fe0ffe7f

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0x0882040000930001 0x0088204000093000

def z54 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe09f0007 0x7ffefffffe09f000

def z55 : W := mkw 0x2880182501280840 0x0288018250128084 0x4444386c036098c0 0x84444386c036098c

def z56 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xa1ba03901c80660b 0x5a1ba03901c80660

def z57 : W := mkw 0x800e025000000000 0x1800e02500000000 0xfbee07f3e0000000 0x3fbee07f3e000000

def z58 : W := mkw 0x900e025012801401 0x1900e02501280140 0x01fe00701f803e03 0xd01fe00701f803e0

def z59 : W := mkw 0x0b8048808d7ce9e4 0xc0b8048808d7ce9e 0x001000001f7cf9ff 0xc001000001f7cf9f

def z60 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7660380d806c81cc 0xe7660380d806c81c

def z61 : W := mkw 0x4340c18aac55e3b4 0xe4340c18aac55e3b 0xeef9c38e1cffe7ff 0xeeef9c38e1cffe7f

def z62 : W := mkw 0x4000810a00000000 0x04000810a0000000 0xeee9c38e00000000 0x2eee9c38e0000000

def z63 : W := mkw 0xa00f367540000008 0x1a00f36754000000 0x11063c71e0000000 0x111063c71e000000

def z64 : W := mkw 0xa00f367540000008 0x1a00f36754000000 0xbba63c73e0000000 0x3bba63c73e000000

def z65 : W := mkw 0x6001b52f40000008 0x06001b52f4000000 0xfee9ff8fe0000000 0x2fee9ff8fe000000

def z66 : W := mkw 0xe20093ff4400d409 0x0e20093ff4400d40 0xe01003ffe000fe08 0x3e01003ffe000fe0

def z67 : W := mkw 0xd20fa7da5680d409 0x1d20fa7da5680d40 0x888bc7927c804601 0x0888bc7927c80460

def z68 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xe44dfbffe0000000 0x3e44dfbffe000000

def z69 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x000803801c000000 0x0000803801c00000

def z70 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x0eedf8001f700005 0xc0eedf8001f70000

def z71 : W := mkw 0x08800800812c2940 0x408800800812c294 0x33300001836cb9ce 0xf33300001836cb9c

def z72 : W := mkw 0xf00fb77f52801409 0x1f00fb77f5280140 0xffffffffe3803e02 0x3ffffffffe3803e0

def z73 : W := mkw 0x2000102500000000 0x0200010250000000 0xffe63c7fe0000000 0x3ffe63c7fe000000

def z74 : W := mkw 0x28801825812c2940 0x428801825812c294 0xfff4386f837cf9ff 0xffff4386f837cf9f

def z75 : W := mkw 0x820002d00400d401 0x0820002d00400d40 0xe01003f00000fe08 0x1e01003f00000fe0

def z76 : W := mkw 0x638091af8404e9e0 0xc638091af8404e9e 0xe01003ef8000f9f8 0x3e01003ef8000f9f

def z77 : W := mkw 0x800e025000000000 0x1800e02500000000 0x808a039000000000 0x0808a03900000000

def z78 : W := mkw 0x00400000a0052310 0x600400000a005231 0xa1b20010009f673f 0x5a1b20010009f673

def z79 : W := mkw 0x140f64001ad20006 0x1140f64001ad2000 0x088bc4001c930001 0x0088bc4001c93000

def z80 : W := mkw 0xa88f3e75c12c2948 0x5a88f3e75c12c294 0x11163c71e30c3802 0x111163c71e30c380

def z81 : W := mkw 0x1c016c001bfa0006 0x01c016c001bfa000 0x1e01fc001fff0007 0xc1e01fc001fff000

def z82 : W := mkw 0x800e025000000000 0x1800e02500000000 0xe1ee03f000000000 0x1e1ee03f00000000

def z83 : W := mkw 0x030040800c50c0a4 0x8030040800c50c0a 0x000000001c70c1fd 0xc000000001c70c1f

def z84 : W := mkw 0x00400000a0052310 0x600400000a005231 0x10000401e00f0000 0x010000401e00f000

def z85 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0e8038000000000 0x0e0e803800000000

def z86 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7ff63c6d83ffb9cf 0xf7ff63c6d83ffb9c

def z87 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe05c03f01f00fe08 0x9e05c03f01f00fe0

def z88 : W := mkw 0x00400000a0052310 0x600400000a005231 0x00100011e0002600 0x100100011e000260

def z89 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xc0ce03f01f80de01 0x8c0ce03f01f80de0

def z90 : W := mkw 0x28801825812c2940 0x428801825812c294 0x5644386d836c99c4 0xa5644386d836c99c

def z91 : W := mkw 0x7f8ffdaf9ffee9e6 0xd7f8ffdaf9ffee9e 0xffffffef9ffff9ff 0xfffffffef9ffff9f

def z92 : W := mkw 0x0000000000000000 0x0000000000000000 0x6660000c006081cc 0xe6660000c006081c

def z93 : W := mkw 0x08800800812c2940 0x408800800812c294 0x00100000036cb9ce 0xc00100000036cb9c

def z94 : W := mkw 0xc00fa75a40000008 0x1c00fa75a4000000 0x888bc79260000000 0x0888bc7926000000

def z95 : W := mkw 0xc30fe7da4c50c0ac 0x9c30fe7da4c50c0a 0xeeebc79e7c70c1fd 0xeeeebc79e7c70c1f

def z96 : W := mkw 0x6001b52f40000008 0x06001b52f4000000 0x1e01fc0fe0000000 0x21e01fc0fe000000

def z97 : W := mkw 0x100f240012800000 0x1100f24001280000 0x1feffc001f800003 0xc1feffc001f80000

def z98 : W := mkw 0x0000000000000000 0x0000000000000000 0xa1b200100080660b 0x5a1b200100080660

def z99 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x4e49c38e1c7081f4 0xa4e49c38e1c7081f

def z100 : W := mkw 0x4300818a0400c0a0 0x84300818a0400c0a 0xe000038e0000c1f8 0x2e000038e0000c1f

def z101 : W := mkw 0x3ccf7c25bbff2b56 0x73ccf7c25bbff2b5 0xfffffc7fffffffff 0xffffffc7ffffffff

def z102 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x77763c7de3efbfce 0xf77763c7de3efbfc

def z103 : W := mkw 0x4000810a00000000 0x04000810a0000000 0xe000038e00000000 0x2e000038e0000000

def z104 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x9e8bff9fe0000000 0x29e8bff9fe000000

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0xbba20402009f413f 0x6bba20402009f413

def z106 : W := mkw 0x904e0250b2853711 0x7904e0250b285371 0xbbb60473e39f7f3f 0x7bbb60473e39f7f3

def z107 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x405c03e01f80fe0b 0xc405c03e01f80fe0

def z108 : W := mkw 0xa04f3675e0052318 0x7a04f3675e005231 0x11163c71e08f2602 0x111163c71e08f260

def z109 : W := mkw 0x0000400008500004 0x0000040000850000 0x0889c0001c100001 0x00889c0001c10000

def z110 : W := mkw 0x0000000000000000 0x0000000000000000 0xabb200120090673f 0x7abb200120090673

def z111 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x444dfbec00000000 0x0444dfbec0000000

def z112 : W := mkw 0x000f240000000000 0x1000f24000000000 0x088bc40000000000 0x0088bc4000000000

def z113 : W := mkw 0xb28e12f59684fd41 0x5b28e12f59684fd4 0xe1fe03fd9f80ffcb 0xfe1fe03fd9f80ffc

def z114 : W := mkw 0xe000937f40000008 0x0e000937f4000000 0xe00003ffe0000000 0x3e00003ffe000000

def z115 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x044df8001f600000 0x8044df8001f60000

def z116 : W := mkw 0xe8cfbf7fe12d2b58 0x7e8cfbf7fe12d2b5 0xffffffffe3ffffff 0xfffffffffe3fffff

def z117 : W := mkw 0x0000000000000000 0x0000000000000000 0xaaa000020010413d 0x6aaa000020010413

def z118 : W := mkw 0x00400000a0052310 0x600400000a005231 0x11120411e08f2602 0x111120411e08f260

def z119 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x4449c38c1c6080c0 0x84449c38c1c6080c

def z120 : W := mkw 0x0000000000000000 0x0000000000000000 0x1a000403e0000000 0x21a000403e000000

def z121 : W := mkw 0x820e02d00400d401 0x1820e02d00400d40 0xe1fe03f00000fe08 0x1e1fe03f00000fe0

def z122 : W := mkw 0xd30ec3da1ed0d4a5 0x9d30ec3da1ed0d4a 0x444dc3ec1f6098c0 0x8444dc3ec1f6098c

def z123 : W := mkw 0x1c4f6c00bbff2316 0x71c4f6c00bbff231 0xbffffc13ffff673f 0xfbffffc13ffff673

def z124 : W := mkw 0x0000000000000000 0x0000000000000000 0xeee0000e0070c1fd 0xeeee0000e0070c1f

def z125 : W := mkw 0xd30ec3da1ed0d4a5 0x9d30ec3da1ed0d4a 0xefffc3fe1ff0ffff 0xfefffc3fe1ff0fff

def z126 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x404c03e01f009800 0x8404c03e01f00980

def z127 : W := mkw 0x0800080001280000 0x0080008000128000 0x17643800036c0006 0xc17643800036c000

def z128 : W := mkw 0x4d01ed0a097a00a6 0x84d01ed0a097a00a 0x1e01fc0e007f01f4 0x21e01fc0e007f01f

def z129 : W := mkw 0x1c4f2c00b3af2312 0x71c4f2c00b3af231 0xbbb63c13e39f673f 0x7bbb63c13e39f673

def z130 : W := mkw 0x1c0f2c0013aa0002 0x11c0f2c0013aa000 0x11063c00038f0002 0x011063c00038f000

def z131 : W := mkw 0x5f0fed8a1ffac0a6 0x95f0fed8a1ffac0a 0x9fefff821fff4037 0xc9fefff821fff403

def z132 : W := mkw 0x0880080001280840 0x0088008000128084 0x00000000036098c0 0x800000000036098c

def z133 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x6669c38c1c6081cc 0xe6669c38c1c6081c

def z134 : W := mkw 0x900e025012801401 0x1900e02501280140 0x0116007003803e02 0x10116007003803e0

def z135 : W := mkw 0xe04fb77fe0052318 0x7e04fb77fe005231 0xffffffffe0006738 0x3ffffffffe000673

def z136 : W := mkw 0x00400000a0052310 0x600400000a005231 0xb3300013e00c673e 0x7b3300013e00c673

def z137 : W := mkw 0xa00f367540000008 0x1a00f36754000000 0x77663c7de0000000 0x377663c7de000000

def z138 : W := mkw 0xe88fbf7fc12c2948 0x5e88fbf7fc12c294 0xffefffffe06c01c4 0x3ffefffffe06c01c

def z139 : W := mkw 0x2000102500000000 0x0200010250000000 0x7764386d80000000 0x37764386d8000000

def z140 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0xbfeffc13ffff0007 0xfbfeffc13ffff000

def z141 : W := mkw 0x3c8f3c2593ae2942 0x53c8f3c2593ae294 0x11163c61838f3802 0x111163c61838f380

def z142 : W := mkw 0x800e025000000000 0x1800e02500000000 0xe1fe03f00300b80a 0xde1fe03f00300b80

def z143 : W := mkw 0xe04fb77fe0052318 0x7e04fb77fe005231 0xffffffffe08f2602 0x3ffffffffe08f260

def z144 : W := mkw 0x2080102580042940 0x4208010258004294 0x6010006d8000b9c8 0x36010006d8000b9c

def z145 : W := mkw 0x0800080001280000 0x0080008000128000 0x00000000036c0006 0xc00000000036c000

def z146 : W := mkw 0x1c404800bbff2316 0x61c404800bbff231 0xbbb20413ffff673f 0xfbbb20413ffff673

def z147 : W := mkw 0x0c416c00a97f2316 0x60c416c00a97f231 0x1e01fc03e07f0134 0x21e01fc03e07f013

def z148 : W := mkw 0xf20fb7ff5680d409 0x1f20fb7ff5680d40 0xffffffffff80fe0b 0xfffffffffff80fe0

def z149 : W := mkw 0xbace1af5b7adff51 0x7bace1af5b7adff5 0xfffe3fffffffffff 0xffffe3ffffffffff

def z150 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x554ffffde0000000 0x1554ffffde000000

def z151 : W := mkw 0x28801825812c2940 0x428801825812c294 0xfff63c7fe36cb9ce 0xffff63c7fe36cb9c

def z152 : W := mkw 0x180e080013a80000 0x1180e080013a8000 0x17ee38001fec0007 0xc17ee38001fec000

def z153 : W := mkw 0x0000000000000000 0x0000000000000000 0x1ba20400009f0007 0x41ba20400009f000

def z154 : W := mkw 0x000f240000000000 0x1000f24000000000 0x11063c0000000000 0x011063c000000000

def z155 : W := mkw 0x820e02d00400c000 0x1820e02d00400c00 0xe1ee03f01c00c009 0xde1ee03f01c00c00

def z156 : W := mkw 0xfc0fff7f5bfa000e 0x1fc0fff7f5bfa000 0x444dfbec1f600000 0x8444dfbec1f60000

def z157 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x198ffc001f9f0003 0x0198ffc001f9f000

def z158 : W := mkw 0x0000000000000000 0x0000000000000000 0x617400600300b80a 0xd617400600300b80

def z159 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1e8bfc001cff0005 0x01e8bfc001cff000

def z160 : W := mkw 0xe000937f40000008 0x0e000937f4000000 0x400003ec00000000 0x0400003ec0000000

def z161 : W := mkw 0x1c0f2c0013aa0002 0x11c0f2c0013aa000 0x0004380003000000 0x0000438000300000

def z162 : W := mkw 0x0800080001280000 0x0080008000128000 0x0444380003600000 0x8044438000360000

def z163 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xeeedfbee00000000 0x2eeedfbee0000000

def z164 : W := mkw 0x6c01fd2f497a000e 0x06c01fd2f497a000 0x1e01fc0fe07f0004 0x21e01fc0fe07f000

def z165 : W := mkw 0x0000000080042100 0x4000000008004210 0xbbb20413e00c210e 0x7bbb20413e00c210

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0x8882041260000000 0x0888204126000000

def z167 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x154ffc001fef0002 0x8154ffc001fef000

def z168 : W := mkw 0xe04fb77fe0052318 0x7e04fb77fe005231 0xffffffffe09f673f 0x7ffffffffe09f673

def z169 : W := mkw 0xe040937fe0052318 0x6e040937fe005231 0xe01003ffe0006738 0x3e01003ffe000673

def z170 : W := mkw 0x400fa50a00000000 0x1400fa50a0000000 0xffefff8e00000000 0x2ffefff8e0000000

def z171 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbbb20413e0006738 0x3bbb20413e000673

def z172 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeffdc3ee1f70f9ff 0xfeffdc3ee1f70f9f

def z173 : W := mkw 0x9e0f6ed01ffad407 0x19e0f6ed01ffad40 0x444dfbe01f609800 0x8444dfbe01f60980

def z174 : W := mkw 0x00400000a0052310 0x600400000a005231 0x3b300403e01f213e 0x73b300403e01f213

def z175 : W := mkw 0x020000800400c000 0x0020000800400c00 0xe0e803801c00c009 0xce0e803801c00c00

def z176 : W := mkw 0x28801825812c2940 0x428801825812c294 0xf7f6387d83ecffcf 0xff7f6387d83ecffc

def z177 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x044df8001fff0007 0xc044df8001fff000

def z178 : W := mkw 0x920002d01680d401 0x0920002d01680d40 0xe01003f01f80fe0b 0xde01003f01f80fe0

def z179 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x8e89c38e1c7041f5 0x28e89c38e1c7041f

def z180 : W := mkw 0x9a8e0ad097acfd41 0x59a8e0ad097acfd4 0xe1fe03f01fecffcf 0xde1fe03f01fecffc

def z181 : W := mkw 0x2c817c25897e2946 0x42c817c25897e294 0x7f75fc6d837fb9ce 0xf7f75fc6d837fb9c

def z182 : W := mkw 0x600fb52f40000008 0x1600fb52f4000000 0x1feffc0fe0000000 0x21feffc0fe000000

def z183 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x819e03f01f807e03 0x1819e03f01f807e0

def z184 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeee9c38e1c104031 0x2eee9c38e1c10403

def z185 : W := mkw 0x28801825812c2940 0x428801825812c294 0x5554386d836cb8c2 0x95554386d836cb8c

def z186 : W := mkw 0x004f2400a0052310 0x7004f2400a005231 0xbffffc13e09f673f 0x7bffffc13e09f673

def z187 : W := mkw 0x430fe58a0c50c0a4 0x9430fe58a0c50c0a 0xffefff8e1c70c1fd 0xeffefff8e1c70c1f

def z188 : W := mkw 0x1c0e48001bfa0006 0x11c0e48001bfa000 0x01ee00001fff0007 0xc01ee00001fff000

def z189 : W := mkw 0x00400000a0052310 0x600400000a005231 0x1bb20400009f673f 0x41bb20400009f673

def z190 : W := mkw 0xe30ff7ff4c50c0ac 0x9e30ff7ff4c50c0a 0xffeffffffc70c1fd 0xfffeffffffc70c1f

def z191 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x776dfbed80000000 0x3776dfbed8000000

def z192 : W := mkw 0x6b80d9af0d78c8e4 0x86b80d9af0d78c8e 0xeeedfbee1f70d9fd 0xeeeedfbee1f70d9f

def z193 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x8889c3821c70c1fd 0xc8889c3821c70c1f

def z194 : W := mkw 0x0000000080042100 0x4000000008004210 0x33300001800c210e 0x733300001800c210

def z195 : W := mkw 0x0000400008500004 0x0000040000850000 0x1febc4001cff0007 0xc1febc4001cff000

def z196 : W := mkw 0x020040800c50c004 0x0020040800c50c00 0xeee9c3801c70c00d 0xceee9c3801c70c00

def z197 : W := mkw 0xe88fbf7fc12c2948 0x5e88fbf7fc12c294 0xffffffffe30c3802 0x3ffffffffe30c380

def z198 : W := mkw 0xd30ec3da1ed0d4a5 0x9d30ec3da1ed0d4a 0xe9ffc3f21f90fe3b 0xde9ffc3f21f90fe3

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z200 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0xbfeffc021fff413f 0xebfeffc021fff413

def z201 : W := mkw 0x820002d00400d401 0x0820002d00400d40 0xe0f803f01c00fe09 0xde0f803f01c00fe0

def z202 : W := mkw 0x1c0048001bfa0006 0x01c0048001bfa000 0x0ee9c0001fff0007 0xc0ee9c0001fff000

def z203 : W := mkw 0x5f0fed8a1ffac0a6 0x95f0fed8a1ffac0a 0x444dfb8c1f6080c0 0x8444dfb8c1f6080c

def z204 : W := mkw 0x2080102580042940 0x4208010258004294 0x7330006d800cb9ce 0x77330006d800cb9c

def z205 : W := mkw 0x4340c18aac55e3b4 0xe4340c18aac55e3b 0xfffbc79ffcffe7ff 0xffffbc79ffcffe7f

def z206 : W := mkw 0x2080102580042940 0x4208010258004294 0x0010006180003800 0x1001000618000380

def z207 : W := mkw 0x6b80d9af8d7ce9e4 0xc6b80d9af8d7ce9e 0xfffdfbef9f7cf9ff 0xffffdfbef9f7cf9f

def z208 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x7774386d83ffffff 0xf7774386d83fffff

def z209 : W := mkw 0x0000000000000000 0x0000000000000000 0xbba20413e09f0007 0x7bba20413e09f000

def z210 : W := mkw 0x28801825812c2940 0x428801825812c294 0x1600380d806c01c4 0x21600380d806c01c

def z211 : W := mkw 0xba8e1af597acfd41 0x5ba8e1af597acfd4 0xf7fe3bfd9fecffcf 0xff7fe3bfd9fecffc

def z212 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeffbc39e1cf0e7ff 0xfeffbc39e1cf0e7f

def z213 : W := mkw 0x4100c10a085000a4 0x84100c10a085000a 0x0e01c00e007001f4 0x20e01c00e007001f

def z214 : W := mkw 0xe30ff7ff4c50c0ac 0x9e30ff7ff4c50c0a 0xeeedfbee1c70c1fd 0xeeeedfbee1c70c1f

def z215 : W := mkw 0x0040000020010210 0x2004000002001021 0xbba20413e0934631 0x3bba20413e093463

def z216 : W := mkw 0x120000801680d401 0x0120000801680d40 0x617400601f80fe0b 0xd617400601f80fe0

def z217 : W := mkw 0x00400000a0052310 0x600400000a005231 0xb1b20411e08f660b 0x5b1b20411e08f660

def z218 : W := mkw 0x4340818aa405e3b0 0xe4340818aa405e3b 0xe010039fe000e7f8 0x3e010039fe000e7f

def z219 : W := mkw 0x140040001ad20006 0x0140040001ad2000 0x000000001c930001 0x0000000001c93000

def z220 : W := mkw 0x4000c10a08500004 0x04000c10a0850000 0xeee9c38e1c700005 0xeeee9c38e1c70000

def z221 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xbbb63c73e39f7f3f 0x7bbb63c73e39f7f3

def z222 : W := mkw 0x030040800c50c0a4 0x8030040800c50c0a 0xaaa000021c70c1fd 0xeaaa000021c70c1f

def z223 : W := mkw 0x4100c10a085000a4 0x84100c10a085000a 0x0801c00200100030 0x00801c0020010003

def z224 : W := mkw 0x2b8058a58d7ce9e4 0xc2b8058a58d7ce9e 0x7774386d9f7cf9ff 0xf7774386d9f7cf9f

def z225 : W := mkw 0x5f4fed8abfffe3b6 0xf5f4fed8abfffe3b 0xffffff9fffffe7ff 0xfffffff9fffffe7f

def z226 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0xbffffc101fff660f 0xdbffffc101fff660

def z227 : W := mkw 0xaa801af5852cfd41 0x4aa801af5852cfd4 0xf7743bfd836cffce 0xff7743bfd836cffc

def z228 : W := mkw 0xd20fa7da5680d409 0x1d20fa7da5680d40 0xe9ffc7f27f80fe0b 0xde9ffc7f27f80fe0

def z229 : W := mkw 0xb20f36f55680d409 0x1b20f36f55680d40 0xf1fe3ff1ff80fe0b 0xdf1fe3ff1ff80fe0

def z230 : W := mkw 0x28801825812c2940 0x428801825812c294 0x33343861830c390e 0x733343861830c390

def z231 : W := mkw 0x020000800400c000 0x0020000800400c00 0xeae803821c10c13d 0xeeae803821c10c13

def z232 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeee9c38e1c6080c0 0xaeee9c38e1c6080c

def z233 : W := mkw 0xe001b77f40000008 0x0e001b77f4000000 0xfe01ffffe0000000 0x3fe01ffffe000000

def z234 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x0e01c00e1c70c1fd 0xe0e01c00e1c70c1f

def z235 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x7feffc0c1fff81cf 0xe7feffc0c1fff81c

def z236 : W := mkw 0xe20fb7ff4400c008 0x1e20fb7ff4400c00 0xffeffffffc00c009 0xfffeffffffc00c00

def z237 : W := mkw 0x4300818a0400c0a0 0x84300818a0400c0a 0xe0e8038e1c00c1f9 0xee0e8038e1c00c1f

def z238 : W := mkw 0x01004000085000a4 0x801004000085000a 0x00000000007001f4 0x000000000007001f

def z239 : W := mkw 0x120000801680d401 0x0120000801680d40 0x001000001f80fe0b 0xc001000001f80fe0

def z240 : W := mkw 0x4000810a00000000 0x04000810a0000000 0x4449c38c00000000 0x04449c38c0000000

def z241 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe7fe03fc1fe0ffcf 0xfe7fe03fc1fe0ffc

def z242 : W := mkw 0x0040000020010210 0x2004000002001021 0xaaa204126093473d 0x6aaa204126093473

def z243 : W := mkw 0x0000000000000000 0x0000000000000000 0x01a2000000800003 0x401a200000080000

def z244 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x617c03e01f00b80a 0xd617c03e01f00b80

def z245 : W := mkw 0xbe8f7ef59ffefd47 0x5be8f7ef59ffefd4 0xfffffffd9fffffcf 0xffffffffd9fffffc

def z246 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600000c006001c4 0x20600000c006001c

def z247 : W := mkw 0xa00e127500000000 0x1a00e12750000000 0xf7ee3bfd80000000 0x3f7ee3bfd8000000

def z248 : W := mkw 0x3c0f7c251bfa0006 0x13c0f7c251bfa000 0x7feffc6d9fff0007 0xf7feffc6d9fff000

def z249 : W := mkw 0xc00e835a00000000 0x1c00e835a0000000 0xefefc3fe00000000 0x3efefc3fe0000000

def z250 : W := mkw 0xb88e1a7593ac3d41 0x5b88e1a7593ac3d4 0x7776387d83ecbfce 0xf7776387d83ecbfc

def z251 : W := mkw 0x824002d0a405f711 0x6824002d0a405f71 0xe01003f3e000ff38 0x3e01003f3e000ff3

def z252 : W := mkw 0xd40fe75a5ad2000e 0x1d40fe75a5ad2000 0x888bc7927c930001 0x0888bc7927c93000

def z253 : W := mkw 0x3c8f7c259bfe2946 0x53c8f7c259bfe294 0x1ffffc619fff3807 0xd1ffffc619fff380

def z254 : W := mkw 0x000f240000000000 0x1000f24000000000 0x044df80000000000 0x0044df8000000000

def z255 : W := mkw 0x0800080001280000 0x0080008000128000 0x1fe63c0003ff0007 0xc1fe63c0003ff000

def z256 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x809a03901f80fe0b 0xc809a03901f80fe0

def z257 : W := mkw 0xc30083da0400d4a1 0x8c30083da0400d4a 0xe01003fe0000fff8 0x3e01003fe0000fff

def z258 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x0ccffc001ff30001 0x80ccffc001ff3000

def z259 : W := mkw 0xa000127540000008 0x0a00012754000000 0x00000071e0000000 0x100000071e000000

def z260 : W := mkw 0xc00fa75a40000008 0x1c00fa75a4000000 0x0009c38000000000 0x00009c3800000000

def z261 : W := mkw 0x020000800400c000 0x0020000800400c00 0xe00003800000c008 0x0e00003800000c00

def z262 : W := mkw 0xb00f367552801409 0x1b00f36755280140 0x11163c71e3803e02 0x111163c71e3803e0

def z263 : W := mkw 0x4300c18a8c54e1a4 0xc4300c18a8c54e1a 0xfff9c38f9c7ce1ff 0xffff9c38f9c7ce1f

def z264 : W := mkw 0xf00fb77f52800008 0x1f00fb77f5280000 0xffefffffff800003 0xfffefffffff80000

def z265 : W := mkw 0x960f66d01ed2d407 0x1960f66d01ed2d40 0x888bc7901c934601 0x0888bc7901c93460

def z266 : W := mkw 0xe88fbf7fc12c2948 0x5e88fbf7fc12c294 0xffffffffe36cb9ce 0xfffffffffe36cb9c

def z267 : W := mkw 0x9c0f6e501bfa0006 0x19c0f6e501bfa000 0xffeffff01fff0007 0xdffeffff01fff000

def z268 : W := mkw 0x28801825812c2940 0x428801825812c294 0x6454386d8360b9c8 0xb6454386d8360b9c

def z269 : W := mkw 0x4300818a0400c0a0 0x84300818a0400c0a 0x4000038c000080c0 0x04000038c000080c

def z270 : W := mkw 0x20c01025a0052b50 0x620c01025a0052b5 0xe010007fe000fff8 0x3e010007fe000fff

def z271 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1e4dfc001f7f0004 0x81e4dfc001f7f000

def z272 : W := mkw 0x5c0fed0a1bfa0006 0x15c0fed0a1bfa000 0xffefff8e1fff0007 0xeffefff8e1fff000

def z273 : W := mkw 0x2880182501280840 0x0288018250128084 0x6574386c0360b8ca 0xd6574386c0360b8c

def z274 : W := mkw 0x820002d00400d401 0x0820002d00400d40 0x8000039000004600 0x0800003900000460

def z275 : W := mkw 0x1f0048801ffac0a6 0x81f0048801ffac0a 0x000000001fffc1ff 0xc000000001fffc1f

def z276 : W := mkw 0x00400000a0052310 0x600400000a005231 0x1bb20411e09f2607 0x51bb20411e09f260

def z277 : W := mkw 0xe30ff7ff4c50c0ac 0x9e30ff7ff4c50c0a 0xffeffffffc104031 0x3ffeffffffc10403

def z278 : W := mkw 0x2000102500000000 0x0200010250000000 0x1600380d80000000 0x21600380d8000000

def z279 : W := mkw 0x9e0f6ed01ffad407 0x19e0f6ed01ffad40 0xe5fffbf01fe0fe0b 0xde5fffbf01fe0fe0

def z280 : W := mkw 0x1c4f6c00bbff2316 0x71c4f6c00bbff231 0x1ffffc11ffff2607 0xd1ffffc11ffff260

def z281 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xe000038e1c70c1fd 0xee000038e1c70c1f

def z282 : W := mkw 0x0000000000000000 0x0000000000000000 0x6774006c0360b9ce 0xf6774006c0360b9c

def z283 : W := mkw 0x904e0250b2853711 0x7904e0250b285371 0x11160471e38f3e02 0x111160471e38f3e0

def z284 : W := mkw 0xe80fbf7f41280008 0x1e80fbf7f4128000 0xffefffffe36c0006 0xfffefffffe36c000

def z285 : W := mkw 0x100e000012800000 0x1100e00001280000 0x61fe00601f80b80b 0xd61fe00601f80b80

def z286 : W := mkw 0x080f2c0001280000 0x1080f2c000128000 0x1feffc00036c0006 0xc1feffc00036c000

def z287 : W := mkw 0x12400080b685f711 0x612400080b685f71 0xbbb20413ff9fff3f 0xfbbb20413ff9fff3

def z288 : W := mkw 0xfc0fff7f5bfa000e 0x1fc0fff7f5bfa000 0xffefffffff600000 0xbffefffffff60000

def z289 : W := mkw 0x2080102500000840 0x0208010250000084 0x4000006c000098c0 0x04000006c000098c

def z290 : W := mkw 0x924e02d0b685f711 0x7924e02d0b685f71 0xe1fe03f3ff80ff3b 0xfe1fe03f3ff80ff3

def z291 : W := mkw 0xeb8fffffcd7ce9ec 0xdeb8fffffcd7ce9e 0xffffffffff7cf9ff 0xfffffffffff7cf9f

def z292 : W := mkw 0x1e0f6c801ffad407 0x11e0f6c801ffad40 0x1ffffc001ffffe0f 0xc1ffffc001ffffe0

def z293 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x1e003c0fe07f01f4 0x21e003c0fe07f01f

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0x0660000000600004 0xc066000000060000

def z295 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x998ffff3e0000000 0x1998ffff3e000000

def z296 : W := mkw 0x00400000a0052310 0x600400000a005231 0x33320411e08f270e 0x733320411e08f270

def z297 : W := mkw 0x0040000020010210 0x2004000002001021 0x0002041060830600 0x0000204106083060

def z298 : W := mkw 0x030040800c50c0a4 0x8030040800c50c0a 0x000000001c104031 0x0000000001c10403

def z299 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xfbfe07f01f9ffe0f 0xdfbfe07f01f9ffe0

def z300 : W := mkw 0x0000000000000000 0x0000000000000000 0x1a000400001f0004 0x01a000400001f000

def z301 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x415e03f01f80be02 0x9415e03f01f80be0

def z302 : W := mkw 0x0000000000000000 0x0000000000000000 0x001000000080660b 0x4001000000080660

def z303 : W := mkw 0x28801825812c2940 0x428801825812c294 0x3730380d806c21ce 0x73730380d806c21c

def z304 : W := mkw 0x924e02d03681d611 0x3924e02d03681d61 0xe9fe07f27f93fe3b 0xde9fe07f27f93fe3

def z305 : W := mkw 0x20c01025a0052b50 0x620c01025a0052b5 0xfbb2047fe09fffff 0x7fbb2047fe09ffff

def z306 : W := mkw 0xa88f3e75c12c2948 0x5a88f3e75c12c294 0x77763c7de36cb9ce 0xf77763c7de36cb9c

def z307 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xebfe03f21f90ff3f 0xfebfe03f21f90ff3

def z308 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffffffffe080660b 0x7ffffffffe080660

def z309 : W := mkw 0x570fe58a1ed2c0a6 0x9570fe58a1ed2c0a 0x888bc7821c934031 0x0888bc7821c93403

def z310 : W := mkw 0x020000800400c000 0x0020000800400c00 0xe6e8038c1c60c1cd 0xee6e8038c1c60c1c

def z311 : W := mkw 0x2880182501280840 0x0288018250128084 0x0004386003001800 0x0000438600300180

def z312 : W := mkw 0xf24fb7fff685f719 0x7f24fb7fff685f71 0xffffffffff9fff3f 0xfffffffffff9fff3

def z313 : W := mkw 0x0000400008500004 0x0000040000850000 0x6ee9c00c1c7081cd 0xe6ee9c00c1c7081c

def z314 : W := mkw 0x820002d00400d401 0x0820002d00400d40 0xe17403f00300fe0a 0xde17403f00300fe0

def z315 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe0ec03e01f00d809 0xce0ec03e01f00d80

def z316 : W := mkw 0xfc0fbf7f53aa000a 0x1fc0fbf7f53aa000 0xffefffffe38f0002 0x3ffefffffe38f000

def z317 : W := mkw 0x6301f5af4c50c0ac 0x86301f5af4c50c0a 0xfee9ff8ffc70c1fd 0xefee9ff8ffc70c1f

def z318 : W := mkw 0xe04fb77f60010218 0x3e04fb77f6001021 0xffefffffe0934631 0x3ffefffffe093463

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0a0000000004009 0x4a0a000000000400

def z320 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xe88bc7ffe0000000 0x3e88bc7ffe000000

def z321 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xffebc78e1cffc1ff 0xeffebc78e1cffc1f

def z322 : W := mkw 0x1c0048001bfa0006 0x01c0048001bfa000 0x176438001fff0007 0xc176438001fff000

def z323 : W := mkw 0x28801825812c2940 0x428801825812c294 0x1714386d836c39c6 0x31714386d836c39c

def z324 : W := mkw 0x130040801ed0d4a5 0x8130040801ed0d4a 0x001000001ff0ffff 0xc001000001ff0fff

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0xe1f600700380fe0b 0xde1f600700380fe0

def z326 : W := mkw 0x08800800812c2940 0x408800800812c294 0x00100000030c3802 0x000100000030c380

def z327 : W := mkw 0x00400000a0052310 0x600400000a005231 0x11120411e09f673f 0x511120411e09f673

def z328 : W := mkw 0x924e02d0b685f711 0x7924e02d0b685f71 0xf1fe07f1ff8ffe0b 0xdf1fe07f1ff8ffe0

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0x6060000000008008 0xc606000000000800

def z330 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x1f07fc7fe0000000 0x31f07fc7fe000000

def z331 : W := mkw 0x0000000000000000 0x0000000000000000 0x00e800001c000001 0xc00e800001c00000

def z332 : W := mkw 0x0000000000000000 0x0000000000000000 0x6660000c00000000 0x26660000c0000000

def z333 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffffffffe300b80a 0xfffffffffe300b80

def z334 : W := mkw 0x200f342500000000 0x1200f34250000000 0x7feffc6d80000000 0x37feffc6d8000000

def z335 : W := mkw 0x0401640008520006 0x0040164000852000 0x0801c40000130000 0x00801c4000013000

def z336 : W := mkw 0x4300818a0400c0a0 0x84300818a0400c0a 0xeee9c38e0000c1f8 0x2eee9c38e0000c1f

def z337 : W := mkw 0x00400000a0052310 0x600400000a005231 0x9a820413e09f4735 0x29a820413e09f473

def z338 : W := mkw 0x6b80d9af0d78c8e4 0x86b80d9af0d78c8e 0x444dfbec1f6098c0 0x8444dfbec1f6098c

def z339 : W := mkw 0x140f64001ad20006 0x1140f64001ad2000 0x1feffc001c930001 0x01feffc001c93000

def z340 : W := mkw 0x140f64001ad20006 0x1140f64001ad2000 0x0009c0001c000000 0x00009c0001c00000

def z341 : W := mkw 0x2000102500000000 0x0200010250000000 0x1104386180000000 0x1110438618000000

def z342 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe06081cc 0xfffefffffe06081c

def z343 : W := mkw 0xfb8edbff9ffcfde5 0xdfb8edbff9ffcfde 0xfffffbff9ffcffff 0xffffffbff9ffcfff

def z344 : W := mkw 0x4001a50a40000008 0x04001a50a4000000 0x0801c40260000000 0x00801c4026000000

def z345 : W := mkw 0x0040000020010210 0x2004000002001021 0x8000001260004630 0x0800000126000463

def z346 : W := mkw 0x4300818a0400c0a0 0x84300818a0400c0a 0xeaa0038e0010c1fd 0x6eaa0038e0010c1f

def z347 : W := mkw 0x0000000080042100 0x4000000008004210 0x73740061830cb90e 0xf73740061830cb90

def z348 : W := mkw 0x00400000a0052310 0x600400000a005231 0xa8920413e0936739 0x3a8920413e093673

def z349 : W := mkw 0x1c8048009bfe2946 0x41c8048009bfe294 0x001000001fffb9cf 0xc001000001fffb9c

def z350 : W := mkw 0x930e42d01ed0d4a5 0x9930e42d01ed0d4a 0xe1fe03f01ff0ffff 0xde1fe03f01ff0fff

def z351 : W := mkw 0x4100c10a085000a4 0x84100c10a085000a 0xaea1c00e007041fd 0x6aea1c00e007041f

def z352 : W := mkw 0xd34ec3dabed5f7b5 0xfd34ec3dabed5f7b 0xffffc7ffffffffff 0xfffffc7fffffffff

def z353 : W := mkw 0x4300818a0400c0a0 0x84300818a0400c0a 0xe660038e0060c1fc 0xee660038e0060c1f

def z354 : W := mkw 0x0000000000000000 0x0000000000000000 0x3320000180000000 0x3332000018000000

def z355 : W := mkw 0xf30ff7ff5ed0d4ad 0x9f30ff7ff5ed0d4a 0xfffffffffff0ffff 0xffffffffffff0fff

def z356 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x4ee9c38c1c7080c5 0xc4ee9c38c1c7080c

def z357 : W := mkw 0x6000912f00000000 0x06000912f0000000 0xffedfbef80000000 0x3ffedfbef8000000

def z358 : W := mkw 0x0000000000000000 0x0000000000000000 0xbba20413e010413d 0x7bba20413e010413

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0x4440000c006080c0 0x84440000c006080c

def z360 : W := mkw 0x0000000000000000 0x0000000000000000 0x0aa0000000100005 0x40aa000000010000

def z361 : W := mkw 0x0000000000000000 0x0000000000000000 0x11020400008f0002 0x011020400008f000

def z362 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x0009c3801c000000 0x00009c3801c00000

def z363 : W := mkw 0x5f00c98a1ffac0a6 0x85f00c98a1ffac0a 0xeee9c38e1fffc1ff 0xeeee9c38e1fffc1f

def z364 : W := mkw 0x900e025012801401 0x1900e02501280140 0x0002001000800600 0x0000200100080060

def z365 : W := mkw 0x0000000000000000 0x0000000000000000 0x0112001000802602 0x1011200100080260

def z366 : W := mkw 0x120000801680d401 0x0120000801680d40 0xa1b200101f80fe0b 0xda1b200101f80fe0

def z367 : W := mkw 0x00404000a8552314 0x600404000a855231 0xbffbc413fcff673f 0xfbffbc413fcff673

def z368 : W := mkw 0x0040000020010210 0x2004000002001021 0x0800040260130030 0x0080004026013003

def z369 : W := mkw 0x920e42d01ed0d405 0x1920e42d01ed0d40 0xefffc3f01ff0fe0f 0xdefffc3f01ff0fe0

def z370 : W := mkw 0x1c404800bbff2316 0x61c404800bbff231 0x001000001fff673f 0xc001000001fff673

def z371 : W := mkw 0x0000000080042100 0x4000000008004210 0x7770000d806ca1ce 0xf7770000d806ca1c

def z372 : W := mkw 0x0001240000000000 0x0000124000000000 0x1e01fc0000000000 0x01e01fc000000000

def z373 : W := mkw 0x0c004800097a0006 0x00c004800097a000 0x00000000007f0004 0x000000000007f000

def z374 : W := mkw 0x9e0e4ad01ffad407 0x19e0e4ad01ffad40 0xe1fe03f01ffffe0f 0xde1fe03f01ffffe0

def z375 : W := mkw 0x00400000a0052310 0x600400000a005231 0xfbf60473e39fff3f 0xffbf60473e39fff3

def z376 : W := mkw 0x2000102580042100 0x4200010258004210 0x7774386d800c210e 0x77774386d800c210

def z377 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xcccffffe60000000 0x0cccffffe6000000

def z378 : W := mkw 0x388e182593ac2940 0x5388e182593ac294 0x77fe386d9fecb9cf 0xf77fe386d9fecb9c

def z379 : W := mkw 0x6881bd2fc12c2948 0x46881bd2fc12c294 0x1e01fc0fe06c01c4 0x21e01fc0fe06c01c

def z380 : W := mkw 0x000f240000000000 0x1000f24000000000 0xbfeffc13e0000000 0x3bfeffc13e000000

def z381 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe09a03f01c80fe09 0x1e09a03f01c80fe0

def z382 : W := mkw 0x00400000a0052310 0x600400000a005231 0xaab00002009f673f 0x6aab00002009f673

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0x222000000000010c 0x6222000000000010

def z384 : W := mkw 0x120000801680d401 0x0120000801680d40 0x000000001f009800 0x8000000001f00980

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0xa1a2001000000000 0x1a1a200100000000

def z386 : W := mkw 0x1c0048001bfa0006 0x01c0048001bfa000 0x1ba204001fff0007 0xc1ba204001fff000

def z387 : W := mkw 0x00400000a0052310 0x600400000a005231 0x99920413e09f6633 0x199920413e09f663

def z388 : W := mkw 0x9e4f6ed0bffff717 0x79e4f6ed0bffff71 0xfffffff3ffffff3f 0xffffffff3ffffff3

def z389 : W := mkw 0x08c00800a12d2b50 0x608c00800a12d2b5 0x0010000003ffffff 0xc0010000003fffff

def z390 : W := mkw 0x2880182501280840 0x0288018250128084 0x7764386d836098c0 0xb7764386d836098c

def z391 : W := mkw 0xa88e1a75812c2940 0x5a88e1a75812c294 0xf7fe3bfd836cb9ce 0xff7fe3bfd836cb9c

def z392 : W := mkw 0x00400000a0052310 0x600400000a005231 0x00000003e0000130 0x200000003e000013

def z393 : W := mkw 0x000f240000000000 0x1000f24000000000 0x1feffc00009f0007 0x41feffc00009f000

def z394 : W := mkw 0xff0fffff5ffac0ae 0x9ff0fffff5ffac0a 0xffefffffffffc1ff 0xfffefffffffffc1f

def z395 : W := mkw 0x1c0f6c009bfe2106 0x51c0f6c009bfe210 0x3ffffc019fff210f 0xf3ffffc019fff210

def z396 : W := mkw 0x0000400008500004 0x0000040000850000 0x000000001c700005 0xc000000001c70000

def z397 : W := mkw 0x28801825812c2940 0x428801825812c294 0x1764380d836c01c6 0xe1764380d836c01c

def z398 : W := mkw 0x020000800400d401 0x0020000800400d40 0x001000000000fe08 0x0001000000000fe0

def z399 : W := mkw 0x140f64001ad20006 0x1140f64001ad2000 0x0eebc4001cf30005 0xc0eebc4001cf3000

def z400 : W := mkw 0x4340c18aac55e3b4 0xe4340c18aac55e3b 0xbbbbc793fc9f673f 0x7bbbbc793fc9f673

def z401 : W := mkw 0x2c817c25897e2946 0x42c817c25897e294 0x1e01fc0d807f01c4 0x21e01fc0d807f01c

def z402 : W := mkw 0xe30ff7ff4c50c0ac 0x9e30ff7ff4c50c0a 0x444dfbec1c6080c0 0x8444dfbec1c6080c

def z403 : W := mkw 0x900e025012801401 0x1900e02501280140 0x617600700380be0a 0xd617600700380be0

def z404 : W := mkw 0x1c8f6c009bfe2946 0x51c8f6c009bfe294 0x1ffffc001fffb9cf 0xc1ffffc001fffb9c

def z405 : W := mkw 0x03404080ac55e3b4 0xe03404080ac55e3b 0x001000001cffe7ff 0xc001000001cffe7f

def z406 : W := mkw 0x28801825812c2940 0x428801825812c294 0x6010006d836cb9ce 0xf6010006d836cb9c

def z407 : W := mkw 0x1e0f6c801ffac006 0x11e0f6c801ffac00 0xffefff801fffc00f 0xcffefff801fffc00

def z408 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1f07fc0003ff0006 0x01f07fc0003ff000

def z409 : W := mkw 0x8000025000000000 0x0800002500000000 0xe00003f000000000 0x1e00003f00000000

def z410 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x4449c38c1c70c1fd 0xc4449c38c1c70c1f

def z411 : W := mkw 0x6980d92f897c29e4 0xc6980d92f897c29e 0x1e01f80f807c01f4 0x21e01f80f807c01f

def z412 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000010413d 0x4000000000010413

def z413 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xffebc79ffc70c1fd 0xfffebc79ffc70c1f

def z414 : W := mkw 0xc000835a40000008 0x0c000835a4000000 0x8000039260000000 0x0800003926000000

def z415 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x088bc4001fff0007 0xc088bc4001fff000

def z416 : W := mkw 0xe08fb77fc0042948 0x5e08fb77fc004294 0xffffffffe000b9c8 0x3ffffffffe000b9c

def z417 : W := mkw 0x3c8f7c259bfe2946 0x53c8f7c259bfe294 0x1feffc0d9fff01c7 0xe1feffc0d9fff01c

def z418 : W := mkw 0x4b80c98a8d7ce9e4 0xc4b80c98a8d7ce9e 0xeef9c38e1f7cf9ff 0xeeef9c38e1f7cf9f

def z419 : W := mkw 0x6881bd2fc12c2948 0x46881bd2fc12c294 0x7f75fc6fe36cb9ce 0xf7f75fc6fe36cb9c

def z420 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x5e4dffefe0000000 0x25e4dffefe000000

def z421 : W := mkw 0x0000000000000000 0x0000000000000000 0xbbb20413e080660b 0x7bbb20413e080660

def z422 : W := mkw 0x3c8f7c251bfa0846 0x13c8f7c251bfa084 0x444df86c1f6098c0 0x8444df86c1f6098c

def z423 : W := mkw 0x100e000012800000 0x1100e00001280000 0x1bee04001f9f0007 0xc1bee04001f9f000

def z424 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000006081cc 0xc00000000006081c

def z425 : W := mkw 0x0c016c00097a0006 0x00c016c00097a000 0x1f65fc00037f0006 0xc1f65fc00037f000

def z426 : W := mkw 0x28805825897c2944 0x428805825897c294 0x7ffdf86d9f7cb9cf 0xf7ffdf86d9f7cb9c

def z427 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x7ffffc601fffb80f 0xd7ffffc601fffb80

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0xa010001000006608 0x1a01000100000660

def z429 : W := mkw 0x1c4f6c003bfb0216 0x31c4f6c003bfb021 0x9feffc127fff4637 0xc9feffc127fff463

def z430 : W := mkw 0x1c4f6c00bbff2316 0x71c4f6c00bbff231 0x1ffffc001fff673f 0xc1ffffc001fff673

def z431 : W := mkw 0x6041b52fe0052318 0x66041b52fe005231 0x1e01fc0fe01f0134 0x21e01fc0fe01f013

def z432 : W := mkw 0x5d0fed0a1bfa00a6 0x95d0fed0a1bfa00a 0x1feffc0e1fff01f7 0xe1feffc0e1fff01f

def z433 : W := mkw 0x3c8f7c259bfe2946 0x53c8f7c259bfe294 0x777df86d9f6cb9ce 0xf777df86d9f6cb9c

def z434 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xe889c38e1c10c1f9 0x2e889c38e1c10c1f

def z435 : W := mkw 0xe080937fc0042948 0x4e080937fc004294 0xe01003ffe000b9c8 0x3e01003ffe000b9c

def z436 : W := mkw 0x0000000000000000 0x0000000000000000 0x6164006000000000 0x1616400600000000

def z437 : W := mkw 0x030040800c50c0a4 0x8030040800c50c0a 0xe0e803801c70c1fd 0xce0e803801c70c1f

def z438 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xe449c38e1c60c1f8 0xae449c38e1c60c1f

def z439 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x11163c71e38f3e02 0x111163c71e38f3e0

def z440 : W := mkw 0x4340c18a2c51c2b4 0xa4340c18a2c51c2b 0xeeebc79e7cf3c7fd 0xeeeebc79e7cf3c7f

def z441 : W := mkw 0x1c00080013aa0002 0x01c00080013aa000 0x00000000038f0002 0x000000000038f000

def z442 : W := mkw 0x2000102500000000 0x0200010250000000 0x4444386c00000000 0x04444386c0000000

def z443 : W := mkw 0x5f0fed8a1ffac0a6 0x95f0fed8a1ffac0a 0x5fefff8c1fff80c7 0xc5fefff8c1fff80c

def z444 : W := mkw 0x6380d1af8c54e9e4 0xc6380d1af8c54e9e 0xeef9c3ef9c70f9fd 0xfeef9c3ef9c70f9f

def z445 : W := mkw 0xd30e83da1680d4a1 0x9d30e83da1680d4a 0xe1fe03fe1f80fffb 0xfe1fe03fe1f80fff

def z446 : W := mkw 0x6000912f40000008 0x06000912f4000000 0x0000000fe0000000 0x20000000fe000000

def z447 : W := mkw 0x4100810a000000a0 0x84100810a000000a 0x0000000e000001f0 0x20000000e000001f

def z448 : W := mkw 0x08800800812c2940 0x408800800812c294 0x00000000006c01c4 0x000000000006c01c

def z449 : W := mkw 0x0000000000000000 0x0000000000000000 0x1ba2040000000000 0x01ba204000000000

def z450 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xccc9c38e1c70c0f1 0x8ccc9c38e1c70c0f

def z451 : W := mkw 0x0040000020010210 0x2004000002001021 0xa9b204126093663b 0x5a9b204126093663

def z452 : W := mkw 0x7c0ffd2f5bfa000e 0x17c0ffd2f5bfa000 0x1feffc0fffff0007 0xe1feffc0fffff000

def z453 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x5fefffec00000000 0x05fefffec0000000

def z454 : W := mkw 0xe000937f40000008 0x0e000937f4000000 0xfba207ffe0000000 0x3fba207ffe000000

def z455 : W := mkw 0x2080102580042940 0x4208010258004294 0x6670006d8060b9cc 0xf6670006d8060b9c

def z456 : W := mkw 0xbc0f3e7553aa000a 0x1bc0f3e7553aa000 0x11063c71e38f0002 0x111063c71e38f000

def z457 : W := mkw 0x20401025a0052310 0x620401025a005231 0xfff63c7fe09f673f 0x7fff63c7fe09f673

def z458 : W := mkw 0x104e0000b2852310 0x7104e0000b285231 0xbbfe0413ff9f673f 0xfbbfe0413ff9f673

def z459 : W := mkw 0xfe0fffff5ffad40f 0x1fe0fffff5ffad40 0xfffffffffffffe0f 0xffffffffffffffe0

def z460 : W := mkw 0xe00e937f40000008 0x1e00e937f4000000 0xe1ee03ffe0000000 0x3e1ee03ffe000000

def z461 : W := mkw 0x02400080a405e310 0x602400080a405e31 0xfbfa0793fc9fe73f 0xffbfa0793fc9fe73

def z462 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7774386d830c3802 0x37774386d830c380

def z463 : W := mkw 0x820002d00400d401 0x0820002d00400d40 0x400003e000009800 0x0400003e00000980

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000000c000081c8 0x26000000c000081c

def z465 : W := mkw 0xe8809b7fc12c2948 0x4e8809b7fc12c294 0xf7743bffe36cb9ce 0xff7743bffe36cb9c

def z466 : W := mkw 0xc04fa75a60010218 0x3c04fa75a6001021 0x888bc79260934631 0x0888bc7926093463

def z467 : W := mkw 0x920f26d01680d401 0x1920f26d01680d40 0xfffffff01f80fe0b 0xdfffffff01f80fe0

def z468 : W := mkw 0xb20e12f51680d401 0x1b20e12f51680d40 0xf7fe3bfd9f80fe0b 0xff7fe3bfd9f80fe0

def z469 : W := mkw 0x08800800812c2940 0x408800800812c294 0x61740060036cb9ce 0xd61740060036cb9c

def z470 : W := mkw 0xe04fb77fe0052318 0x7e04fb77fe005231 0xffefffffe01f0134 0x3ffefffffe01f013

def z471 : W := mkw 0x0000000000000000 0x0000000000000000 0x0164000003000002 0xc016400000300000

def z472 : W := mkw 0x2080102580042940 0x4208010258004294 0x0000000d800001c0 0x20000000d800001c

def z473 : W := mkw 0x6001b52f40000008 0x06001b52f4000000 0x7f65fc6fe0000000 0x37f65fc6fe000000

def z474 : W := mkw 0x0000000080042100 0x4000000008004210 0x2010000180002108 0x3201000018000210

def z475 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7114386d830cb9ca 0x37114386d830cb9c

def z476 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xf1063fffe0000000 0x3f1063fffe000000

def z477 : W := mkw 0x6880992f812c2940 0x46880992f812c294 0xfffdfbef836cb9ce 0xffffdfbef836cb9c

def z478 : W := mkw 0x3c8f7c251bfa0846 0x13c8f7c251bfa084 0x5feffc6c1fff98c7 0xc5feffc6c1fff98c

def z479 : W := mkw 0x0040000020010210 0x2004000002001021 0x9ba20412609f4637 0x49ba20412609f463

def z480 : W := mkw 0xe88fbf7f41280848 0x1e88fbf7f4128084 0x444dfbec036098c0 0x8444dfbec036098c

def z481 : W := mkw 0x0c0f6c00097a0006 0x10c0f6c00097a000 0x1feffc00007f0004 0x01feffc00007f000

def z482 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe11603f00380fe0a 0x1e11603f00380fe0

def z483 : W := mkw 0x800e025000000000 0x1800e02500000000 0x0106007000000000 0x1010600700000000

def z484 : W := mkw 0x6001b52f40000008 0x06001b52f4000000 0x0401f80c00000000 0x00401f80c0000000

def z485 : W := mkw 0x140f64001ad20006 0x1140f64001ad2000 0x1babc4001c9f0007 0x41babc4001c9f000

def z486 : W := mkw 0x4140c10aa85523b4 0xe4140c10aa85523b 0xbfb3c41fe0ff67ff 0x7bfb3c41fe0ff67f

def z487 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe1ee03f01c804601 0x1e1ee03f01c80460

def z488 : W := mkw 0x1c0f2c0013aa0002 0x11c0f2c0013aa000 0x11ee3c001f8f0003 0xc11ee3c001f8f000

def z489 : W := mkw 0x0000000080042100 0x4000000008004210 0x12000001800c0104 0x212000001800c010

def z490 : W := mkw 0x2880182501280840 0x0288018250128084 0x6664386c036099cc 0xe6664386c036099c

def z491 : W := mkw 0x00400000a0052310 0x600400000a005231 0xa0100013e09f673f 0x7a0100013e09f673

def z492 : W := mkw 0xe30ff7ff4c50c0ac 0x9e30ff7ff4c50c0a 0xffeffffffc6080c0 0xbffeffffffc6080c

def z493 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xfbfe07f3ff80fe0b 0xffbfe07f3ff80fe0

def z494 : W := mkw 0x4000810a00000000 0x04000810a0000000 0xeee9c38e0010413d 0x6eee9c38e0010413

def z495 : W := mkw 0x0080000080042940 0x4008000008004294 0x001000000000b9c8 0x0001000000000b9c

def z496 : W := mkw 0x1f0f6c801ffac0a6 0x91f0f6c801ffac0a 0x1feffc001fffc1ff 0xc1feffc001fffc1f

def z497 : W := mkw 0x0000000000000000 0x0000000000000000 0x4044006003009800 0x8404400600300980

def z498 : W := mkw 0x6041b52fe0052318 0x66041b52fe005231 0xbfb3fc1fe09f673f 0x7bfb3fc1fe09f673

def z499 : W := mkw 0x8000025000001401 0x0800002500000140 0x0010007000003e00 0x10010007000003e0

def z500 : W := mkw 0xa00f367540000008 0x1a00f36754000000 0x0004386000000000 0x0000438600000000

def z501 : W := mkw 0x100e40001ad00004 0x1100e40001ad0000 0x0fefc0001ff00007 0xc0fefc0001ff0000

def z502 : W := mkw 0x4b00c98a0d78c0a4 0x84b00c98a0d78c0a 0xffedfb8e1f7cc1ff 0xeffedfb8e1f7cc1f

def z503 : W := mkw 0x000e000000000000 0x1000e00000000000 0x01ee000000000000 0x001ee00000000000

def z504 : W := mkw 0xe10ff77f485000ac 0x9e10ff77f485000a 0xffefffffe07001f4 0x3ffefffffe07001f

def z505 : W := mkw 0x2000102500000000 0x0200010250000000 0x7774386d8300b80a 0xf7774386d8300b80

def z506 : W := mkw 0x0800080001280000 0x0080008000128000 0x16003800006c0004 0x016003800006c000

def z507 : W := mkw 0x4f01ed8a0d7ac0a6 0x84f01ed8a0d7ac0a 0xfee9ff8e1c7fc1fd 0xefee9ff8e1c7fc1f

def z508 : W := mkw 0x1a80088097acfd41 0x41a80088097acfd4 0x001000001fecffcf 0xc001000001fecffc

def z509 : W := mkw 0x1000000012801401 0x0100000001280140 0x0010000003803e02 0x00010000003803e0

def z510 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x11063c001fff0007 0xc11063c001fff000

def z511 : W := mkw 0x0000400008500004 0x0000040000850000 0xaee9c0021c70413d 0xeaee9c0021c70413

def z512 : W := mkw 0xfc4fff7ffbff231e 0x7fc4fff7ffbff231 0xffffffffffff673f 0xfffffffffffff673

def z513 : W := mkw 0x1c0048001bfa0006 0x01c0048001bfa000 0x000000001f600000 0x8000000001f60000

def z514 : W := mkw 0xc300c3da0c50d4a5 0x8c300c3da0c50d4a 0xeef9c3fe1c70fffd 0xfeef9c3fe1c70fff

def z515 : W := mkw 0x144f6400bad72316 0x7144f6400bad7231 0xbbbbc413fc9f673f 0x7bbbbc413fc9f673

def z516 : W := mkw 0x2880182501280840 0x0288018250128084 0x0400380c006000c0 0x00400380c006000c

def z517 : W := mkw 0x288f3c25812c2940 0x5288f3c25812c294 0x7ffffc6d836cb9ce 0xf7ffffc6d836cb9c

def z518 : W := mkw 0x2080102580042940 0x4208010258004294 0x7774386d8000b9c8 0x37774386d8000b9c

def z519 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7764386d806c01c4 0x37764386d806c01c

def z520 : W := mkw 0x6bc0d9afad7debf4 0xe6bc0d9afad7debf 0xffffffffffffffff 0xffffffffffffffff

def z521 : W := mkw 0x00400000a0052310 0x600400000a005231 0x00000000001f0134 0x000000000001f013

def z522 : W := mkw 0x0000000000000000 0x0000000000000000 0x0ee9c00000000000 0x00ee9c0000000000

def z523 : W := mkw 0x3c8058259bfe2946 0x43c8058259bfe294 0x7774386d9fffb9cf 0xf7774386d9fffb9c

def z524 : W := mkw 0x120000801680d401 0x0120000801680d40 0xe0f803801f80fe0b 0xce0f803801f80fe0

def z525 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xee01c38e0070c1fc 0x2ee01c38e0070c1f

def z526 : W := mkw 0x4100c10a085000a4 0x84100c10a085000a 0x0ee9c00e1c7001f5 0xe0ee9c00e1c7001f

def z527 : W := mkw 0x9e0f6ed01ffad407 0x19e0f6ed01ffad40 0x9fefff901fff4607 0xc9fefff901fff460

def z528 : W := mkw 0xd30ec3da1ed0d4a5 0x9d30ec3da1ed0d4a 0xeeedc3ee1f70d9fd 0xeeeedc3ee1f70d9f

def z529 : W := mkw 0x28801825812c2940 0x428801825812c294 0x10003801800c0000 0x010003801800c000

def z530 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbbb20413e08f2602 0x3bbb20413e08f260

def z531 : W := mkw 0x4340c18aac55e3b4 0xe4340c18aac55e3b 0xeef9c39ffc70e7fd 0xfeef9c39ffc70e7f

def z532 : W := mkw 0xf20e93ff5680d409 0x1f20e93ff5680d40 0xe1fe03ffff80fe0b 0xfe1fe03ffff80fe0

def z533 : W := mkw 0x020000800400c000 0x0020000800400c00 0x808803801c004001 0x0808803801c00400

def z534 : W := mkw 0x4000810a00000000 0x04000810a0000000 0xeee9c38e006081cc 0xeeee9c38e006081c

def z535 : W := mkw 0x820002d00400d401 0x0820002d00400d40 0xe1b203f00080fe0b 0x5e1b203f00080fe0

def z536 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x81ee03901f804603 0xc81ee03901f80460

def z537 : W := mkw 0x0800080001280000 0x0080008000128000 0x7764380c036c81ce 0xe7764380c036c81c

def z538 : W := mkw 0x100e000012800000 0x1100e00001280000 0xa1fe00101f80660b 0xda1fe00101f80660

def z539 : W := mkw 0x020000800400c000 0x0020000800400c00 0xe1fa03901c80e60b 0xde1fa03901c80e60

def z540 : W := mkw 0x4300818a0400c0a0 0x84300818a0400c0a 0x8000038200004030 0x0800003820000403

def z541 : W := mkw 0x6300d1af0c50c0a4 0x86300d1af0c50c0a 0xffedfbef9c70c1fd 0xfffedfbef9c70c1f

def z542 : W := mkw 0xc04fa75ae0052318 0x7c04fa75ae005231 0xbbbbc793e09f673f 0x7bbbbc793e09f673

def z543 : W := mkw 0x1c0f2c0013aa0002 0x11c0f2c0013aa000 0x1feffc00038f0002 0x01feffc00038f000

def z544 : W := mkw 0xba8e1af597acfd41 0x5ba8e1af597acfd4 0x777c3bed9f6cb9ce 0xf777c3bed9f6cb9c

def z545 : W := mkw 0x1c4f6c00bbff2316 0x71c4f6c00bbff231 0x1feffc03ffff0137 0xe1feffc03ffff013

def z546 : W := mkw 0x960f66d01ed2d407 0x1960f66d01ed2d40 0xe9ffc7f01f93fe0b 0xde9ffc7f01f93fe0

def z547 : W := mkw 0xba8e1af517a8dc41 0x1ba8e1af517a8dc4 0xe5fe3bfc1fe0fecb 0xde5fe3bfc1fe0fec

def z548 : W := mkw 0xe88fbf7fc12c2948 0x5e88fbf7fc12c294 0x777dfbed836cb9ce 0xf777dfbed836cb9c

def z549 : W := mkw 0x0000000000000000 0x0000000000000000 0x1764380000000000 0x0176438000000000

def z550 : W := mkw 0x0000000000000000 0x0000000000000000 0xbbb20410009f660f 0x5bbb20410009f660

def z551 : W := mkw 0x144f64003ad30216 0x3144f64003ad3021 0x888bc4127c934631 0x0888bc4127c93463

def z552 : W := mkw 0x1c4f2c00b3af2312 0x71c4f2c00b3af231 0x11163c11e38f2602 0x111163c11e38f260

def z553 : W := mkw 0x100e000012800000 0x1100e00001280000 0x004c00001f000000 0x8004c00001f00000

def z554 : W := mkw 0x020000800400c000 0x0020000800400c00 0x404803801c008000 0x8404803801c00800

def z555 : W := mkw 0x00400000a0052310 0x600400000a005231 0x1a100403e09f673f 0x61a100403e09f673

def z556 : W := mkw 0x4200818a0400c000 0x04200818a0400c00 0xeee9c38e1c00c009 0xeeee9c38e1c00c00

def z557 : W := mkw 0x5f0fed8a1ffac0a6 0x95f0fed8a1ffac0a 0xeeedfb8e1f70c1fd 0xeeeedfb8e1f70c1f

def z558 : W := mkw 0x9e0f6ed01ffad407 0x19e0f6ed01ffad40 0x5fefffe01fff9807 0xc5fefffe01fff980

def z559 : W := mkw 0x100e000012800000 0x1100e00001280000 0x0106000003800002 0x0010600000380000

def z560 : W := mkw 0x020000800400c000 0x0020000800400c00 0x000000001c00c009 0xc000000001c00c00

def z561 : W := mkw 0x0000000000000000 0x0000000000000000 0x11020411e0000000 0x111020411e000000

def z562 : W := mkw 0x28801825812c2940 0x428801825812c294 0x1610380d836cb9ce 0xe1610380d836cb9c

def z563 : W := mkw 0xe88fbf7f41280848 0x1e88fbf7f4128084 0xffefffffe36098c0 0xbffefffffe36098c

def z564 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x05eff8001fe00003 0xc05eff8001fe0000

def z565 : W := mkw 0x6001b52f40000008 0x06001b52f4000000 0xbfa3fc1fe0000000 0x3bfa3fc1fe000000

def z566 : W := mkw 0xc30ec3da0c50c0a4 0x9c30ec3da0c50c0a 0xefefc3fe1c70c1fd 0xfefefc3fe1c70c1f

def z567 : W := mkw 0x120e00801680c000 0x1120e00801680c00 0xe1ee03801f80c00b 0xce1ee03801f80c00

def z568 : W := mkw 0x0000000080042100 0x4000000008004210 0xb3b20011808c670f 0x7b3b20011808c670

def z569 : W := mkw 0x2000102500000000 0x0200010250000000 0x7764386d806081cc 0xf7764386d806081c

def z570 : W := mkw 0x0000000000000000 0x0000000000000000 0x213000000000200a 0x5213000000000200

def z571 : W := mkw 0x08400800a12d2310 0x608400800a12d231 0xbff63c13e3ff673f 0xfbff63c13e3ff673

def z572 : W := mkw 0xd30ec3da1ed0d4a5 0x9d30ec3da1ed0d4a 0x888bc3921c904631 0x0888bc3921c90463

def z573 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbaa00403e01f413d 0x6baa00403e01f413

def z574 : W := mkw 0x00400000a0052310 0x600400000a005231 0xaab00013e010673d 0x7aab00013e010673

def z575 : W := mkw 0x00400000a0052310 0x600400000a005231 0x00100000008f2602 0x000100000008f260

def z576 : W := mkw 0x4340c18aac55e3b4 0xe4340c18aac55e3b 0xfee9c78ffc7fc1fd 0xefee9c78ffc7fc1f

def z577 : W := mkw 0x00400000a0052310 0x600400000a005231 0x88920412609f673f 0x488920412609f673

def z578 : W := mkw 0x0000000000000000 0x0000000000000000 0x13200000000c0006 0x413200000000c000

def z579 : W := mkw 0xf20fb7ff5680d409 0x1f20fb7ff5680d40 0xe5fffbfc1f80fe0b 0xde5fffbfc1f80fe0

def z580 : W := mkw 0x0000000000000000 0x0000000000000000 0x0114006003003802 0x1011400600300380

def z581 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x011600701f80fe0b 0xd011600701f80fe0

def z582 : W := mkw 0x28801825812c2940 0x428801825812c294 0x71743861830cb80a 0xd71743861830cb80

def z583 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xaaa9c3821c10413d 0x6aaa9c3821c10413

def z584 : W := mkw 0x0c016c00097a0006 0x00c016c00097a000 0x1fa3fc0000ff0007 0x41fa3fc0000ff000

def z585 : W := mkw 0x900e025012801401 0x1900e02501280140 0x0004006003001800 0x0000400600300180

def z586 : W := mkw 0x6101f52f485000ac 0x86101f52f485000a 0x1e01fc0fe07001f4 0x21e01fc0fe07001f

def z587 : W := mkw 0xe300d3ff4c50c0ac 0x8e300d3ff4c50c0a 0xeee9c3fffc70c1fd 0xfeee9c3fffc70c1f

def z588 : W := mkw 0x6980d92f897c29e4 0xc6980d92f897c29e 0x7f75f86f837cb9fe 0xf7f75f86f837cb9f

def z589 : W := mkw 0x140f240012820002 0x1140f24001282000 0x0002040000830000 0x0000204000083000

def z590 : W := mkw 0xec0fff7f497a000e 0x1ec0fff7f497a000 0xffefffffe07f0004 0x3ffefffffe07f000

def z591 : W := mkw 0x030040800c50c0a4 0x8030040800c50c0a 0x0ee9c0001c70c1fd 0xc0ee9c0001c70c1f

def z592 : W := mkw 0xc00fa75a40000008 0x1c00fa75a4000000 0xbbabc793e0000000 0x3bbabc793e000000

def z593 : W := mkw 0x28801825812c2940 0x428801825812c294 0x17743861836c3806 0xd17743861836c380

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0xaaa0000200000000 0x2aaa000020000000

def z595 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1feffc001f600000 0x81feffc001f60000

def z596 : W := mkw 0xa28012f58404fd41 0x4a28012f58404fd4 0xe01003fd8000ffc8 0x3e01003fd8000ffc

def z597 : W := mkw 0x03404080ac55e3b4 0xe03404080ac55e3b 0xbbb20413fcffe7ff 0xfbbb20413fcffe7f

def z598 : W := mkw 0xf20fb7ff5680d409 0x1f20fb7ff5680d40 0x444dfbec1f009800 0x8444dfbec1f00980

def z599 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x8ee9c3821c704035 0xc8ee9c3821c70403

def z600 : W := mkw 0x2001342540000008 0x0200134254000000 0x10003c01e0000000 0x010003c01e000000

def z601 : W := mkw 0x0000000000000000 0x0000000000000000 0x601000600000b808 0x1601000600000b80

def z602 : W := mkw 0x4340818aa405e3b0 0xe4340818aa405e3b 0xfbb2079fe09fe7ff 0x7fbb2079fe09fe7f

def z603 : W := mkw 0x00400000a0052310 0x600400000a005231 0x1b120413e09f2736 0x31b120413e09f273

def z604 : W := mkw 0xc30fe7da4c50c0ac 0x9c30fe7da4c50c0a 0x888bc7927c104031 0x0888bc7927c10403

def z605 : W := mkw 0x3c8f3c2593ae2942 0x53c8f3c2593ae294 0x77763c6d83efb9ce 0xf77763c6d83efb9c

def z606 : W := mkw 0x4040810aa0052310 0x64040810aa005231 0xfffbc79fe09f673f 0x7fffbc79fe09f673

def z607 : W := mkw 0x28801825812c2940 0x428801825812c294 0x11143861836cb9ce 0xd11143861836cb9c

def z608 : W := mkw 0xd20e83da1680d401 0x1d20e83da1680d40 0xefffc3fe1f80fe0b 0xfefffc3fe1f80fe0

def z609 : W := mkw 0x800f265000000000 0x1800f26500000000 0xffeffff000000000 0x1ffeffff00000000

def z610 : W := mkw 0xba8e1af517a8dc41 0x1ba8e1af517a8dc4 0x444c3bec1f6098c0 0x8444c3bec1f6098c

def z611 : W := mkw 0x08000800812c2100 0x408000800812c210 0x37743801836c210e 0xf37743801836c210

def z612 : W := mkw 0x6b8099af852ce9e0 0xc6b8099af852ce9e 0xf7743bef836cf9fe 0xff7743bef836cf9f

def z613 : W := mkw 0x0c416c00a97f2316 0x60c416c00a97f231 0xbfb3fc13e0ff673f 0x7bfb3fc13e0ff673

def z614 : W := mkw 0xc00fa75a40000008 0x1c00fa75a4000000 0xeeebc79e60000000 0x2eeebc79e6000000

def z615 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xe5effbfc00000000 0x1e5effbfc0000000

def z616 : W := mkw 0x00400000a0052310 0x600400000a005231 0xa1b20013e080673b 0x7a1b20013e080673

def z617 : W := mkw 0x140f64001ad20006 0x1140f64001ad2000 0x09efc4001f930003 0xc09efc4001f93000

def z618 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbba20413e01f0134 0x3bba20413e01f013

def z619 : W := mkw 0x3a8018a597acfd41 0x43a8018a597acfd4 0x7774386d9fecffcf 0xf7774386d9fecffc

def z620 : W := mkw 0xf20fb7ff5680d409 0x1f20fb7ff5680d40 0xffeffffffc804601 0x3ffeffffffc80460

def z621 : W := mkw 0x900e025012801401 0x1900e02501280140 0xe1fe03f003803e02 0x1e1fe03f003803e0

def z622 : W := mkw 0x0000000080042100 0x4000000008004210 0xbbb00003801c613f 0x7bbb00003801c613

def z623 : W := mkw 0x0000000000000000 0x0000000000000000 0x8880000200104031 0x0888000020010403

def z624 : W := mkw 0x0c012c00012a0002 0x00c012c00012a000 0x10003c00000f0000 0x010003c00000f000

def z625 : W := mkw 0x4100c10a085000a4 0x84100c10a085000a 0xeee9c38e007001f4 0x2eee9c38e007001f

def z626 : W := mkw 0xfc0fff7f5bfa000e 0x1fc0fff7f5bfa000 0x5fefffec1fff0007 0xc5fefffec1fff000

def z627 : W := mkw 0x824002d0a405f711 0x6824002d0a405f71 0xfbb207f3e09fff3f 0x7fbb207f3e09fff3

def z628 : W := mkw 0xe040937fe0052318 0x6e040937fe005231 0xfbb207ffe09f673f 0x7fbb207ffe09f673

def z629 : W := mkw 0xfa8fbfffd7acfd49 0x5fa8fbfffd7acfd4 0xffffffffffecffcf 0xfffffffffffecffc

def z630 : W := mkw 0x0000000000000000 0x0000000000000000 0x001000000300b80a 0xc001000000300b80

def z631 : W := mkw 0x28801825812c2940 0x428801825812c294 0x4454386c036cb9ce 0xc4454386c036cb9c

def z632 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xbfb23c1fe0ff67ff 0x7bfb23c1fe0ff67f

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000000200004138 0x2a00000020000413

def z634 : W := mkw 0x924e02d03681d611 0x3924e02d03681d61 0x888a07927c934631 0x0888a07927c93463

def z635 : W := mkw 0x900e025012800000 0x1900e02501280000 0xe1ee03f01f800003 0xde1ee03f01f80000

def z636 : W := mkw 0x030000800400c0a0 0x8030000800400c0a 0x000000000000c1f8 0x0000000000000c1f

def z637 : W := mkw 0x9a0e0ad017a8d401 0x19a0e0ad017a8d40 0xf7fe3bf01fecfe0f 0xdf7fe3bf01fecfe0

def z638 : W := mkw 0xc00fa75a40000008 0x1c00fa75a4000000 0xe9efc7f260000000 0x1e9efc7f26000000

def z639 : W := mkw 0xa00f367540000008 0x1a00f36754000000 0xf1ee3ff1e0000000 0x1f1ee3ff1e000000

def z640 : W := mkw 0x800e025000000000 0x1800e02500000000 0x404c03e000000000 0x0404c03e00000000

def z641 : W := mkw 0xc00fa75a40000008 0x1c00fa75a4000000 0x9fefff9260000000 0x09fefff926000000

def z642 : W := mkw 0x000f640008500004 0x1000f64000850000 0x1feffc001c700005 0xc1feffc001c70000

def z643 : W := mkw 0x2800182501280000 0x0280018250128000 0x7764386d836c0006 0xf7764386d836c000

def z644 : W := mkw 0x900e025012801401 0x1900e02501280140 0xa1b6007003807e0b 0x5a1b6007003807e0

def z645 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xe8e9c3821c10c039 0xce8e9c3821c10c03

def z646 : W := mkw 0x6b80d9af8d7ce9e4 0xc6b80d9af8d7ce9e 0x777dfbed9f6cb9ce 0xf777dfbed9f6cb9c

def z647 : W := mkw 0x9e0f2ed017aad403 0x19e0f2ed017aad40 0xf1fe3ff01f8ffe0b 0xdf1fe3ff01f8ffe0

def z648 : W := mkw 0x120000801680d401 0x0120000801680d40 0x000000001c804601 0x0000000001c80460

def z649 : W := mkw 0x00400000a0052310 0x600400000a005231 0xba100413e01f673c 0x3ba100413e01f673

def z650 : W := mkw 0x1000000012800000 0x0100000001280000 0x000000001f800003 0xc000000001f80000

def z651 : W := mkw 0x00400000a0052310 0x600400000a005231 0x1ba20403e09f0137 0x61ba20403e09f013

def z652 : W := mkw 0x0000000080042100 0x4000000008004210 0x11100001800c2002 0x111100001800c200

def z653 : W := mkw 0x4340c18a2c51c2b4 0xa4340c18a2c51c2b 0x888bc7927c934631 0x0888bc7927c93463

def z654 : W := mkw 0xe30fb7ff4400c0a8 0x9e30fb7ff4400c0a 0xffefffffe000c1f8 0x3ffefffffe000c1f

def z655 : W := mkw 0x4100c10a085000a4 0x84100c10a085000a 0x6e61c00e007081fc 0xe6e61c00e007081f

def z656 : W := mkw 0xdc0fef5a5bfa000e 0x1dc0fef5a5bfa000 0x9fefff927fff0007 0xc9fefff927fff000

def z657 : W := mkw 0x530ec18a1ed0c0a4 0x9530ec18a1ed0c0a 0xefefc38e1ff0c1ff 0xeefefc38e1ff0c1f

def z658 : W := mkw 0x1c0f2c0013aa0002 0x11c0f2c0013aa000 0x1ba63c00039f0007 0x41ba63c00039f000

def z659 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7610386d806cb9cc 0x37610386d806cb9c

def z660 : W := mkw 0xa04f3675e0052318 0x7a04f3675e005231 0xbbb63c73e09f673f 0x7bbb63c73e09f673

def z661 : W := mkw 0x570fe58a1ed2c0a6 0x9570fe58a1ed2c0a 0xeeebc78e1cf3c1fd 0xeeeebc78e1cf3c1f

def z662 : W := mkw 0xa00f367540000008 0x1a00f36754000000 0x1feffc71e0000000 0x11feffc71e000000

def z663 : W := mkw 0x804e0250a0052310 0x7804e0250a005231 0xfbfe07f3e09f673f 0x7fbfe07f3e09f673

def z664 : W := mkw 0x0800080001280000 0x0080008000128000 0x77743860036cb80e 0xd77743860036cb80

def z665 : W := mkw 0x120e00801680d401 0x1120e00801680d40 0x01fe00001f80fe0b 0xc01fe00001f80fe0

def z666 : W := mkw 0x1c0f2c0013aa0002 0x11c0f2c0013aa000 0x17663c0003ef0006 0xc17663c0003ef000

def z667 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x176df8001f6c0006 0xc176df8001f6c000

def z668 : W := mkw 0x2080102580042940 0x4208010258004294 0x6174006d8300b9ca 0xf6174006d8300b9c

def z669 : W := mkw 0x12400080b685f711 0x612400080b685f71 0x001000001f9fff3f 0xc001000001f9fff3

def z670 : W := mkw 0x1e0048801ffad407 0x01e0048801ffad40 0x001000001ffffe0f 0xc001000001ffffe0

def z671 : W := mkw 0xe30093ff4400c0a8 0x8e30093ff4400c0a 0xe00003ffe000c1f8 0x3e00003ffe000c1f

def z672 : W := mkw 0xdf0fefda1ffad4a7 0x9df0fefda1ffad4a 0xfffffffe1fffffff 0xffffffffe1ffffff

def z673 : W := mkw 0xba8e1af597acfd41 0x5ba8e1af597acfd4 0xf1fe3bf19f8cfe0b 0xdf1fe3bf19f8cfe0

def z674 : W := mkw 0x030040800c50c0a4 0x8030040800c50c0a 0x6660000c1c70c1fd 0xe6660000c1c70c1f

def z675 : W := mkw 0xe00ff77f4850000c 0x1e00ff77f4850000 0xffeffffffc700005 0xfffeffffffc70000

def z676 : W := mkw 0x9c0f2e5013aa1403 0x19c0f2e5013aa140 0x11163c70038f3e02 0x111163c70038f3e0

def z677 : W := mkw 0x0800480009780004 0x0080048000978000 0x1fedf8001f7c0007 0xc1fedf8001f7c000

def z678 : W := mkw 0xbc0f7e755bfa000e 0x1bc0f7e755bfa000 0x1feffc71ffff0007 0xd1feffc71ffff000

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a00000200100134 0x20a0000020010013

def z680 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe0ea03901c80c609 0xce0ea03901c80c60

def z681 : W := mkw 0x08c00800a12d2b50 0x608c00800a12d2b5 0xbbb20413e3ffffff 0xfbbb20413e3fffff

def z682 : W := mkw 0x0000000080042100 0x4000000008004210 0x00100000000c210e 0x400100000000c210

def z683 : W := mkw 0xd30ec3da1ed0d4a5 0x9d30ec3da1ed0d4a 0xe5ffc3fc1fe0fecb 0xde5ffc3fc1fe0fec

def z684 : W := mkw 0x030040800c50c0a4 0x8030040800c50c0a 0x000000001c6080c0 0x8000000001c6080c

def z685 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xe4e9c38c1c60c0c9 0xce4e9c38c1c60c0c

def z686 : W := mkw 0xf20fb7ff5680d409 0x1f20fb7ff5680d40 0xffefffffff009800 0xbffefffffff00980

def z687 : W := mkw 0x00400000a0052310 0x600400000a005231 0x0010000000006738 0x0001000000000673

def z688 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe1ee03f01f009800 0x9e1ee03f01f00980

def z689 : W := mkw 0x020000800400c000 0x0020000800400c00 0xe1fc03e01f00f80b 0xde1fc03e01f00f80

def z690 : W := mkw 0x800f265040000008 0x1800f26504000000 0x0002041060000000 0x0000204106000000

def z691 : W := mkw 0x5300c18a1ed0d4a5 0x85300c18a1ed0d4a 0xeef9c38e1ff0ffff 0xeeef9c38e1ff0fff

def z692 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x41ee03e01f809803 0xc41ee03e01f80980

def z693 : W := mkw 0x0000400008500004 0x0000040000850000 0x0449c0001c600000 0x80449c0001c60000

def z694 : W := mkw 0x4000810a00000000 0x04000810a0000000 0x8889c38200000000 0x08889c3820000000

def z695 : W := mkw 0x2a8018a5852ce940 0x42a8018a5852ce94 0xf7fc3bed9f6cf9cf 0xff7fc3bed9f6cf9c

def z696 : W := mkw 0xe34ff7ffec55e3bc 0xfe34ff7ffec55e3b 0xfffffffffcffe7ff 0xffffffffffcffe7f

def z697 : W := mkw 0x924e02d0b685f711 0x7924e02d0b685f71 0xe1fe03f01f9fff3f 0xde1fe03f01f9fff3

def z698 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0000013e0000000 0x3a0000013e000000

def z699 : W := mkw 0xb88e1a7593ac3d41 0x5b88e1a7593ac3d4 0x11163871838c3e02 0x111163871838c3e0

def z700 : W := mkw 0x08800800812c2940 0x408800800812c294 0x6670000c036cb9ce 0xe6670000c036cb9c

def z701 : W := mkw 0x0c016c00097a0006 0x00c016c00097a000 0x0401f80000600000 0x00401f8000060000

def z702 : W := mkw 0x100e000012800000 0x1100e00001280000 0x008a00001c800001 0x0008a00001c80000

def z703 : W := mkw 0xe000937f40000008 0x0e000937f4000000 0xf7643bffe0000000 0x3f7643bffe000000

def z704 : W := mkw 0xd30ec3da1ed0d4a5 0x9d30ec3da1ed0d4a 0xeeebc39e1cf0c7fd 0xeeeebc39e1cf0c7f

def z705 : W := mkw 0xf40ff77f5ad2000e 0x1f40ff77f5ad2000 0xffeffffffc930001 0x3ffeffffffc93000

def z706 : W := mkw 0x924e02d0b685f711 0x7924e02d0b685f71 0xbbba0793fc9f673f 0x7bbba0793fc9f673

def z707 : W := mkw 0x28c0182521290a50 0x228c0182521290a5 0xccc63c7e63f3def1 0x8ccc63c7e63f3def

def z708 : W := mkw 0x2880182501280840 0x0288018250128084 0xe5f6387c03e0fecb 0xde5f6387c03e0fec

def z709 : W := mkw 0x0c016c00097a0006 0x00c016c00097a000 0x1e89fc001c7f0005 0x01e89fc001c7f000

def z710 : W := mkw 0xba8e1af597acfd41 0x5ba8e1af597acfd4 0x968a3b9d9cec47c5 0x2968a3b9d9cec47c

def z711 : W := mkw 0x100f240012800000 0x1100f24001280000 0x1feffc001f9f0007 0xc1feffc001f9f000

def z712 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xffe9c38f9c70c1fd 0xfffe9c38f9c70c1f

def z713 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x4449c38c1c60c1f8 0x84449c38c1c60c1f

def z714 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe070c1fd 0xfffefffffe070c1f

def z715 : W := mkw 0x920f26d01680d401 0x1920f26d01680d40 0xfffffff01f9ffe0f 0xdfffffff01f9ffe0

def z716 : W := mkw 0x020000800400c000 0x0020000800400c00 0xe1fe03f01f80fe0b 0xde1fe03f01f80fe0

def z717 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe3009800 0xbffefffffe300980

def z718 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x15effc001fef0003 0xc15effc001fef000

def z719 : W := mkw 0xf00fb77f52801409 0x1f00fb77f5280140 0xffefffffe3001800 0x3ffefffffe300180

def z720 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1feffc11ffff0007 0xd1feffc11ffff000

def z721 : W := mkw 0x6b80d9af8d7ce9e4 0xc6b80d9af8d7ce9e 0x999dfbe39f1c7833 0x1999dfbe39f1c783

def z722 : W := mkw 0x0c016c00097a0006 0x00c016c00097a000 0x1febfc001cff0007 0xc1febfc001cff000

def z723 : W := mkw 0x0800080001280000 0x0080008000128000 0x7774386c036cb9ce 0xf7774386c036cb9c

def z724 : W := mkw 0xf00fb77f52800008 0x1f00fb77f5280000 0xffffffffff80660b 0xfffffffffff80660

def z725 : W := mkw 0xe10fb77f400000a8 0x9e10fb77f400000a 0xffefffffe00001f0 0x3ffefffffe00001f

def z726 : W := mkw 0x2880182501280840 0x0288018250128084 0x4564386c036098c2 0xc4564386c036098c

def z727 : W := mkw 0x000f640008500004 0x1000f64000850000 0x1feffc001cff0007 0xc1feffc001cff000

def z728 : W := mkw 0x7201b5af5680d409 0x07201b5af5680d40 0x1e11fc0fff80fe0b 0xe1e11fc0fff80fe0

def z729 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xf1fe07f01f8ffe0b 0xdf1fe07f01f8ffe0

def z730 : W := mkw 0x348f74259ad62946 0x5348f74259ad6294 0x689bc46d9c93b9c9 0x3689bc46d9c93b9c

def z731 : W := mkw 0x5f0fad8a17aac0a2 0x95f0fad8a17aac0a 0xf1063f8e038fc1fa 0x2f1063f8e038fc1f

def z732 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1f07fc001fff0007 0xc1f07fc001fff000

def z733 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7774386d836cb8c2 0xb7774386d836cb8c

def z734 : W := mkw 0x28801825812c2940 0x428801825812c294 0x5764386d836c99c6 0xe5764386d836c99c

def z735 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xaea9c38e1c7041fd 0x6aea9c38e1c7041f

def z736 : W := mkw 0x900e025012801401 0x1900e02501280140 0xe1fe03f01f803e03 0xde1fe03f01f803e0

def z737 : W := mkw 0x2880182501280840 0x0288018250128084 0x5644386d836098c0 0xa5644386d836098c

def z738 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xe4e9c38e1c60c1f9 0xee4e9c38e1c60c1f

def z739 : W := mkw 0x1c4f6c00bbff2316 0x71c4f6c00bbff231 0xa45df813ff606738 0xba45df813ff60673

def z740 : W := mkw 0xd10ec35a1ad014a5 0x9d10ec35a1ad014a 0x0f17c07e03f03ff6 0x30f17c07e03f03ff

def z741 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xbbaffff3e0000000 0x3bbaffff3e000000

def z742 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1fabfc001cff0007 0x41fabfc001cff000

def z743 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe1fe03f01f9ffe0f 0xde1fe03f01f9ffe0

def z744 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x5feffc0c1fff80c7 0xc5feffc0c1fff80c

def z745 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe1fe03f01f90ff3f 0xde1fe03f01f90ff3

def z746 : W := mkw 0x0c016c00097a0006 0x00c016c00097a000 0x1fedfc001f7f0007 0xc1fedfc001f7f000

def z747 : W := mkw 0x0bc04880ad7debf4 0xe0bc04880ad7debf 0x001000001fffffff 0xc001000001ffffff

def z748 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffffffffe380fe0b 0xfffffffffe380fe0

def z749 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x7774386d836cfffe 0xf7774386d836cfff

def z750 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x776ffffde0000000 0x3776ffffde000000

def z751 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xefedc38e1f70c1ff 0xeefedc38e1f70c1f

def z752 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7ffdf86d836cb9ce 0xf7ffdf86d836cb9c

def z753 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xfbfe07f21f9fff3f 0xffbfe07f21f9fff3

def z754 : W := mkw 0x2880182501280840 0x0288018250128084 0x4444386c036c98c6 0xc4444386c036c98c

def z755 : W := mkw 0xc88faf5ac12c2948 0x5c88faf5ac12c294 0x889bc792636cb9ce 0xc889bc792636cb9c

def z756 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0xbfeffc13ffff413f 0xfbfeffc13ffff413

def z757 : W := mkw 0x600fb52f40000008 0x1600fb52f4000000 0xffefff8fe0000000 0x2ffefff8fe000000

def z758 : W := mkw 0x28801825812c2940 0x428801825812c294 0x4454386c0360b9c8 0x84454386c0360b9c

def z759 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffffffffe090673f 0x7ffffffffe090673

def z760 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x110ffff1e0000000 0x1110ffff1e000000

def z761 : W := mkw 0xa30f76f54c50c0ac 0x9a30f76f54c50c0a 0x11063c71fc70c1fd 0xd11063c71fc70c1f

def z762 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe0104031 0x3ffefffffe010403

def z763 : W := mkw 0x28801825812c2940 0x428801825812c294 0xfff63c7fe37cf9ff 0xffff63c7fe37cf9f

def z764 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1e4dfc001fff0007 0xc1e4dfc001fff000

def z765 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x7feffc0c1fff0007 0xe7feffc0c1fff000

def z766 : W := mkw 0xe001b77f40000008 0x0e001b77f4000000 0xffa3ffffe0000000 0x3ffa3ffffe000000

def z767 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xff07ffffe0000000 0x3ff07ffffe000000

def z768 : W := mkw 0x8e016ed00d7ad407 0x08e016ed00d7ad40 0xfe11fff0007ffe0c 0x1fe11fff0007ffe0

def z769 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xfff63c7fe37fb9fe 0xffff63c7fe37fb9f

def z770 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeee9c39ffc70c1fd 0xfeee9c39ffc70c1f

def z771 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x5f4fffffe0000000 0x35f4fffffe000000

def z772 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xefffc3f01f80fe0b 0xdefffc3f01f80fe0

def z773 : W := mkw 0xf00fb77f52801409 0x1f00fb77f5280140 0xffffffffff803e03 0xfffffffffff803e0

def z774 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xf9effff3e0000000 0x1f9effff3e000000

def z775 : W := mkw 0x4340c18aac55e3b4 0xe4340c18aac55e3b 0x555bc79dfcefa6c2 0x9555bc79dfcefa6c

def z776 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x8e89c38e1c70c1fd 0xe8e89c38e1c70c1f

def z777 : W := mkw 0x28801825812c2940 0x428801825812c294 0xfff6387f83fcffff 0xffff6387f83fcfff

def z778 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xeccfffffe0000000 0x3eccfffffe000000

def z779 : W := mkw 0x1e404880bffff717 0x61e404880bffff71 0x001000001fffff3f 0xc001000001fffff3

def z780 : W := mkw 0xe001b77f40000008 0x0e001b77f4000000 0xe401fbffe0000000 0x3e401fbffe000000

def z781 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe1fe03f01f807e03 0x1e1fe03f01f807e0

def z782 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe5fe03fc1fe0fecb 0xde5fe03fc1fe0fec

def z783 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xecc9c38e1c70c1f9 0xaecc9c38e1c70c1f

def z784 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x0e09c38e1c7001f4 0x20e09c38e1c7001f

def z785 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xa1be03f01f807e0b 0x5a1be03f01f807e0

def z786 : W := mkw 0x1c0f2c0013aa0002 0x11c0f2c0013aa000 0x1feffc001f8f0003 0xc1feffc001f8f000

def z787 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x5e443c6fe37f99f4 0xa5e443c6fe37f99f

def z788 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbbb60473e39f7f3f 0x7bbb60473e39f7f3

def z789 : W := mkw 0x69c0d92fa97d2bf4 0xe69c0d92fa97d2bf 0x1e01fc0fe07f01f4 0x21e01fc0fe07f01f

def z790 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe0fc03f01f00fe09 0xde0fc03f01f00fe0

def z791 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xf98fffffe0000000 0x3f98fffffe000000

def z792 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xfffbc79e1cffe7ff 0xffffbc79e1cffe7f

def z793 : W := mkw 0x00400000a0052310 0x600400000a005231 0x9b920413e09f6737 0x39b920413e09f673

def z794 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0xfffffc701ffffe0f 0xdfffffc701ffffe0

def z795 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbbf60413e39f673f 0xfbbf60413e39f673

def z796 : W := mkw 0x2880182501280840 0x0288018250128084 0x7764386c036c99ce 0xe7764386c036c99c

def z797 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x7ffffc6c1fffb9cf 0xf7ffffc6c1fffb9c

def z798 : W := mkw 0x28801825812c2940 0x428801825812c294 0x5774386d836cb8c6 0xd5774386d836cb8c

def z799 : W := mkw 0x920f26d01680d401 0x1920f26d01680d40 0xf1fe3ff01f80fe0b 0xdf1fe3ff01f80fe0

def z800 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x7774387de36cbfce 0xf7774387de36cbfc

def z801 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xefffc3fe1ff0ffff 0xfefffc3fe1ff0fff

def z802 : W := mkw 0x800f265000000000 0x1800f26500000000 0xffeffff3e0000000 0x3ffeffff3e000000

def z803 : W := mkw 0x28801825812c2940 0x428801825812c294 0xfff63c7fe3ecffcf 0xffff63c7fe3ecffc

def z804 : W := mkw 0xc00fa75a40000008 0x1c00fa75a4000000 0xbfefff93e0000000 0x3bfefff93e000000

def z805 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe11603f01f80fe0b 0xde11603f01f80fe0

def z806 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x198ffc001fff0007 0xc198ffc001fff000

def z807 : W := mkw 0x0040000020010210 0x2004000002001021 0xbba20413e09f4637 0x7bba20413e09f463

def z808 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xfff63c7fe3efbfce 0xffff63c7fe3efbfc

def z809 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1feffc001f7f0004 0x81feffc001f7f000

def z810 : W := mkw 0xe001b77f40000008 0x0e001b77f4000000 0x9e01ff9fe0000000 0x29e01ff9fe000000

def z811 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x9feffff3e0000000 0x19feffff3e000000

def z812 : W := mkw 0xfc00db7f5bfa000e 0x0fc00db7f5bfa000 0xe00003ffffff0007 0xfe00003ffffff000

def z813 : W := mkw 0x820002d00400d401 0x0820002d00400d40 0xe1fc03f01f00fe0b 0xde1fc03f01f00fe0

def z814 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1ffffc101fff2607 0xd1ffffc101fff260

def z815 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x4454386c03ffffff 0xc4454386c03fffff

def z816 : W := mkw 0x00400000a0052310 0x600400000a005231 0x9ba20413e09f4737 0x69ba20413e09f473

def z817 : W := mkw 0x00400000a0052310 0x600400000a005231 0xfff6047fe3ffffff 0xffff6047fe3fffff

def z818 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe00081c8 0x3ffefffffe00081c

def z819 : W := mkw 0x6001b52f40000008 0x06001b52f4000000 0x9e89ff8fe0000000 0x29e89ff8fe000000

def z820 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x5feffffde0000000 0x15feffffde000000

def z821 : W := mkw 0x2880182501280840 0x0288018250128084 0x4644386c036099c4 0xa4644386c036099c

def z822 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe1fe03f01f00fe08 0x9e1fe03f01f00fe0

def z823 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe15e03f01f80fe0a 0x9e15e03f01f80fe0

def z824 : W := mkw 0xf00fb77f52800008 0x1f00fb77f5280000 0xffefffffe3800002 0x3ffefffffe380000

def z825 : W := mkw 0x00400000a0052310 0x600400000a005231 0xfbfa0793e09f673f 0x7fbfa0793e09f673

def z826 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xf76dfbffe0000000 0x3f76dfbffe000000

def z827 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x7f6dffefe0000000 0x37f6dffefe000000

def z828 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7774386d8360b9c8 0xb7774386d8360b9c

def z829 : W := mkw 0x2880182501280840 0x0288018250128084 0x5fe63c6c03ff98c7 0xc5fe63c6c03ff98c

def z830 : W := mkw 0x28801825812c2940 0x428801825812c294 0xf774387d836cffce 0xff774387d836cffc

def z831 : W := mkw 0xf00fb77f52800008 0x1f00fb77f5280000 0xffeffffffc800001 0x3ffeffffffc80000

def z832 : W := mkw 0x2880182501280840 0x0288018250128084 0x5764386c036098c0 0x85764386c036098c

def z833 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe09a03f01f80fe0b 0xde09a03f01f80fe0

def z834 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x8ee9c38e1c7041f5 0xe8ee9c38e1c7041f

def z835 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x444dfbfde0000000 0x1444dfbfde000000

def z836 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x7ff63c7de3ffbfcf 0xf7ff63c7de3ffbfc

def z837 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1e8bfc001fff0007 0xc1e8bfc001fff000

def z838 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1f4ffc001fff0006 0x81f4ffc001fff000

def z839 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe01f0004 0x3ffefffffe01f000

def z840 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe9fe07f27f80fe0b 0xde9fe07f27f80fe0

def z841 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x5feffc601fff9807 0xc5feffc601fff980

def z842 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1feffc001fff413f 0xc1feffc001fff413

def z843 : W := mkw 0x2880182501280840 0x0288018250128084 0xeee4386e0370d9fd 0xeeee4386e0370d9f

def z844 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x415e03f01f80fe0b 0xd415e03f01f80fe0

def z845 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1f8ffc001fff0007 0x01f8ffc001fff000

def z846 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xfffbc79ffcf0e7ff 0xffffbc79ffcf0e7f

def z847 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe3fe03f01f80ff0f 0xfe3fe03f01f80ff0

def z848 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xfe8bffffe0000000 0x3fe8bffffe000000

def z849 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xffedfb8e1c70c1fd 0xeffedfb8e1c70c1f

def z850 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1eebfc001cff0005 0xc1eebfc001cff000

def z851 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x154ffc001fff0007 0xc154ffc001fff000

def z852 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe1fe03f01fe0ffcf 0xde1fe03f01fe0ffc

def z853 : W := mkw 0x9c0f6e501bfa1407 0x19c0f6e501bfa140 0x1feffc101fff0607 0xc1feffc101fff060

def z854 : W := mkw 0x2880182501280840 0x0288018250128084 0x5644386c036c98c4 0x85644386c036c98c

def z855 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1feffc001cff0005 0x01feffc001cff000

def z856 : W := mkw 0x2880182501280840 0x0288018250128084 0x7774386c036cb8ce 0xd7774386c036cb8c

def z857 : W := mkw 0x00400000a0052310 0x600400000a005231 0x99920413e09f673f 0x599920413e09f673

def z858 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xefebc39e1c70c1fd 0xfefebc39e1c70c1f

def z859 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xee89c38e1c70c1fd 0x2ee89c38e1c70c1f

def z860 : W := mkw 0x00400000a0052310 0x600400000a005231 0xfbb2041fe09fe7ff 0x7fbb2041fe09fe7f

def z861 : W := mkw 0x28801825812c2940 0x428801825812c294 0x4444386d836099c0 0xa4444386d836099c

def z862 : W := mkw 0x28801825812c2940 0x428801825812c294 0x6574386d8360b9ca 0xf6574386d8360b9c

def z863 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1baffc001f9f0007 0x41baffc001f9f000

def z864 : W := mkw 0xe04fb77fe0052318 0x7e04fb77fe005231 0x445dfbec009f673f 0x4445dfbec009f673

def z865 : W := mkw 0x28801825812c2940 0x428801825812c294 0xfff63c7d83ffffcf 0xffff63c7d83ffffc

def z866 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x1e09ff8fe0000000 0x21e09ff8fe000000

def z867 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xebfe03f21f80fe0b 0xfebfe03f21f80fe0

def z868 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1eedfc001f7f0005 0xc1eedfc001f7f000

def z869 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe0de03f01f80fe09 0x9e0de03f01f80fe0

def z870 : W := mkw 0x0800480009780004 0x0080048000978000 0x1feffc001fff0007 0xc1feffc001fff000

def z871 : W := mkw 0x920f26d01680d401 0x1920f26d01680d40 0xfffffff3ff80fe0b 0xffffffff3ff80fe0

def z872 : W := mkw 0xf00fb77f52801409 0x1f00fb77f5280140 0xffffffffe3807e0b 0x7ffffffffe3807e0

def z873 : W := mkw 0x00400000a0052310 0x600400000a005231 0xa8920413e09f673f 0x7a8920413e09f673

def z874 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x044df8001f7f0004 0x8044df8001f7f000

def z875 : W := mkw 0x28801825812c2940 0x428801825812c294 0x77763c7de36cb9ce 0xf77763c7de36cb9c

def z876 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe0fc03e01f80fe0b 0xce0fc03e01f80fe0

def z877 : W := mkw 0x00400000a0052310 0x600400000a005231 0xfbf60473e09f673f 0x7fbf60473e09f673

def z878 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xccc9c38e1c70c1fd 0xcccc9c38e1c70c1f

def z879 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbaa20413e09f473d 0x6baa20413e09f473

def z880 : W := mkw 0x1c0f6c001bfa1407 0x11c0f6c001bfa140 0x1ffffc001fff3e07 0xc1ffffc001fff3e0

def z881 : W := mkw 0x2880182501280840 0x0288018250128084 0x5544386d836098c0 0x95544386d836098c

def z882 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7f743c6fe36cb9ce 0xf7f743c6fe36cb9c

def z883 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe3000002 0xfffefffffe300000

def z884 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x7f763c7fe3ffbffe 0xf7f763c7fe3ffbff

def z885 : W := mkw 0x28801825812c2940 0x428801825812c294 0x6454386d836cb9ce 0xf6454386d836cb9c

def z886 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1e09fc001c7f0004 0x01e09fc001c7f000

def z887 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffffffffe0802602 0x3ffffffffe080260

def z888 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeeebc39e1cf0c7fd 0xeeeebc39e1cf0c7f

def z889 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffeffffffc000001 0xfffeffffffc00000

def z890 : W := mkw 0x0c0f6c00097a0006 0x10c0f6c00097a000 0x1feffc001c7f0005 0xc1feffc001c7f000

def z891 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x81fe03f01f807e03 0xd81fe03f01f807e0

def z892 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x405c03f01f00be00 0x9405c03f01f00be0

def z893 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7776387d83ecbfce 0xf7776387d83ecbfc

def z894 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe00c0006 0x7ffefffffe00c000

def z895 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x011e03f01f803e02 0x1011e03f01f803e0

def z896 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xe4e9c38c1c70c1fd 0xce4e9c38c1c70c1f

def z897 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbff20413e0ff673f 0xfbff20413e0ff673

def z898 : W := mkw 0x28801825812c2940 0x428801825812c294 0x5444386d836c98c0 0x85444386d836c98c

def z899 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xfbfe07f01f80fe0b 0xdfbfe07f01f80fe0

def z900 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7574386d836cb8ca 0xd7574386d836cb8c

def z901 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x05eff8001fff0007 0xc05eff8001fff000

def z902 : W := mkw 0x6001b52f40000008 0x06001b52f4000000 0xfe01ff8fe0000000 0x2fe01ff8fe000000

def z903 : W := mkw 0x00400000a0052310 0x600400000a005231 0x9a920413e09f673f 0x69a920413e09f673

def z904 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1ffffc001fffb80f 0xc1ffffc001fffb80

def z905 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe1fe03f3ff80fe0b 0xfe1fe03f3ff80fe0

def z906 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe9fe03f21f90fe3b 0xde9fe03f21f90fe3

def z907 : W := mkw 0x6001b52f40000008 0x06001b52f4000000 0xffedffefe0000000 0x3ffedffefe000000

def z908 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7714386d836cb9ce 0x37714386d836cb9c

def z909 : W := mkw 0x28801825812c2940 0x428801825812c294 0xf7f6387d836cb9ce 0xff7f6387d836cb9c

def z910 : W := mkw 0xf00fb77f52800008 0x1f00fb77f5280000 0xffffffffff80b80b 0xfffffffffff80b80

def z911 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbba20413e09f4735 0x3bba20413e09f473

def z912 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xf54fffffe0000000 0x3f54fffffe000000

def z913 : W := mkw 0x28801825812c2940 0x428801825812c294 0xfff4386f836cb9ce 0xffff4386f836cb9c

def z914 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x176ffc001fef0006 0xc176ffc001fef000

def z915 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xbfabff9fe0000000 0x3bfabff9fe000000

def z916 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0xbfeffc021fff0007 0xebfeffc021fff000

def z917 : W := mkw 0x28801825812c2940 0x428801825812c294 0x5654386d836cb9ce 0xe5654386d836cb9c

def z918 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffffffffe000b808 0x3ffffffffe000b80

def z919 : W := mkw 0x2880182501280840 0x0288018250128084 0x6444386c036099c8 0xa6444386c036099c

def z920 : W := mkw 0x00400000a0052310 0x600400000a005231 0xfff2041fe09f673f 0x7fff2041fe09f673

def z921 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xf7fe3bf01f80fe0b 0xdf7fe3bf01f80fe0

def z922 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x7ff63c6d83ffffff 0xf7ff63c6d83fffff

def z923 : W := mkw 0x28801825812c2940 0x428801825812c294 0x4454386d8360b8c0 0x94454386d8360b8c

def z924 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe09f413f 0x7ffefffffe09f413

def z925 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeee9c38e1c7041f5 0x2eee9c38e1c7041f

def z926 : W := mkw 0x1f404880bfffe3b6 0xe1f404880bfffe3b 0x001000001fffe7ff 0xc001000001fffe7f

def z927 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xf1fe07f1ff80fe0b 0xdf1fe07f1ff80fe0

def z928 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x4e49c38e1c70c1fd 0xe4e49c38e1c70c1f

def z929 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1feffc001fff81cf 0xc1feffc001fff81c

def z930 : W := mkw 0xe001b77f40000008 0x0e001b77f4000000 0x5e01ffefe0000000 0x25e01ffefe000000

def z931 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe06080c0 0xbffefffffe06080c

def z932 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xf7f6387fe3ecffff 0xff7f6387fe3ecfff

def z933 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7ff4386d837cb9cf 0xf7ff4386d837cb9c

def z934 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x3feffc001fff010f 0xe3feffc001fff010

def z935 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeef9c39e1c70e7fd 0xfeef9c39e1c70e7f

def z936 : W := mkw 0x6001b52f40000008 0x06001b52f4000000 0xffebff9fe0000000 0x3ffebff9fe000000

def z937 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xf7763c7fe3effffe 0xff7763c7fe3effff

def z938 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x6669c38c1c70c1fd 0xe6669c38c1c70c1f

def z939 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbff63c13e09f673f 0x7bff63c13e09f673

def z940 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xcec9c38e1c70c1f5 0xacec9c38e1c70c1f

def z941 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x405c03e01f00fe08 0x8405c03e01f00fe0

def z942 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xfff63c7fe36cfffe 0xffff63c7fe36cfff

def z943 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbbb20413e09f6633 0x3bbb20413e09f663

def z944 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xfbfe07f3ff90ff3f 0xffbfe07f3ff90ff3

def z945 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x4ee9c38e1c7081f5 0xe4ee9c38e1c7081f

def z946 : W := mkw 0x924e02d0b685f711 0x7924e02d0b685f71 0x5a4c07e3ff1f9934 0xa5a4c07e3ff1f993

def z947 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7114386d836cb9ce 0xf7114386d836cb9c

def z948 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe0600004 0xfffefffffe060000

def z949 : W := mkw 0xa00f367540000008 0x1a00f36754000000 0xffeffff1e0000000 0x1ffeffff1e000000

def z950 : W := mkw 0x2000102500000000 0x0200010250000000 0x7774386d8360b9ce 0xf7774386d8360b9c

def z951 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeee9c38e1cffc1ff 0xeeee9c38e1cffc1f

def z952 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbffbc413e09f673f 0x7bffbc413e09f673

def z953 : W := mkw 0x2880182501280840 0x0288018250128084 0x7764386d836c98c6 0xf7764386d836c98c

def z954 : W := mkw 0xf00fb77f52800008 0x1f00fb77f5280000 0xffefffffff9f0007 0xfffefffffff9f000

def z955 : W := mkw 0x2880182501280840 0x0288018250128084 0x4664386c036098c4 0xc4664386c036098c

def z956 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x9f8fffffe0000000 0x39f8fffffe000000

def z957 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xeffe03fe1ff0ffff 0xfeffe03fe1ff0fff

def z958 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xf5effffde0000000 0x1f5effffde000000

def z959 : W := mkw 0x9c0f6e501bfa0006 0x19c0f6e501bfa000 0x1feffc701fff0007 0xd1feffc701fff000

def z960 : W := mkw 0x00400000a0052310 0x600400000a005231 0xb1120413e09f673f 0x7b1120413e09f673

def z961 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0xbffffc13ffff660f 0xfbffffc13ffff660

def z962 : W := mkw 0x6000912f00000000 0x06000912f0000000 0xffefffffe0000000 0x3ffefffffe000000

def z963 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x176df8001fff0007 0xc176df8001fff000

def z964 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0xffefff801fff0007 0xcffefff801fff000

def z965 : W := mkw 0x400fa50a00000000 0x1400fa50a0000000 0xffefff9fe0000000 0x3ffefff9fe000000

def z966 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeef9c3ee1c70f9fd 0xfeef9c3ee1c70f9f

def z967 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x405c03e01f80be02 0x8405c03e01f80be0

def z968 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xe5effbffe0000000 0x3e5effbffe000000

def z969 : W := mkw 0x28801825812c2940 0x428801825812c294 0x6574386c036cb9ce 0xd6574386c036cb9c

def z970 : W := mkw 0x2880182501280840 0x0288018250128084 0x6454386c0360b8c8 0x96454386c0360b8c

def z971 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x7feffc601fff0007 0xd7feffc601fff000

def z972 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xddcfffffe0000000 0x1ddcfffffe000000

def z973 : W := mkw 0xf40fb77f5282000a 0x1f40fb77f5282000 0xffefffffe0830000 0x3ffefffffe083000

def z974 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0xbffffc121fff673f 0xfbffffc121fff673

def z975 : W := mkw 0x2880182501280840 0x0288018250128084 0x4444386c036099cc 0xc4444386c036099c

def z976 : W := mkw 0xf00fb77f52801409 0x1f00fb77f5280140 0xffefffffe0800600 0x3ffefffffe080060

def z977 : W := mkw 0x920f26d05680d409 0x1920f26d05680d40 0xe1fe07f07f80fe0b 0xde1fe07f07f80fe0

def z978 : W := mkw 0x1c016c001bfa0006 0x01c016c001bfa000 0x1f65fc001fff0007 0xc1f65fc001fff000

def z979 : W := mkw 0xd30fe7da5ed0d4ad 0x9d30fe7da5ed0d4a 0x888bc7927c904631 0x0888bc7927c90463

def z980 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xfee9c78e1c7fc1fd 0xefee9c78e1c7fc1f

def z981 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe1fe03f01f80be02 0x9e1fe03f01f80be0

def z982 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7654386d836cb9cc 0xb7654386d836cb9c

def z983 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x110ffc001f8f0002 0x0110ffc001f8f000

def z984 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xe669c38e1c60c1fc 0xee669c38e1c60c1f

def z985 : W := mkw 0x00400000a0052310 0x600400000a005231 0xba920413e09f673d 0x3ba920413e09f673

def z986 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7f74386f837cb9fe 0xf7f74386f837cb9f

def z987 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffffffffe09f660f 0x7ffffffffe09f660

def z988 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xfff43c6fe37ff9ff 0xffff43c6fe37ff9f

def z989 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe0004009 0x7ffefffffe000400

def z990 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe19e03f01f80fe0b 0x1e19e03f01f80fe0

def z991 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xfeedffefe0000000 0x2feedffefe000000

def z992 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe7fe03f01fe0fe0f 0xde7fe03f01fe0fe0

def z993 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x4449c38e1c6081f0 0xa4449c38e1c6081f

def z994 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x41fe03f01f80be03 0xd41fe03f01f80be0

def z995 : W := mkw 0x9c0f6e501bfa0006 0x19c0f6e501bfa000 0xfffffff01fff660f 0xdfffffff01fff660

def z996 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xf7f6387d83ffffff 0xff7f6387d83fffff

def z997 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0xbfeffc101fff0007 0xdbfeffc101fff000

def z998 : W := mkw 0xd70fe7da1ed2d4a7 0x9d70fe7da1ed2d4a 0x888bc7921c934631 0x0888bc7921c93463

def z999 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xffe9c38e1c7cc1ff 0xeffe9c38e1c7cc1f

def z1000 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1f6dfc001f7f0006 0xc1f6dfc001f7f000

def z1001 : W := mkw 0x00400000a0052310 0x600400000a005231 0xb9b20413e09f663b 0x5b9b20413e09f663

def z1002 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x7774386fe36cb9fe 0xf7774386fe36cb9f

def z1003 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe1fe03fc1f80ffcb 0xfe1fe03fc1f80ffc

def z1004 : W := mkw 0x9c0f6e501bfa0006 0x19c0f6e501bfa000 0xfffffff01fffb80f 0xdfffffff01fffb80

def z1005 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeff9c38e1c70e1ff 0xfeff9c38e1c70e1f

def z1006 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x9feffc101fff4607 0xc9feffc101fff460

def z1007 : W := mkw 0x9c0f6e501bfa0006 0x19c0f6e501bfa000 0xffeffff3ffff0007 0xfffeffff3ffff000

def z1008 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x044df8001fef0002 0x8044df8001fef000

def z1009 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1feffc0c1fff01c7 0xe1feffc0c1fff01c

def z1010 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xfeebff9fe0000000 0x2feebff9fe000000

def z1011 : W := mkw 0x00400000a0052310 0x600400000a005231 0xfbb20473e09fff3f 0x7fbb20473e09fff3

def z1012 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xf7f63c7de3efffcf 0xff7f63c7de3efffc

def z1013 : W := mkw 0x2880182501280840 0x0288018250128084 0x4554386c0360b8c2 0x94554386c0360b8c

def z1014 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x55563c7de3efbec2 0x955563c7de3efbec

def z1015 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1feffc021fff0137 0xe1feffc021fff013

def z1016 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x988bff93e0000000 0x0988bff93e000000

def z1017 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xee49c38e1c70c1fc 0xaee49c38e1c70c1f

def z1018 : W := mkw 0x1c016c001bfa0006 0x01c016c001bfa000 0x1e01fc001f7f0004 0x81e01fc001f7f000

def z1019 : W := mkw 0x920002d01680d401 0x0920002d01680d40 0xe17403f01f80fe0b 0xde17403f01f80fe0

def z1020 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x3ffffc001fff200f 0xd3ffffc001fff200

def z1021 : W := mkw 0x28801825812c2940 0x428801825812c294 0x5754386d836cb9c6 0xb5754386d836cb9c

def z1022 : W := mkw 0x2880182501280840 0x0288018250128084 0x6664386c036098c0 0xa6664386c036098c

def z1023 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x6e69c38e1c7081fc 0xe6e69c38e1c7081f

def z1024 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xfee9c78ffc70c1fd 0xefee9c78ffc70c1f

def z1025 : W := mkw 0x9c0f6e505bfa000e 0x19c0f6e505bfa000 0x1feffc107fff0007 0xc1feffc107fff000

def z1026 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xebfe03f01f90fe0f 0xdebfe03f01f90fe0

def z1027 : W := mkw 0x28801825812c2940 0x428801825812c294 0x4454386c036cb8c2 0x84454386c036cb8c

def z1028 : W := mkw 0x140f64001ad20006 0x1140f64001ad2000 0x1feffc001c9f0007 0x41feffc001c9f000

def z1029 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x19effc001f9f0003 0xc19effc001f9f000

def z1030 : W := mkw 0x2880182501280840 0x0288018250128084 0x4454386c0360b8ca 0xc4454386c0360b8c

def z1031 : W := mkw 0x9c0f6e501bfa0006 0x19c0f6e501bfa000 0x5fefffe01fff0007 0xc5fefffe01fff000

def z1032 : W := mkw 0x28801825812c2940 0x428801825812c294 0xf774386f836cf9fe 0xff774386f836cf9f

def z1033 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe0004138 0x3ffefffffe000413

def z1034 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x4ee9c38c1c70c1fd 0xc4ee9c38c1c70c1f

def z1035 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x7feffc001fff800f 0xc7feffc001fff800

def z1036 : W := mkw 0x1d0f6c001bfa00a6 0x91d0f6c001bfa00a 0x1feffc001fff01f7 0xc1feffc001fff01f

def z1037 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xc0de03f01f80fe0b 0xcc0de03f01f80fe0

def z1038 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe08f0002 0x3ffefffffe08f000

def z1039 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1ffffc001fff660f 0xc1ffffc001fff660

def z1040 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeee9c38e1c7081f4 0xaeee9c38e1c7081f

def z1041 : W := mkw 0x1c016c001bfa0006 0x01c016c001bfa000 0x1fa3fc001fff0007 0xc1fa3fc001fff000

def z1042 : W := mkw 0x00c00000a0052b50 0x600c00000a0052b5 0xbbb20413e09fffff 0x7bbb20413e09ffff

def z1043 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x41fe03e01f80fe0b 0xc41fe03e01f80fe0

def z1044 : W := mkw 0xf00fb77f52801409 0x1f00fb77f5280140 0xffffffffe380be0a 0xfffffffffe380be0

def z1045 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe0100005 0x7ffefffffe010000

def z1046 : W := mkw 0xe001b77f40000008 0x0e001b77f4000000 0xff65ffffe0000000 0x3ff65ffffe000000

def z1047 : W := mkw 0x920002d01680d401 0x0920002d01680d40 0xe0f803f01f80fe0b 0xde0f803f01f80fe0

def z1048 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7774386d83ffb9cf 0xf7774386d83ffb9c

def z1049 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1ecffc001fff0005 0x81ecffc001fff000

def z1050 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xdecfffffe0000000 0x2decfffffe000000

def z1051 : W := mkw 0x6001b52f40000008 0x06001b52f4000000 0x5e49ff8fe0000000 0x25e49ff8fe000000

def z1052 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffffffffe000200a 0x7ffffffffe000200

def z1053 : W := mkw 0x63c091afa405ebf0 0xe63c091afa405ebf 0xe01003ffe000fff8 0x3e01003ffe000fff

def z1054 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeeebc78e1cf3c1fd 0xeeeebc78e1cf3c1f

def z1055 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x3feffc019fff0007 0xf3feffc019fff000

def z1056 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0xffeffc0e1fffc1ff 0xeffeffc0e1fffc1f

def z1057 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x9feffc127fff0007 0xc9feffc127fff000

def z1058 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbbb20413e39fff3f 0xfbbb20413e39fff3

def z1059 : W := mkw 0x1c016c001bfa0006 0x01c016c001bfa000 0x1e01fc001cff0005 0x01e01fc001cff000

def z1060 : W := mkw 0x28801825812c2940 0x428801825812c294 0xf7fc3bed836cb9ce 0xff7fc3bed836cb9c

def z1061 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7f743c6d837fb9ce 0xf7f743c6d837fb9c

def z1062 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x144dfc001f6f0000 0x8144dfc001f6f000

def z1063 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xfbfe07f3ff9ffe0f 0xffbfe07f3ff9ffe0

def z1064 : W := mkw 0x4100c10a085000a4 0x84100c10a085000a 0xeee9c38e1c7001f5 0xeeee9c38e1c7001f

def z1065 : W := mkw 0x2880182501280840 0x0288018250128084 0x6444386d836098c0 0xb6444386d836098c

def z1066 : W := mkw 0xf00fb77f52800008 0x1f00fb77f5280000 0xffefffffff000000 0xbffefffffff00000

def z1067 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xc1de03f01f80fe03 0x9c1de03f01f80fe0

def z1068 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xf3fe03f19f80fe0b 0xff3fe03f19f80fe0

def z1069 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1feffc001fef0002 0x81feffc001fef000

def z1070 : W := mkw 0x00400000a0052310 0x600400000a005231 0x98820413e09f4631 0x098820413e09f463

def z1071 : W := mkw 0x28801825812c2940 0x428801825812c294 0x6674386d8360b9cc 0xf6674386d8360b9c

def z1072 : W := mkw 0x28801825812c2940 0x428801825812c294 0xf774387fe36cb9ce 0xff774387fe36cb9c

def z1073 : W := mkw 0x920002d01680d401 0x0920002d01680d40 0xe01003f01f00fe08 0x9e01003f01f00fe0

def z1074 : W := mkw 0x9c0f6e501bfa1407 0x19c0f6e501bfa140 0xbffffc701fff7e0f 0xdbffffc701fff7e0

def z1075 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xefebc38e1cf0c1ff 0xeefebc38e1cf0c1f

def z1076 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbfb2041fe0ff67ff 0x7bfb2041fe0ff67f

def z1077 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbbfa0413fc9f673f 0xfbbfa0413fc9f673

def z1078 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x819e03f01f80fe0b 0xd819e03f01f80fe0

def z1079 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeef9c38e1f70f9ff 0xeeef9c38e1f70f9f

def z1080 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x77763c7de3ffffff 0xf77763c7de3fffff

def z1081 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x77743c6de36fb9ce 0xf77743c6de36fb9c

def z1082 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0xbfeffc001fff400f 0xcbfeffc001fff400

def z1083 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe06001c4 0x3ffefffffe06001c

def z1084 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x7f743c6fe3ffffff 0xf7f743c6fe3fffff

def z1085 : W := mkw 0x28801825812c2940 0x428801825812c294 0x4444386c036c99c4 0x84444386c036c99c

def z1086 : W := mkw 0x1c0048001bfa0006 0x01c0048001bfa000 0x1fedf8001fff0007 0xc1fedf8001fff000

def z1087 : W := mkw 0x0c016c00097a0006 0x00c016c00097a000 0x1e01fc001c7f0005 0xc1e01fc001c7f000

def z1088 : W := mkw 0xe08fb77f40000848 0x1e08fb77f4000084 0xffefffffe00098c0 0x3ffefffffe00098c

def z1089 : W := mkw 0x28801825812c2940 0x428801825812c294 0x1714386d836cb9ce 0xf1714386d836cb9c

def z1090 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffffffffe0006608 0x3ffffffffe000660

def z1091 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x617e03f01f80be0a 0xd617e03f01f80be0

def z1092 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe0100134 0x3ffefffffe010013

def z1093 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7774386d83ecffcf 0xf7774386d83ecffc

def z1094 : W := mkw 0x2880182501280840 0x0288018250128084 0x7774386d8360b8ca 0xf7774386d8360b8c

def z1095 : W := mkw 0x00400000a0052310 0x600400000a005231 0x1b120413e09f673f 0x71b120413e09f673

def z1096 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe9fe07f01f93fe0b 0xde9fe07f01f93fe0

def z1097 : W := mkw 0x1c016c001bfa0006 0x01c016c001bfa000 0x0401f8001fff0007 0xc0401f8001fff000

def z1098 : W := mkw 0x4300c18a0c50d4a5 0x84300c18a0c50d4a 0xeef9c38e1c70fffd 0xeeef9c38e1c70fff

def z1099 : W := mkw 0x9c0f6e501bfa1407 0x19c0f6e501bfa140 0xfffffff01fff3e07 0xdfffffff01fff3e0

def z1100 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe17c03f01f00fe0a 0xde17c03f01f00fe0

def z1101 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x7774386d83efbfce 0xf7774386d83efbfc

def z1102 : W := mkw 0x930e02d01680d4a1 0x9930e02d01680d4a 0xe1fe03f01f80fffb 0xde1fe03f01f80fff

def z1103 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xffebc79ffcffc1ff 0xfffebc79ffcffc1f

def z1104 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xffebc78e1c70c1fd 0xeffebc78e1c70c1f

def z1105 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeee9c38e1c60c1f8 0xaeee9c38e1c60c1f

def z1106 : W := mkw 0x28801825812c2940 0x428801825812c294 0xfff63c7fe3ffb9cf 0xffff63c7fe3ffb9c

def z1107 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7554386d836cb9ca 0xb7554386d836cb9c

def z1108 : W := mkw 0x28801825812c2940 0x428801825812c294 0xf7f4386d836cf9cf 0xff7f4386d836cf9c

def z1109 : W := mkw 0x2880182501280840 0x0288018250128084 0x5544386c036c98c2 0x85544386c036c98c

def z1110 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x5fefffefe0000000 0x25fefffefe000000

def z1111 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xefedc3ee1c70c1fd 0xfefedc3ee1c70c1f

def z1112 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x544dffede0000000 0x0544dffede000000

def z1113 : W := mkw 0x960f26d01682d403 0x1960f26d01682d40 0xe1fe07f01f83fe0b 0xde1fe07f01f83fe0

def z1114 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x188bfc001c9f0001 0x0188bfc001c9f000

def z1115 : W := mkw 0x120000801680d401 0x0120000801680d40 0xe1fc03e01f80fe0b 0xde1fc03e01f80fe0

def z1116 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffffffffe3003802 0x3ffffffffe300380

def z1117 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe0800003 0x7ffefffffe080000

def z1118 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xfe4dffffe0000000 0x3fe4dffffe000000

def z1119 : W := mkw 0xe24093ffe405f719 0x6e24093ffe405f71 0xe01003ffe000ff38 0x3e01003ffe000ff3

def z1120 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xe889c38e1c70c1fd 0xee889c38e1c70c1f

def z1121 : W := mkw 0xe001b77f40000008 0x0e001b77f4000000 0xfee9ffffe0000000 0x3fee9ffffe000000

def z1122 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xfff4386f83ffffff 0xffff4386f83fffff

def z1123 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x9fefff9fe0000000 0x29fefff9fe000000

def z1124 : W := mkw 0x28801825812c2940 0x428801825812c294 0x5774386c036cb9ce 0xc5774386c036cb9c

def z1125 : W := mkw 0x9c0f6e501bfa1407 0x19c0f6e501bfa140 0x1feffc601fff1807 0xc1feffc601fff180

def z1126 : W := mkw 0x28801825812c2940 0x428801825812c294 0x77fc386d9f6cb9cf 0xf77fc386d9f6cb9c

def z1127 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0x444dfbefe0000000 0x2444dfbefe000000

def z1128 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1feffc03ffff0007 0xe1feffc03ffff000

def z1129 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0x4449c38c1c7081f4 0x84449c38c1c7081f

def z1130 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xe449c38e1c70c1fd 0xee449c38e1c70c1f

def z1131 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1dcffc001fff0003 0x81dcffc001fff000

def z1132 : W := mkw 0xe34093ffe405e3b8 0xee34093ffe405e3b 0xe01003ffe000e7f8 0x3e01003ffe000e7f

def z1133 : W := mkw 0xe000937f40000008 0x0e000937f4000000 0xffedfbffe0000000 0x3ffedfbffe000000

def z1134 : W := mkw 0x00400000a0052310 0x600400000a005231 0xb9920413e09f673b 0x3b9920413e09f673

def z1135 : W := mkw 0x920f26d01680d401 0x1920f26d01680d40 0xe9ffc7f01f80fe0b 0xde9ffc7f01f80fe0

def z1136 : W := mkw 0x00400000a0052310 0x600400000a005231 0x9bb20413e09f6637 0x59bb20413e09f663

def z1137 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbb120413e09f673e 0x3bb120413e09f673

def z1138 : W := mkw 0xe00fb77f40001409 0x1e00fb77f4000140 0xffffffffe0003e00 0x3ffffffffe0003e0

def z1139 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe7fe03fc1f80fe0b 0xfe7fe03fc1f80fe0

def z1140 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xf3fe03f01f8cfe0f 0xdf3fe03f01f8cfe0

def z1141 : W := mkw 0x00400000a0052310 0x600400000a005231 0xfbf20413e09fe73f 0xffbf20413e09fe73

def z1142 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe05c03f01f80fe0b 0xde05c03f01f80fe0

def z1143 : W := mkw 0x9c0f6e501bfa0006 0x19c0f6e501bfa000 0x9fefff901fff0007 0xc9fefff901fff000

def z1144 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xe454387fe360fff8 0xbe454387fe360fff

def z1145 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe0008008 0xfffefffffe000800

def z1146 : W := mkw 0x2880182501280840 0x0288018250128084 0x6564386c036098c0 0x96564386c036098c

def z1147 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0x617c03e01f80fe0b 0xd617c03e01f80fe0

def z1148 : W := mkw 0x920f26d01680d401 0x1920f26d01680d40 0xe5fffbf01f80fe0b 0xde5fffbf01f80fe0

def z1149 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeeebc79e7c70c1fd 0xeeeebc79e7c70c1f

def z1150 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeef9c38e1cf0e7ff 0xeeef9c38e1cf0e7f

def z1151 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7764386d836c99c4 0xb7764386d836c99c

def z1152 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffffffffe360b9ce 0xfffffffffe360b9c

def z1153 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe0804601 0x3ffefffffe080460

def z1154 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x7ff63c6fe3ffb9ff 0xf7ff63c6fe3ffb9f

def z1155 : W := mkw 0x2880182501280840 0x0288018250128084 0x7764386d836099cc 0xf7764386d836099c

def z1156 : W := mkw 0x2880182501280840 0x0288018250128084 0xffe63c7fe36098c0 0xbffe63c7fe36098c

def z1157 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x0eedf8001fff0007 0xc0eedf8001fff000

def z1158 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xf774387fe3ffffff 0xff774387fe3fffff

def z1159 : W := mkw 0x28801825812c2940 0x428801825812c294 0x77f6386d83ecb9cf 0xf77f6386d83ecb9c

def z1160 : W := mkw 0x28801825812c2940 0x428801825812c294 0x5554386d836cb9ce 0xd5554386d836cb9c

def z1161 : W := mkw 0x2880182501280840 0x0288018250128084 0x6464386c036098c8 0xc6464386c036098c

def z1162 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x9feffc021fff4037 0xc9feffc021fff403

def z1163 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xfff4387fe37cffff 0xffff4387fe37cfff

def z1164 : W := mkw 0x28801825812c2940 0x428801825812c294 0x77763c6d83efb9ce 0xf77763c6d83efb9c

def z1165 : W := mkw 0x920002d01680d401 0x0920002d01680d40 0x401003e01f80fe0b 0xc401003e01f80fe0

def z1166 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x0ccffc001fff0007 0xc0ccffc001fff000

def z1167 : W := mkw 0x2880182501280840 0x0288018250128084 0x6774386c0360b9ce 0xf6774386c0360b9c

def z1168 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0xff743c7fe37ffffe 0xfff743c7fe37ffff

def z1169 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7664386d836c99cc 0xe7664386d836c99c

def z1170 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7ff63c6d836cb9ce 0xf7ff63c6d836cb9c

def z1171 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1ffffc601fff3807 0xd1ffffc601fff380

def z1172 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xeeedfbffe0000000 0x3eeedfbffe000000

def z1173 : W := mkw 0x920002d01680d401 0x0920002d01680d40 0xe1b203f01f80fe0b 0xde1b203f01f80fe0

def z1174 : W := mkw 0x4300c18a0c50c0a4 0x84300c18a0c50c0a 0xeeedc3ee1f70d9fd 0xeeeedc3ee1f70d9f

def z1175 : W := mkw 0x1c8f6c001bfa0846 0x11c8f6c001bfa084 0x1feffc001fff98c7 0xc1feffc001fff98c

def z1176 : W := mkw 0x9c0f6e501bfa1407 0x19c0f6e501bfa140 0x7ffffc701fffbe0f 0xd7ffffc701fffbe0

def z1177 : W := mkw 0x28801825812c2940 0x428801825812c294 0x7774386d837cf9ff 0xf7774386d837cf9f

def z1178 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe000010c 0x7ffefffffe000010

def z1179 : W := mkw 0x28801825812c2940 0x428801825812c294 0x6674386c036cb9ce 0xe6674386c036cb9c

def z1180 : W := mkw 0x0c016c00097a0006 0x00c016c00097a000 0x1e49fc001c7f0004 0x81e49fc001c7f000

def z1181 : W := mkw 0x28c01825a12d2b50 0x628c01825a12d2b5 0x7774386d837fb9fe 0xf7774386d837fb9f

def z1182 : W := mkw 0x1c0f6c001bfa0006 0x11c0f6c001bfa000 0x1feffc001f9f0003 0x01feffc001f9f000

def z1183 : W := mkw 0x920e02d01680d401 0x1920e02d01680d40 0xe1fe03f21f80ff3b 0xfe1fe03f21f80ff3

def z1184 : W := mkw 0x28801825812c2940 0x428801825812c294 0xfff63c6f83fff9ff 0xffff63c6f83fff9f

def z1185 : W := mkw 0x00400000a0052310 0x600400000a005231 0xbbb20413e0ffe7ff 0xfbbb20413e0ffe7f

def z1186 : W := mkw 0x1c016c001bfa0006 0x01c016c001bfa000 0x1ee9fc001fff0007 0xc1ee9fc001fff000

def z1187 : W := mkw 0xe00fb77f40000008 0x1e00fb77f4000000 0xffefffffe0930001 0x3ffefffffe093000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z8,z2,z3,z4,z5,z6]),(0,[z9,z1,z3,z4,z10,z5,z6])],[(0,[z11,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z12,z4,z5,z6]),(0,[z1,z2,z3,z13,z4,z5,z6]),(1,[z1,z2,z14,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z16,z6]),(0,[z17,z1,z2,z3,z4,z5,z6]),(0,[z1,z18,z2,z3,z4,z5,z6])],[(0,[z8,z1,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z20,z5,z6]),(0,[z21,z1,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z22,z6])],[(0,[z23,z1,z2,z24,z4,z5,z6]),(0,[z25,z1,z2,z3,z4,z5,z6]),(0,[z26,z27,z2,z3,z4,z5,z6]),(0,[z1,z2,z28,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z29]),(0,[z1,z2,z3,z4,z5,z30,z6]),(0,[z1,z2,z3,z4,z5,z6,z31])],[(1,[z1,z2,z32,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z33,z6]),(0,[z1,z2,z34,z4,z35,z5,z6]),(0,[z36,z1,z2,z3,z4,z5,z6]),(0,[z1,z37,z2,z3,z4,z16,z6]),(0,[z1,z2,z3,z4,z38,z5,z6]),(0,[z1,z2,z3,z39,z4,z5,z6]),(1,[z1,z40,z3,z4,z5,z6])],[(0,[z1,z41,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z42,z4,z5,z6]),(0,[z1,z2,z43,z3,z44,z5,z6])],[(1,[z1,z2,z3,z4,z5,z45]),(0,[z1,z46,z2,z3,z4,z16,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z47]),(0,[z1,z48,z2,z3,z4,z5,z6]),(0,[z49,z1,z2,z3,z4,z5,z6]),(0,[z50,z1,z3,z4,z5,z6,z51]),(0,[z1,z52,z2,z3,z4,z5,z6])],[(0,[z53,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z54]),(0,[z27,z1,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z56,z5,z6]),(0,[z1,z2,z3,z4,z57,z5,z6]),(0,[z1,z2,z3,z4,z58,z5,z6]),(0,[z1,z59,z2,z3,z4,z5,z6]),(0,[z1,z2,z60,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z61,z5,z6]),(0,[z1,z2,z3,z62,z4,z5,z63])],[(0,[z1,z2,z3,z4,z5,z64,z6]),(0,[z1,z2,z3,z4,z65,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z66]),(0,[z1,z2,z3,z4,z5,z67,z6])],[(1,[z1,z2,z3,z4,z5,z68]),(0,[z1,z2,z34,z4,z69,z5,z6]),(0,[z1,z70,z2,z3,z4,z5,z6]),(0,[z1,z71,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z72])],[(0,[z1,z2,z73,z34,z4,z5,z6]),(1,[z1,z2,z74,z4,z5,z6]),(0,[z1,z3,z4,z75,z5,z16,z6]),(0,[z1,z2,z3,z4,z76,z5,z6]),(0,[z1,z2,z3,z4,z77,z5,z6]),(0,[z78,z1,z2,z3,z4,z5,z6])],[(0,[z1,z79,z2,z15,z4,z5,z6]),(0,[z1,z3,z15,z4,z10,z5,z6]),(0,[z1,z46,z3,z4,z75,z5,z6]),(0,[z1,z2,z3,z4,z5,z80,z6]),(0,[z1,z81,z3,z4,z82,z5,z6])]],
   [[(0,[z1,z83,z2,z55,z4,z5,z6]),(0,[z84,z1,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z86,z4,z5,z6]),(1,[z1,z2,z3,z4,z87,z6]),(0,[z88,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z89,z5,z6]),(0,[z1,z2,z90,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z91,z5,z6]),(0,[z92,z1,z2,z3,z44,z5,z6]),(0,[z1,z93,z2,z3,z4,z5,z94]),(0,[z1,z2,z3,z4,z5,z95,z6]),(0,[z1,z2,z3,z4,z96,z5,z94]),(0,[z1,z97,z2,z3,z4,z5,z6])],[(0,[z98,z1,z2,z3,z99,z5,z6]),(0,[z1,z3,z100,z4,z5,z16,z6])],[(0,[z1,z2,z3,z4,z87,z5,z6]),(0,[z1,z2,z3,z101,z4,z5,z6]),(1,[z1,z2,z102,z4,z5,z6]),(0,[z1,z2,z3,z103,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z104,z6])],[(0,[z105,z1,z2,z3,z4,z5,z6]),(1,[z52,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z106,z5,z6])],[(0,[z1,z2,z3,z4,z107,z5,z6]),(0,[z1,z2,z3,z4,z5,z108,z6]),(0,[z109,z1,z2,z3,z4,z5,z6]),(0,[z110,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z55,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z111,z6]),(0,[z112,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z113,z6]),(0,[z1,z2,z3,z4,z5,z114,z6])],[(0,[z1,z46,z115,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z116]),(0,[z117,z1,z2,z55,z4,z5,z6]),(0,[z118,z2,z3,z119,z4,z5,z6]),(0,[z120,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z16,z6,z51]),(0,[z1,z2,z3,z4,z121,z5,z6]),(0,[z1,z2,z3,z4,z5,z122,z6])]],
   [[(0,[z1,z123,z3,z4,z5,z6,z51]),(0,[z124,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z55,z4,z5,z125,z6]),(0,[z1,z2,z3,z4,z126,z5,z6]),(0,[z1,z127,z2,z15,z4,z5,z6]),(0,[z1,z46,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z128,z5,z6]),(0,[z1,z2,z129,z3,z4,z5,z6])],[(0,[z1,z130,z3,z100,z4,z5,z6]),(0,[z1,z2,z3,z4,z131,z5,z6])],[(0,[z1,z2,z55,z4,z5,z63,z6]),(0,[z1,z132,z2,z3,z4,z5,z6])],[(0,[z1,z2,z55,z3,z4,z5,z6]),(0,[z1,z2,z3,z133,z4,z5,z6]),(0,[z1,z3,z4,z134,z5,z22,z6])],[(0,[z1,z2,z3,z4,z5,z6,z135]),(0,[z7,z2,z55,z3,z4,z5,z6]),(0,[z117,z1,z2,z3,z4,z5,z6]),(0,[z136,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z137,z6]),(0,[z1,z2,z3,z4,z5,z6,z138])],[(0,[z1,z2,z139,z34,z4,z5,z6]),(1,[z1,z140,z3,z4,z5,z6]),(0,[z1,z2,z3,z141,z4,z5,z6]),(0,[z1,z2,z3,z4,z142,z5,z6])],[(0,[z1,z2,z34,z4,z5,z125,z6]),(0,[z1,z46,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z143]),(0,[z1,z2,z144,z3,z4,z5,z6]),(0,[z1,z145,z2,z3,z4,z5,z6]),(0,[z1,z2,z146,z3,z4,z5,z6])],[(0,[z1,z147,z2,z3,z4,z5,z6]),(0,[z1,z2,z34,z4,z5,z6,z148]),(0,[z1,z2,z3,z4,z5,z149,z6]),(0,[z117,z1,z2,z3,z4,z5,z150]),(0,[z1,z2,z3,z151,z4,z5,z6]),(0,[z1,z152,z2,z3,z4,z5,z6])]],
   [[(0,[z153,z1,z2,z3,z4,z5,z54]),(0,[z1,z3,z100,z4,z10,z5,z6]),(0,[z154,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z155,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z156]),(0,[z1,z157,z2,z3,z4,z5,z6]),(0,[z158,z1,z159,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z160,z6]),(0,[z1,z161,z2,z3,z4,z5,z6]),(0,[z98,z1,z2,z34,z4,z5,z6]),(0,[z1,z162,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z163,z6]),(0,[z1,z2,z3,z4,z164,z5,z6]),(0,[z165,z1,z2,z3,z4,z5,z6])],[(0,[z166,z1,z2,z3,z4,z5,z6]),(0,[z1,z167,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z126,z6,z148]),(1,[z26,z2,z3,z4,z5,z168]),(0,[z1,z2,z3,z4,z5,z6,z169]),(0,[z1,z2,z3,z4,z96,z5,z51])],[(0,[z1,z2,z55,z4,z5,z6,z51]),(0,[z1,z2,z55,z4,z56,z5,z6]),(0,[z1,z2,z55,z43,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z3,z170,z4,z5,z6]),(0,[z171,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z172,z5,z6])],[(0,[z1,z2,z3,z4,z5,z173,z6]),(0,[z174,z1,z2,z3,z4,z5,z6]),(0,[z1,z175,z2,z3,z4,z5,z6])],[(0,[z98,z1,z2,z176,z4,z5,z6]),(1,[z1,z177,z3,z4,z5,z6]),(0,[z50,z1,z2,z3,z4,z178,z6]),(0,[z50,z1,z2,z3,z4,z5,z51]),(0,[z158,z1,z2,z3,z179,z5,z6]),(0,[z1,z2,z3,z4,z5,z180,z6])],[(0,[z1,z2,z3,z181,z4,z5,z6]),(0,[z1,z2,z3,z4,z182,z5,z6]),(0,[z1,z2,z3,z4,z183,z5,z6]),(0,[z1,z2,z3,z184,z4,z5,z6])]],
   [[(0,[z1,z2,z185,z3,z4,z5,z6]),(0,[z1,z186,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z187,z5,z6]),(0,[z1,z188,z2,z3,z4,z5,z6])],[(0,[z1,z2,z123,z34,z4,z5,z6]),(0,[z189,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z62,z5,z6,z190])],[(0,[z1,z2,z3,z4,z5,z191,z6]),(0,[z1,z2,z3,z4,z192,z5,z6]),(0,[z1,z2,z3,z193,z4,z5,z6])],[(0,[z194,z1,z2,z3,z4,z5,z6]),(0,[z195,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z125,z6]),(0,[z1,z196,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z197]),(0,[z1,z2,z3,z4,z5,z198,z6])],[(0,[z199,z1,z2,z3,z4,z5,z6]),(0,[z1,z37,z2,z34,z4,z5,z6]),(0,[z8,z2,z3,z34,z4,z5,z6]),(0,[z117,z1,z200,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z6,z148]),(0,[z1,z2,z3,z4,z201,z5,z6]),(0,[z1,z202,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z203,z5,z6]),(0,[z1,z2,z3,z44,z4,z5,z6]),(0,[z1,z83,z2,z3,z4,z5,z63])],[(0,[z1,z2,z204,z3,z4,z5,z6]),(0,[z50,z1,z2,z34,z4,z5,z6]),(0,[z9,z1,z2,z55,z4,z5,z6]),(1,[z117,z2,z3,z205,z5,z6]),(0,[z1,z2,z206,z3,z4,z5,z6]),(0,[z1,z2,z3,z207,z5,z125,z6]),(1,[z1,z93,z2,z4,z5,z94])],[(0,[z26,z1,z140,z3,z4,z5,z6]),(0,[z1,z2,z3,z208,z4,z5,z6]),(0,[z209,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z210,z3,z4,z211,z6])]],
   [[(0,[z115,z2,z123,z3,z4,z5,z6]),(0,[z158,z1,z2,z55,z4,z5,z6]),(0,[z98,z1,z2,z3,z212,z5,z6]),(0,[z1,z2,z3,z213,z4,z5,z6]),(0,[z1,z175,z2,z3,z4,z134,z6])],[(0,[z1,z2,z55,z4,z5,z111,z6]),(0,[z1,z2,z55,z4,z5,z114,z6]),(0,[z1,z2,z3,z4,z5,z150,z6]),(0,[z1,z2,z3,z4,z5,z6,z214]),(0,[z215,z1,z2,z3,z4,z5,z6]),(0,[z1,z216,z2,z3,z4,z5,z6])],[(0,[z1,z41,z2,z3,z4,z5,z6]),(0,[z217,z1,z2,z3,z4,z5,z6])],[(1,[z153,z123,z3,z4,z5,z6]),(0,[z153,z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z43,z34,z4,z5,z6]),(0,[z1,z2,z210,z34,z4,z5,z6]),(0,[z1,z2,z55,z4,z126,z5,z6]),(0,[z1,z2,z3,z4,z218,z5,z6]),(0,[z1,z2,z3,z205,z5,z125,z6]),(0,[z26,z1,z2,z3,z4,z5,z111]),(0,[z1,z2,z3,z4,z5,z63,z94])],[(0,[z1,z219,z2,z3,z4,z5,z6]),(0,[z1,z41,z3,z4,z5,z16,z6]),(0,[z1,z2,z3,z220,z4,z5,z6]),(0,[z1,z2,z3,z221,z4,z5,z6]),(0,[z1,z2,z210,z3,z4,z35,z6])],[(0,[z1,z222,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z223,z4,z5,z6]),(0,[z158,z1,z2,z3,z4,z5,z6]),(0,[z158,z1,z2,z3,z172,z5,z6]),(0,[z1,z2,z3,z224,z4,z5,z6])],[(0,[z1,z2,z3,z4,z225,z5,z6]),(0,[z1,z2,z3,z100,z119,z5,z6]),(0,[z98,z1,z226,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z3,z4,z5,z227,z6]),(0,[z1,z2,z3,z4,z5,z228,z6]),(0,[z1,z2,z3,z4,z5,z229,z6])],[(0,[z1,z2,z230,z3,z4,z5,z6]),(0,[z1,z231,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z232,z4,z5,z6]),(0,[z1,z37,z2,z3,z4,z5,z233]),(0,[z1,z2,z3,z4,z134,z211,z6]),(0,[z1,z2,z3,z234,z4,z5,z6])]],
   [[(0,[z1,z2,z34,z4,z5,z6,z116]),(0,[z7,z1,z2,z55,z4,z5,z6]),(0,[z26,z1,z177,z3,z4,z5,z6]),(1,[z1,z235,z3,z4,z5,z6])],[(0,[z194,z7,z2,z3,z4,z5,z6]),(0,[z1,z79,z2,z3,z4,z5,z6]),(0,[z1,z41,z2,z3,z4,z5,z114]),(1,[z1,z2,z3,z179,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z236])],[(0,[z1,z2,z3,z4,z96,z5,z168]),(0,[z1,z2,z3,z237,z4,z5,z6]),(1,[z1,z46,z3,z4,z75,z6])],[(0,[z1,z79,z3,z4,z5,z16,z6]),(0,[z1,z130,z2,z3,z100,z5,z6]),(0,[z1,z238,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z213,z4,z134,z6]),(0,[z1,z239,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z240,z4,z5,z6]),(0,[z2,z3,z4,z5,z111,z6,z168]),(0,[z1,z2,z3,z4,z5,z168,z190]),(0,[z92,z1,z2,z3,z4,z241,z6]),(0,[z242,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z134,z35,z6]),(0,[z1,z2,z3,z62,z4,z96,z5])],[(0,[z243,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z24,z4,z5,z6]),(0,[z1,z2,z3,z4,z244,z5,z6]),(0,[z27,z1,z2,z208,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z245,z6]),(0,[z246,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z247,z6]),(0,[z1,z2,z3,z248,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z249,z6]),(0,[z1,z2,z3,z4,z5,z250,z6])],[(0,[z92,z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z119,z5,z6,z190]),(0,[z1,z2,z3,z4,z251,z5,z6]),(0,[z26,z2,z3,z4,z5,z6,z168]),(0,[z1,z2,z3,z4,z5,z252,z6]),(0,[z1,z2,z3,z253,z4,z5,z6])],[(0,[z254,z1,z2,z3,z4,z5,z6]),(0,[z1,z115,z3,z4,z5,z6,z51]),(0,[z1,z255,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z45]),(0,[z1,z2,z3,z4,z126,z16,z6]),(0,[z92,z1,z157,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z256,z5,z6]),(0,[z1,z2,z3,z4,z5,z257,z6])]],
   [[(0,[z1,z258,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z259,z6])],[(0,[z1,z2,z3,z4,z5,z6,z54]),(0,[z1,z2,z34,z4,z5,z260,z6]),(0,[z1,z46,z79,z3,z4,z5,z6]),(1,[z9,z1,z3,z10,z5,z6]),(0,[z1,z261,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z262,z6]),(0,[z1,z2,z3,z4,z5,z6,z148])],[(0,[z1,z2,z3,z4,z263,z5,z6]),(0,[z1,z127,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z264]),(0,[z1,z2,z3,z4,z5,z265,z6]),(0,[z1,z2,z3,z4,z5,z6,z266]),(1,[z1,z3,z4,z5,z267,z6])],[(1,[z1,z2,z268,z4,z5,z6]),(0,[z1,z2,z3,z269,z4,z5,z6]),(1,[z1,z2,z55,z4,z5,z6]),(0,[z1,z2,z270,z3,z4,z5,z6]),(0,[z1,z2,z226,z3,z4,z5,z6]),(0,[z98,z1,z271,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z272,z5,z6])],[(1,[z1,z2,z273,z4,z5,z6]),(1,[z1,z2,z3,z4,z107,z6]),(0,[z1,z2,z3,z4,z274,z5,z6]),(0,[z1,z79,z2,z144,z4,z5,z6]),(0,[z1,z2,z275,z3,z4,z5,z6]),(0,[z276,z1,z2,z3,z4,z5,z6]),(0,[z50,z1,z41,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z277]),(0,[z1,z2,z278,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z279,z6]),(0,[z1,z130,z2,z34,z4,z5,z6]),(0,[z1,z2,z55,z4,z192,z5,z6]),(0,[z1,z2,z280,z3,z4,z5,z6]),(0,[z1,z46,z3,z100,z4,z5,z6]),(0,[z1,z2,z3,z281,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z72]),(0,[z1,z2,z3,z4,z65,z134,z5])],[(0,[z282,z1,z2,z3,z4,z5,z6])],[(0,[z118,z1,z2,z55,z4,z5,z6]),(1,[z1,z2,z90,z4,z5,z6]),(0,[z1,z2,z3,z4,z283,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z284]),(0,[z1,z285,z2,z3,z4,z5,z6]),(1,[z158,z1,z2,z4,z211,z6]),(0,[z1,z286,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z94,z6,z266]),(0,[z1,z287,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z288]),(0,[z1,z2,z55,z44,z4,z5,z6]),(0,[z1,z83,z2,z3,z119,z5,z6]),(0,[z1,z2,z3,z4,z207,z5,z6]),(1,[z1,z2,z3,z172,z5,z6])],[(0,[z1,z2,z289,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z290,z6]),(0,[z1,z79,z3,z4,z10,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z291]),(0,[z1,z2,z3,z44,z5,z125,z6]),(0,[z1,z2,z292,z3,z4,z5,z6])],[(0,[z1,z2,z3,z293,z4,z5,z6]),(0,[z294,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z55,z213,z4,z5,z6]),(0,[z1,z46,z3,z4,z5,z6,z51]),(1,[z1,z2,z3,z4,z5,z295]),(0,[z296,z1,z2,z3,z4,z5,z6])],[(0,[z297,z1,z2,z3,z4,z5,z6]),(0,[z118,z1,z2,z3,z4,z5,z6]),(0,[z1,z298,z2,z3,z4,z5,z6])],[(0,[z1,z127,z2,z144,z4,z5,z6]),(1,[z1,z83,z2,z3,z5,z63])],[(0,[z1,z2,z3,z4,z5,z299,z6]),(0,[z300,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z34,z44,z4,z5,z6]),(0,[z117,z1,z2,z3,z4,z301,z6]),(0,[z1,z2,z3,z119,z10,z5,z6]),(0,[z302,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z303,z3,z4,z5,z6]),(0,[z1,z2,z139,z3,z4,z5,z266])],[(0,[z1,z2,z3,z4,z5,z304,z6]),(0,[z117,z1,z2,z3,z119,z5,z6]),(0,[z1,z144,z3,z15,z4,z5,z6]),(0,[z1,z2,z305,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z293,z34,z4,z5,z6]),(0,[z2,z3,z119,z4,z205,z5,z6]),(0,[z1,z2,z3,z4,z5,z306,z6])],[(0,[z1,z2,z34,z213,z4,z5,z6]),(1,[z1,z2,z3,z4,z307,z6]),(1,[z1,z2,z3,z4,z5,z308]),(0,[z1,z2,z3,z4,z309,z5,z6]),(0,[z1,z310,z2,z3,z4,z5,z6])],[(0,[z1,z2,z311,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z312]),(0,[z1,z2,z44,z4,z207,z5,z6])],[(0,[z313,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z314,z5,z6]),(0,[z1,z37,z2,z3,z4,z75,z6])],[(0,[z1,z2,z3,z4,z315,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z316]),(0,[z1,z2,z3,z213,z207,z5,z6]),(0,[z1,z2,z3,z4,z317,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z318]),(0,[z26,z1,z2,z55,z4,z5,z6]),(0,[z319,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z320,z6])],[(0,[z153,z1,z2,z3,z321,z5,z6]),(1,[z118,z2,z34,z4,z5,z6]),(0,[z26,z1,z2,z3,z4,z107,z6]),(0,[z1,z322,z2,z3,z4,z5,z6]),(0,[z1,z2,z323,z3,z4,z5,z6]),(0,[z1,z324,z2,z3,z4,z5,z6]),(0,[z1,z239,z2,z3,z4,z96,z6])],[(0,[z23,z1,z2,z34,z4,z5,z6]),(0,[z325,z1,z2,z34,z4,z5,z6]),(0,[z1,z326,z2,z3,z4,z5,z6]),(0,[z327,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z132,z2,z55,z4,z5,z6]),(1,[z1,z200,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z328,z6]),(1,[z1,z127,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z22,z6])],[(1,[z1,z2,z86,z4,z5,z6]),(0,[z329,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z330,z6])],[(0,[z26,z1,z2,z3,z4,z5,z6]),(0,[z331,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z332,z1,z2,z3,z4,z5,z6]),(0,[z158,z1,z2,z3,z4,z5,z333]),(0,[z1,z2,z3,z4,z5,z6,z190])],[(0,[z27,z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z55,z4,z5,z6,z148]),(0,[z1,z2,z144,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z63,z168]),(0,[z1,z2,z3,z4,z5,z111,z51]),(0,[z1,z2,z334,z3,z4,z5,z6]),(0,[z1,z335,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z148,z51]),(0,[z1,z2,z3,z336,z4,z5,z6]),(0,[z158,z337,z2,z3,z4,z5,z6])],[(0,[z1,z2,z55,z4,z5,z6,z266]),(0,[z1,z2,z3,z4,z5,z16,z6]),(0,[z1,z2,z3,z4,z338,z5,z6]),(0,[z1,z339,z2,z3,z4,z5,z6])],[(0,[z23,z115,z2,z3,z4,z5,z6]),(0,[z1,z340,z2,z34,z4,z5,z6]),(0,[z1,z239,z2,z3,z4,z126,z6]),(0,[z1,z2,z341,z3,z4,z5,z6])],[(0,[z153,z1,z2,z3,z4,z5,z6]),(0,[z9,z1,z130,z3,z4,z5,z6]),(0,[z1,z2,z43,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z342]),(0,[z1,z2,z3,z4,z5,z6,z343]),(0,[z1,z2,z3,z344,z4,z5,z6]),(0,[z1,z83,z2,z3,z4,z96,z5])]],
   [[(1,[z1,z2,z3,z4,z299,z6]),(0,[z345,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z346,z4,z5,z6]),(0,[z347,z1,z2,z3,z4,z5,z6]),(0,[z348,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z349,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z350,z6])],[(0,[z1,z2,z3,z4,z5,z19,z6]),(0,[z1,z2,z3,z351,z4,z5,z6]),(0,[z1,z177,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z19,z6]),(0,[z1,z2,z3,z4,z5,z352,z6]),(0,[z1,z2,z3,z353,z4,z5,z6]),(0,[z1,z239,z2,z3,z4,z16,z6])],[(0,[z354,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z34,z4,z5,z6,z266]),(0,[z1,z2,z3,z4,z5,z260,z6]),(0,[z1,z175,z2,z55,z4,z5,z6]),(0,[z1,z2,z55,z4,z207,z5,z6]),(0,[z1,z2,z3,z4,z5,z295,z6]),(0,[z1,z2,z3,z4,z5,z6,z355])],[(0,[z1,z2,z3,z356,z4,z5,z6])],[(0,[z1,z115,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z357,z5,z6]),(0,[z358,z1,z2,z3,z4,z5,z6])],[(0,[z153,z1,z2,z3,z4,z5,z68]),(0,[z359,z1,z2,z55,z4,z5,z6])],[(0,[z360,z1,z2,z3,z4,z5,z6]),(0,[z361,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z362,z4,z5,z6]),(1,[z1,z2,z151,z4,z5,z6]),(0,[z1,z2,z3,z4,z363,z5,z6]),(0,[z1,z2,z3,z4,z364,z5,z6]),(0,[z1,z3,z4,z82,z5,z267,z6])]],
   [[(0,[z8,z1,z2,z34,z4,z5,z6]),(0,[z365,z1,z2,z3,z4,z5,z6]),(0,[z1,z366,z2,z3,z4,z5,z6]),(0,[z1,z367,z2,z3,z4,z5,z6]),(0,[z337,z1,z2,z3,z4,z5,z6])],[(0,[z1,z41,z115,z3,z4,z5,z6]),(0,[z194,z1,z2,z55,z4,z5,z6]),(0,[z1,z2,z34,z4,z207,z5,z6]),(0,[z368,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z55,z210,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z369,z6])],[(0,[z1,z2,z370,z3,z4,z5,z6]),(0,[z199,z1,z2,z55,z4,z5,z6]),(0,[z371,z1,z2,z3,z4,z5,z6]),(0,[z372,z1,z2,z3,z4,z5,z6]),(0,[z1,z373,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z374,z6]),(0,[z1,z375,z2,z3,z4,z5,z6])],[(0,[z153,z1,z2,z3,z4,z87,z6]),(0,[z359,z1,z2,z3,z4,z5,z6]),(0,[z27,z1,z2,z3,z4,z5,z168]),(0,[z1,z2,z376,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z10,z5,z6]),(0,[z1,z2,z3,z179,z4,z5,z6]),(0,[z1,z2,z3,z4,z211,z125,z6])],[(0,[z1,z123,z3,z4,z5,z16,z6]),(0,[z1,z2,z3,z4,z5,z377,z6]),(0,[z1,z2,z3,z378,z4,z5,z6]),(0,[z1,z2,z3,z4,z379,z5,z6]),(1,[z1,z239,z2,z3,z4,z96])],[(0,[z380,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z381,z5,z6]),(0,[z9,z1,z46,z3,z4,z5,z6]),(0,[z382,z1,z2,z3,z4,z5,z6])],[(0,[z383,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z34,z4,z5,z19,z6]),(0,[z1,z93,z2,z34,z4,z5,z6]),(0,[z1,z384,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z333])],[(0,[z1,z41,z123,z3,z4,z5,z6]),(0,[z1,z2,z34,z34,z4,z5,z6]),(0,[z385,z1,z2,z3,z4,z5,z6]),(0,[z1,z386,z2,z3,z4,z5,z6]),(1,[z387,z2,z3,z4,z5,z6]),(1,[z337,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z134,z5,z72])]],
   [[(0,[z1,z2,z3,z4,z5,z388,z6]),(0,[z1,z389,z2,z34,z4,z5,z6]),(0,[z1,z41,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z62,z4,z5,z148])],[(0,[z1,z46,z2,z34,z4,z5,z6]),(0,[z98,z1,z2,z3,z4,z126,z6]),(1,[z8,z2,z3,z4,z126,z6]),(0,[z27,z1,z2,z390,z4,z5,z6]),(1,[z1,z79,z144,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z391,z6])],[(0,[z392,z1,z2,z3,z4,z5,z6]),(1,[z23,z115,z3,z4,z5,z6]),(0,[z393,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z394])],[(0,[z1,z2,z395,z3,z4,z5,z6]),(0,[z1,z2,z140,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z114,z168]),(0,[z396,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z397,z3,z4,z5,z6]),(0,[z1,z398,z2,z3,z4,z5,z6]),(0,[z1,z399,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z400,z5,z6]),(1,[z1,z2,z3,z4,z82,z148])],[(0,[z1,z271,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z401,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z266,z148]),(0,[z1,z2,z3,z4,z5,z6,z402])],[(0,[z1,z2,z55,z4,z5,z6,z190]),(0,[z1,z2,z3,z4,z403,z5,z6]),(0,[z1,z2,z404,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z65,z5])],[(0,[z1,z79,z2,z55,z4,z5,z6]),(0,[z1,z405,z2,z3,z4,z5,z6]),(1,[z1,z2,z208,z4,z5,z6]),(0,[z9,z1,z2,z3,z100,z5,z6]),(0,[z1,z2,z406,z3,z4,z5,z6]),(1,[z1,z159,z3,z4,z5,z6]),(0,[z1,z2,z407,z3,z4,z5,z6]),(0,[z1,z408,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z55,z4,z5,z16,z6]),(0,[z1,z2,z3,z4,z409,z5,z6])],[(0,[z1,z239,z2,z55,z4,z5,z6]),(0,[z26,z1,z2,z151,z4,z5,z6]),(1,[z1,z2,z3,z410,z5,z6]),(0,[z92,z52,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z411,z5,z6])],[(0,[z1,z123,z3,z4,z10,z5,z6]),(1,[z1,z2,z3,z4,z301,z6]),(0,[z412,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z413,z5,z6]),(0,[z1,z127,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z414,z6]),(0,[z9,z1,z2,z3,z10,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z264]),(0,[z1,z415,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z94,z148]),(0,[z1,z2,z3,z134,z5,z125,z6])],[(0,[z1,z2,z3,z4,z5,z6,z416]),(0,[z1,z2,z3,z417,z4,z5,z6]),(0,[z1,z2,z3,z4,z418,z5,z6]),(0,[z1,z2,z3,z4,z419,z5,z6])],[(0,[z1,z2,z34,z4,z5,z6,z190]),(0,[z1,z2,z55,z4,z5,z19,z6]),(0,[z1,z2,z3,z4,z5,z420,z6]),(1,[z92,z1,z2,z207,z5,z6]),(0,[z421,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z73,z3,z4,z5,z6]),(0,[z1,z2,z3,z422,z4,z5,z6])],[(0,[z1,z2,z34,z4,z5,z16,z6]),(0,[z1,z423,z2,z3,z4,z5,z6]),(0,[z424,z1,z2,z3,z4,z5,z6]),(0,[z1,z425,z2,z3,z4,z5,z6])],[(0,[z118,z1,z2,z3,z119,z5,z6]),(0,[z1,z2,z3,z426,z4,z5,z6]),(1,[z50,z1,z3,z4,z5,z51]),(0,[z158,z1,z427,z3,z4,z5,z6])]],
   [[(0,[z428,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z429,z3,z4,z5,z6]),(0,[z1,z127,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z430,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z431,z5,z6]),(0,[z1,z2,z3,z4,z432,z5,z6])],[(0,[z1,z2,z3,z433,z4,z5,z6]),(0,[z1,z2,z34,z4,z5,z19,z6]),(0,[z117,z1,z2,z185,z4,z5,z6]),(0,[z1,z2,z3,z100,z205,z5,z6]),(0,[z1,z2,z3,z434,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z435])],[(0,[z23,z1,z2,z32,z4,z5,z6]),(0,[z117,z2,z3,z4,z205,z5,z6]),(0,[z158,z1,z2,z210,z4,z5,z6]),(0,[z436,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z82,z5,z148]),(0,[z1,z437,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z438,z4,z5,z6]),(1,[z1,z2,z3,z213,z134,z6])],[(1,[z1,z2,z24,z4,z5,z6]),(0,[z1,z2,z439,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z440,z5,z6]),(0,[z117,z1,z167,z3,z4,z5,z6]),(0,[z1,z441,z2,z3,z4,z5,z6]),(0,[z1,z239,z2,z3,z4,z96,z5])],[(0,[z1,z2,z442,z3,z4,z5,z6])],[(0,[z1,z2,z289,z55,z4,z5,z6]),(0,[z1,z2,z139,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z443,z5,z6]),(0,[z1,z2,z3,z4,z444,z5,z6]),(0,[z1,z2,z3,z4,z5,z445,z6]),(0,[z1,z46,z41,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z34,z362,z4,z5,z6]),(0,[z1,z2,z34,z4,z134,z5,z6]),(0,[z1,z2,z3,z102,z4,z5,z6]),(0,[z1,z2,z3,z4,z446,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z308]),(0,[z1,z2,z3,z447,z4,z5,z6]),(0,[z1,z448,z2,z3,z4,z5,z6]),(0,[z1,z83,z2,z3,z62,z5,z6])],[(0,[z449,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z450,z4,z5,z6]),(0,[z1,z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z134,z126,z6]),(0,[z1,z2,z3,z4,z75,z5,z6])],[(0,[z7,z1,z2,z34,z4,z5,z6]),(0,[z2,z55,z3,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z16,z6]),(0,[z26,z1,z2,z3,z410,z5,z6]),(0,[z451,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z452,z5,z6])],[(0,[z1,z2,z3,z4,z5,z453,z6]),(0,[z1,z2,z3,z4,z5,z454,z6]),(0,[z1,z2,z34,z4,z10,z5,z6]),(0,[z98,z1,z2,z55,z4,z5,z6]),(0,[z1,z2,z455,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z456,z6]),(0,[z1,z2,z457,z3,z4,z5,z6]),(0,[z1,z2,z139,z3,z4,z5,z6])],[(0,[z1,z458,z2,z3,z4,z5,z6]),(1,[z1,z37,z3,z4,z16,z6]),(0,[z1,z2,z3,z4,z5,z6,z459]),(0,[z1,z2,z3,z4,z5,z460,z6]),(0,[z1,z461,z2,z3,z4,z5,z6]),(0,[z1,z2,z462,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z150]),(1,[z1,z2,z3,z4,z178,z6]),(0,[z1,z2,z235,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z463,z5,z6]),(0,[z464,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z465])]],
   [[(0,[z1,z2,z311,z55,z4,z5,z6]),(0,[z98,z1,z2,z90,z4,z5,z6]),(0,[z2,z3,z4,z126,z5,z19,z6]),(0,[z8,z1,z2,z14,z4,z5,z6]),(0,[z8,z1,z2,z273,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z466,z6]),(0,[z50,z1,z2,z3,z4,z467,z6]),(0,[z1,z2,z3,z4,z5,z468,z6]),(0,[z1,z469,z2,z3,z4,z5,z6])],[(0,[z1,z115,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z4,z5,z6]),(0,[z98,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z470]),(0,[z471,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z472,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z473,z5,z6])],[(0,[z474,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z475,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z476,z6]),(1,[z1,z427,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z477,z5,z6])],[(0,[z1,z2,z123,z55,z4,z5,z6]),(0,[z1,z115,z3,z4,z5,z16,z6]),(0,[z1,z2,z3,z478,z4,z5,z6]),(0,[z1,z2,z3,z15,z4,z5,z6]),(0,[z479,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z480]),(0,[z1,z83,z2,z3,z4,z5,z148]),(0,[z1,z481,z2,z3,z4,z5,z6])],[(0,[z1,z83,z2,z3,z205,z5,z6]),(0,[z8,z1,z2,z3,z4,z5,z6]),(1,[z98,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z5,z111,z148]),(0,[z1,z2,z3,z4,z482,z5,z6]),(0,[z1,z2,z3,z4,z5,z114,z148]),(0,[z1,z2,z3,z4,z5,z94,z190]),(0,[z1,z2,z3,z4,z483,z5,z6])],[(0,[z153,z23,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z176,z4,z5,z6]),(0,[z1,z2,z3,z4,z75,z6,z148])],[(0,[z153,z1,z115,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z484,z5,z6]),(1,[z1,z2,z3,z4,z183,z6]),(0,[z1,z93,z2,z4,z5,z94,z6])],[(0,[z1,z2,z34,z4,z5,z94,z6]),(0,[z1,z485,z2,z3,z4,z5,z6]),(0,[z98,z8,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z342]),(0,[z1,z2,z3,z486,z4,z5,z6])]],
   [[(0,[z1,z2,z123,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z16,z6,z148]),(0,[z1,z46,z2,z3,z4,z75,z6]),(0,[z1,z2,z3,z4,z487,z5,z6]),(0,[z1,z488,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z267,z6])],[(0,[z117,z118,z2,z3,z4,z5,z6]),(0,[z1,z175,z2,z3,z213,z5,z6])],[(0,[z489,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z490,z4,z5,z6]),(0,[z98,z1,z2,z3,z4,z5,z308]),(0,[z1,z2,z3,z4,z96,z5,z6])],[(0,[z117,z1,z2,z3,z205,z5,z6]),(0,[z1,z37,z2,z3,z4,z5,z6]),(0,[z491,z1,z2,z3,z4,z5,z6])],[(0,[z153,z1,z123,z3,z4,z5,z6]),(0,[z1,z389,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z492]),(0,[z1,z2,z3,z4,z5,z493,z6]),(0,[z1,z2,z3,z494,z4,z5,z6]),(0,[z1,z495,z2,z3,z4,z5,z6])],[(0,[z153,z1,z2,z268,z4,z5,z6]),(0,[z153,z1,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z119,z5,z125,z6]),(1,[z1,z2,z3,z4,z5,z420]),(0,[z1,z37,z3,z4,z5,z16,z6]),(0,[z50,z1,z2,z3,z4,z5,z6]),(0,[z92,z1,z235,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z63,z6,z190]),(0,[z1,z2,z496,z3,z4,z5,z6])],[(0,[z118,z1,z2,z490,z4,z5,z6]),(1,[z1,z2,z3,z413,z5,z6])],[(0,[z497,z1,z2,z55,z4,z5,z6]),(0,[z1,z93,z2,z3,z4,z5,z266]),(0,[z1,z2,z3,z4,z96,z5,z266]),(0,[z1,z2,z3,z4,z498,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z499,z5,z6])],[(0,[z1,z115,z3,z4,z10,z5,z6]),(0,[z118,z2,z3,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z500,z6]),(1,[z1,z2,z3,z4,z5,z233]),(0,[z1,z2,z3,z4,z96,z5,z114]),(0,[z1,z501,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z438,z5,z6]),(0,[z1,z2,z3,z4,z502,z5,z6]),(0,[z503,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z210,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z504]),(0,[z1,z2,z505,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z205,z5,z6]),(0,[z98,z1,z2,z3,z4,z5,z420]),(0,[z1,z127,z79,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z205,z5,z6]),(0,[z497,z1,z2,z3,z4,z5,z6]),(0,[z27,z1,z2,z3,z4,z5,z111]),(0,[z1,z506,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z507,z5,z6]),(0,[z50,z1,z2,z3,z4,z5,z114]),(0,[z1,z508,z2,z3,z4,z5,z6]),(0,[z1,z509,z2,z3,z4,z5,z6]),(0,[z1,z510,z2,z3,z4,z5,z6])],[(0,[z511,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z512]),(0,[z1,z513,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z514,z6]),(0,[z1,z2,z3,z4,z96,z6,z148])],[(0,[z1,z83,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z213,z119,z5,z6]),(0,[z1,z515,z2,z3,z4,z5,z6]),(0,[z158,z375,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z333])],[(0,[z1,z2,z516,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z168,z51]),(0,[z1,z2,z3,z517,z4,z5,z6]),(0,[z1,z2,z518,z3,z4,z5,z6]),(0,[z1,z2,z519,z3,z4,z5,z6])]],
   [[(0,[z1,z130,z115,z3,z4,z5,z6]),(0,[z92,z1,z2,z55,z4,z5,z6]),(0,[z1,z79,z130,z3,z4,z5,z6]),(0,[z1,z81,z2,z3,z4,z5,z6])],[(0,[z124,z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z520,z5,z6]),(0,[z1,z239,z2,z3,z4,z19,z6]),(0,[z521,z1,z2,z3,z4,z5,z6]),(0,[z1,z130,z3,z15,z4,z5,z6]),(0,[z522,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z178,z5,z6]),(0,[z1,z2,z3,z523,z4,z5,z6]),(0,[z1,z524,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z525,z4,z5,z6]),(0,[z1,z2,z3,z526,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z527,z6]),(0,[z1,z2,z3,z4,z134,z5,z6])],[(0,[z1,z2,z34,z4,z75,z5,z6]),(0,[z1,z2,z3,z4,z5,z528,z6]),(1,[z1,z2,z390,z4,z5,z6]),(0,[z1,z2,z529,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z35,z125,z6]),(0,[z530,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z531,z5,z6]),(0,[z1,z2,z55,z34,z4,z5,z6]),(0,[z1,z2,z516,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z532]),(0,[z1,z533,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z534,z4,z5,z6])],[(0,[z1,z2,z3,z4,z535,z5,z6]),(0,[z117,z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z75,z126,z6]),(0,[z1,z2,z3,z4,z536,z5,z6]),(0,[z1,z537,z2,z3,z4,z5,z6]),(0,[z92,z1,z2,z3,z4,z5,z6]),(0,[z1,z83,z2,z3,z5,z63,z6])],[(0,[z1,z130,z123,z3,z4,z5,z6]),(0,[z1,z538,z2,z3,z4,z5,z6]),(0,[z1,z255,z2,z3,z4,z5,z6]),(0,[z1,z2,z55,z478,z4,z5,z6]),(0,[z1,z2,z55,z15,z4,z5,z6]),(0,[z1,z2,z200,z3,z4,z5,z6]),(0,[z1,z539,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z493,z6]),(0,[z1,z2,z3,z540,z4,z5,z6]),(0,[z1,z2,z3,z4,z541,z5,z6]),(0,[z1,z2,z3,z4,z5,z542,z6]),(0,[z1,z543,z2,z3,z4,z5,z6])],[(0,[z1,z2,z144,z34,z4,z5,z6]),(0,[z1,z130,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z213,z205,z5,z6]),(0,[z1,z2,z3,z4,z5,z544,z6]),(0,[z1,z2,z3,z62,z4,z5,z6])]],
   [[(0,[z2,z3,z34,z4,z205,z5,z6]),(0,[z1,z2,z490,z3,z4,z5,z6]),(0,[z1,z2,z545,z3,z4,z5,z6]),(0,[z26,z1,z2,z3,z413,z5,z6]),(0,[z1,z2,z3,z4,z5,z546,z6]),(0,[z92,z1,z2,z3,z4,z5,z295])],[(0,[z1,z2,z3,z4,z5,z547,z6]),(0,[z1,z2,z3,z410,z4,z5,z6])],[],[(0,[z153,z1,z2,z86,z4,z5,z6]),(0,[z8,z2,z3,z4,z126,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z548]),(0,[z549,z1,z2,z3,z4,z5,z6]),(0,[z550,z1,z2,z3,z4,z5,z6])],[(0,[z1,z551,z2,z3,z4,z5,z6]),(0,[z1,z2,z552,z3,z4,z5,z6]),(0,[z1,z553,z2,z3,z4,z5,z6]),(0,[z1,z2,z34,z15,z4,z5,z6]),(0,[z1,z554,z2,z3,z4,z5,z6]),(0,[z1,z130,z2,z3,z4,z5,z6])],[],[(0,[z1,z175,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z96,z5,z111]),(0,[z92,z1,z2,z43,z4,z5,z6]),(0,[z1,z2,z3,z213,z134,z5,z6]),(0,[z555,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z556,z4,z5,z6])],[(0,[z1,z2,z3,z4,z557,z5,z6]),(0,[z1,z2,z3,z4,z301,z5,z6]),(0,[z8,z1,z2,z3,z4,z126,z6]),(0,[z1,z2,z3,z4,z5,z558,z6]),(0,[z26,z1,z2,z3,z4,z5,z168]),(0,[z1,z559,z2,z3,z4,z5,z6]),(0,[z387,z1,z2,z3,z4,z5,z6]),(0,[z158,z1,z2,z3,z4,z5,z104]),(0,[z1,z560,z2,z3,z4,z5,z6])]],
   [[(1,[z2,z55,z34,z4,z5,z6]),(0,[z561,z1,z2,z3,z4,z5,z6]),(1,[z1,z81,z3,z4,z5,z6]),(0,[z1,z2,z562,z3,z4,z5,z6])],[(0,[z153,z1,z2,z3,z438,z5,z6]),(0,[z1,z2,z3,z14,z4,z5,z6]),(1,[z375,z2,z3,z4,z5,z6]),(0,[z1,z93,z2,z139,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z94,z6]),(0,[z1,z2,z3,z4,z96,z82,z5])],[(0,[z153,z1,z2,z3,z4,z299,z6]),(0,[z23,z1,z115,z3,z4,z5,z6]),(0,[z7,z118,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z563])],[(0,[z1,z2,z34,z4,z96,z5,z6]),(0,[z1,z564,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z565,z5,z6]),(0,[z1,z41,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z5,z566,z6])],[(0,[z194,z1,z2,z34,z4,z5,z6]),(0,[z98,z1,z2,z3,z4,z19,z6]),(0,[z1,z567,z2,z3,z4,z5,z6]),(0,[z568,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z63,z6]),(0,[z1,z2,z569,z3,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z570,z1,z2,z3,z4,z5,z6]),(0,[z199,z1,z2,z34,z4,z5,z6]),(0,[z1,z571,z2,z3,z4,z5,z6]),(0,[z1,z159,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z572,z6]),(0,[z573,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z55,z4,z205,z5,z6]),(0,[z574,z1,z2,z3,z4,z5,z6])],[]],
   [[(0,[z23,z1,z123,z3,z4,z5,z6]),(0,[z575,z1,z2,z3,z4,z5,z6]),(0,[z26,z1,z2,z3,z4,z493,z6]),(0,[z1,z2,z3,z100,z4,z5,z6]),(0,[z1,z2,z139,z3,z4,z5,z94]),(0,[z1,z2,z3,z4,z5,z190,z266])],[(0,[z23,z1,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z576,z5,z6]),(0,[z1,z2,z3,z4,z5,z63,z266])],[(0,[z158,z1,z2,z3,z4,z211,z6]),(0,[z577,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z82,z5,z6])],[(0,[z194,z2,z3,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z212,z5,z6]),(0,[z1,z2,z3,z4,z5,z211,z6])],[(0,[z1,z2,z34,z4,z205,z5,z6]),(0,[z9,z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z442,z55,z4,z5,z6]),(0,[z1,z2,z3,z119,z4,z5,z6]),(0,[z92,z1,z2,z3,z4,z5,z342]),(0,[z1,z40,z2,z3,z4,z5,z6])],[(0,[z578,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z55,z4,z134,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z579]),(0,[z1,z2,z3,z4,z5,z241,z6]),(0,[z580,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z581,z5,z6])],[(0,[z23,z1,z2,z3,z4,z5,z6]),(0,[z158,z1,z2,z34,z4,z5,z6]),(0,[z325,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z74,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z233,z6]),(0,[z1,z2,z3,z4,z5,z6,z51]),(0,[z1,z2,z43,z3,z207,z5,z6]),(0,[z1,z2,z582,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z68,z6]),(0,[z1,z2,z3,z583,z4,z5,z6]),(0,[z1,z2,z273,z3,z4,z5,z6]),(0,[z1,z584,z2,z3,z4,z5,z6]),(0,[z158,z1,z2,z3,z4,z35,z6])]],
   [[(0,[z1,z2,z3,z4,z585,z5,z6]),(0,[z1,z2,z3,z4,z586,z5,z6])],[(0,[z1,z2,z55,z4,z10,z5,z6]),(1,[z1,z2,z3,z99,z5,z6]),(0,[z1,z2,z210,z4,z35,z5,z6])],[(0,[z1,z2,z34,z4,z520,z5,z6]),(0,[z1,z79,z2,z34,z4,z5,z6]),(0,[z1,z2,z55,z62,z4,z5,z6]),(1,[z27,z2,z3,z4,z5,z111]),(1,[z1,z2,z3,z4,z5,z104])],[(0,[z118,z1,z2,z3,z205,z5,z6]),(0,[z27,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z587]),(0,[z1,z2,z3,z4,z588,z5,z6])],[(0,[z1,z239,z2,z34,z4,z5,z6]),(0,[z1,z2,z55,z4,z5,z547,z6]),(0,[z1,z589,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z590]),(0,[z1,z591,z2,z3,z4,z5,z6])],[(0,[z1,z340,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z592,z6]),(0,[z1,z2,z593,z3,z4,z5,z6]),(0,[z1,z2,z3,z62,z4,z5,z190]),(0,[z1,z2,z3,z4,z82,z6,z148])],[(0,[z594,z1,z2,z3,z4,z5,z6]),(0,[z1,z595,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z596,z6]),(0,[z1,z2,z139,z4,z5,z6,z266]),(0,[z1,z597,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z598])],[(0,[z1,z115,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z599,z4,z5,z6]),(0,[z1,z2,z43,z44,z4,z5,z6]),(0,[z1,z2,z600,z3,z4,z5,z6])]],
   [[(1,[z2,z34,z4,z205,z5,z6]),(0,[z1,z2,z34,z62,z4,z5,z6]),(0,[z601,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z602,z5,z6]),(0,[z603,z1,z2,z3,z4,z5,z6]),(0,[z1,z40,z3,z4,z134,z5,z6]),(0,[z1,z2,z3,z4,z5,z604,z6])],[(1,[z2,z34,z4,z5,z19,z6]),(0,[z1,z2,z3,z605,z4,z5,z6]),(0,[z92,z1,z2,z3,z207,z5,z6])],[(0,[z8,z1,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z606,z4,z5,z6]),(0,[z1,z2,z607,z3,z4,z5,z6]),(0,[z1,z83,z2,z3,z4,z5,z6])],[(0,[z1,z127,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z608,z6])],[(0,[z1,z2,z270,z34,z4,z5,z6]),(0,[z1,z2,z3,z439,z4,z5,z6]),(0,[z1,z2,z55,z4,z5,z94,z6]),(0,[z1,z2,z3,z205,z5,z6,z190]),(0,[z118,z1,z2,z102,z4,z5,z6]),(0,[z1,z2,z3,z4,z609,z5,z6]),(0,[z92,z387,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z610,z6])],[(0,[z1,z485,z2,z55,z4,z5,z6]),(0,[z1,z2,z55,z4,z5,z6,z563]),(0,[z1,z2,z3,z4,z134,z19,z6])],[(0,[z1,z611,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z612,z5,z6]),(0,[z1,z613,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z614,z6])],[(0,[z1,z2,z3,z4,z5,z615,z6]),(0,[z616,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z241,z6]),(0,[z1,z2,z3,z213,z44,z5,z6]),(0,[z1,z617,z2,z3,z4,z5,z6]),(0,[z618,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z619,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z321,z5,z6]),(0,[z1,z93,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z63,z111]),(0,[z1,z37,z2,z3,z4,z5,z264]),(0,[z1,z2,z3,z4,z5,z6,z620]),(0,[z1,z2,z3,z4,z621,z5,z6])],[(1,[z1,z2,z34,z4,z5,z6]),(0,[z1,z37,z2,z55,z4,z5,z6]),(0,[z622,z1,z2,z3,z4,z5,z6])],[(0,[z1,z46,z123,z3,z4,z5,z6]),(0,[z623,z1,z2,z3,z4,z5,z6]),(0,[z1,z624,z2,z3,z4,z5,z6]),(1,[z1,z157,z3,z4,z5,z6]),(1,[z1,z2,z3,z62,z5,z190]),(0,[z1,z2,z3,z625,z4,z5,z6])],[(0,[z1,z2,z55,z100,z4,z5,z6]),(0,[z50,z1,z2,z55,z4,z5,z6]),(0,[z117,z1,z2,z3,z4,z5,z45]),(0,[z1,z2,z3,z4,z5,z6,z626]),(0,[z1,z2,z3,z4,z627,z5,z6])],[],[(0,[z118,z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z34,z4,z5,z63,z6]),(0,[z1,z2,z55,z4,z82,z5,z6]),(1,[z1,z2,z176,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z168]),(0,[z1,z2,z3,z4,z5,z6,z628]),(0,[z1,z2,z3,z4,z5,z6,z629]),(0,[z1,z93,z2,z3,z4,z5,z6])],[(0,[z1,z2,z55,z4,z5,z211,z6]),(0,[z1,z2,z390,z3,z4,z5,z6]),(0,[z630,z1,z2,z3,z4,z5,z6])],[(1,[z8,z2,z34,z4,z5,z6]),(0,[z1,z2,z55,z119,z4,z5,z6]),(0,[z1,z2,z3,z4,z126,z125,z6]),(0,[z1,z2,z3,z4,z5,z168,z148])]],
   [[(1,[z1,z2,z631,z4,z5,z6]),(0,[z1,z46,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z114,z6,z51]),(0,[z1,z2,z3,z632,z4,z5,z6])],[(0,[z633,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z34,z100,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z634,z6]),(0,[z1,z2,z3,z4,z635,z5,z6])],[(0,[z1,z2,z55,z583,z4,z5,z6]),(0,[z117,z1,z2,z74,z4,z5,z6]),(0,[z117,z1,z2,z3,z4,z307,z6]),(0,[z1,z636,z2,z3,z4,z5,z6])],[(0,[z1,z2,z34,z4,z82,z5,z6]),(0,[z1,z2,z3,z4,z5,z637,z6]),(0,[z1,z2,z3,z4,z5,z638,z6]),(0,[z1,z2,z3,z4,z5,z639,z6])],[(0,[z1,z162,z2,z3,z4,z5,z6]),(0,[z1,z2,z34,z4,z5,z211,z6]),(0,[z1,z2,z3,z205,z10,z5,z6]),(0,[z1,z2,z3,z4,z640,z5,z6]),(0,[z1,z2,z3,z4,z5,z641,z6]),(0,[z1,z2,z3,z4,z35,z5,z6]),(0,[z642,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z34,z119,z4,z5,z6]),(0,[z1,z2,z643,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z644,z5,z6]),(0,[z1,z2,z3,z4,z5,z467,z6]),(0,[z1,z2,z3,z645,z4,z5,z6]),(1,[z1,z2,z139,z4,z5,z266])],[(0,[z1,z2,z34,z4,z5,z6,z51]),(0,[z1,z2,z3,z4,z646,z5,z6]),(1,[z1,z2,z3,z212,z5,z6]),(0,[z1,z2,z3,z4,z5,z647,z6]),(0,[z1,z648,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z32,z3,z4,z5,z6]),(0,[z1,z2,z55,z4,z75,z5,z6]),(0,[z1,z2,z55,z4,z5,z592,z6]),(0,[z27,z2,z3,z4,z5,z111,z6]),(0,[z649,z1,z2,z3,z4,z5,z6]),(0,[z1,z650,z2,z3,z4,z5,z6]),(0,[z651,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z427,z3,z4,z5,z6]),(0,[z1,z239,z2,z3,z4,z82,z6])],[(0,[z652,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z653,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z654]),(0,[z1,z2,z3,z655,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z656,z6])],[(0,[z1,z2,z4,z35,z5,z211,z6])],[(0,[z26,z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z69,z5,z6]),(0,[z1,z2,z3,z4,z657,z5,z6])],[(0,[z1,z658,z2,z3,z4,z5,z6]),(0,[z1,z2,z659,z3,z4,z5,z6]),(0,[z1,z175,z2,z3,z4,z125,z6]),(0,[z1,z2,z3,z4,z5,z660,z6])],[(1,[z1,z226,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z661,z5,z6]),(0,[z1,z2,z3,z4,z5,z662,z6]),(0,[z1,z41,z3,z4,z5,z114,z6]),(0,[z1,z2,z3,z4,z663,z5,z6])],[(0,[z1,z664,z2,z3,z4,z5,z6]),(0,[z1,z665,z2,z3,z4,z5,z6]),(0,[z1,z666,z2,z3,z4,z5,z6])],[(0,[z1,z667,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z114,z111]),(0,[z1,z2,z668,z3,z4,z5,z6]),(1,[z1,z175,z2,z3,z125,z6])]],
   [[(0,[z1,z2,z268,z3,z4,z5,z6]),(0,[z1,z669,z2,z3,z4,z5,z6]),(0,[z9,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z670,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z671]),(0,[z1,z83,z2,z3,z4,z5,z190])],[(0,[z1,z2,z34,z101,z4,z5,z6]),(1,[z1,z2,z185,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z111,z190]),(0,[z1,z2,z3,z4,z5,z672,z6]),(0,[z1,z2,z3,z4,z5,z673,z6]),(0,[z1,z674,z2,z3,z4,z5,z6])],[(1,[z194,z2,z34,z4,z5,z6]),(0,[z26,z1,z2,z631,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z675]),(0,[z9,z1,z3,z4,z5,z16,z6]),(0,[z1,z2,z3,z4,z5,z676,z6]),(0,[z1,z677,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z678,z6])],[(0,[z679,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z99,z4,z5,z6]),(0,[z1,z239,z2,z3,z4,z75,z6]),(0,[z1,z2,z3,z4,z680,z5,z6]),(0,[z1,z681,z2,z3,z4,z5,z6])],[(0,[z682,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z34,z4,z5,z111,z6]),(0,[z1,z2,z34,z4,z5,z114,z6]),(0,[z1,z1,z2,z55,z4,z5,z6]),(1,[z1,z167,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z683,z6])],[(0,[z1,z684,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z685,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z686]),(0,[z92,z1,z2,z4,z207,z5,z6])],[(0,[z687,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z34,z4,z126,z5,z6]),(0,[z1,z2,z3,z4,z688,z5,z6]),(1,[z1,z41,z3,z4,z5,z114]),(0,[z1,z689,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z690,z5,z6]),(0,[z1,z2,z3,z213,z4,z125,z6]),(0,[z1,z2,z3,z4,z691,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z692,z5,z6]),(0,[z693,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z55,z4,z5,z6,z168]),(0,[z1,z2,z55,z4,z96,z5,z6]),(0,[z1,z2,z3,z4,z75,z19,z6]),(1,[z1,z2,z3,z4,z467,z6]),(1,[z1,z2,z43,z44,z5,z6]),(0,[z1,z2,z3,z694,z4,z5,z6]),(0,[z158,z1,z2,z4,z5,z211,z6]),(0,[z1,z2,z3,z695,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z696]),(0,[z98,z2,z3,z4,z5,z19,z6])],[(0,[z7,z1,z2,z3,z4,z5,z6]),(1,[z1,z271,z3,z4,z5,z6]),(0,[z1,z2,z631,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z697,z6]),(0,[z1,z130,z2,z3,z10,z5,z6]),(1,[z1,z130,z3,z100,z5,z6]),(0,[z92,z1,z2,z3,z4,z183,z6])],[(1,[z1,z2,z3,z321,z5,z6]),(0,[z698,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z307,z6]),(0,[z1,z79,z144,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z699,z6]),(0,[z1,z700,z2,z3,z4,z5,z6]),(0,[z1,z239,z2,z3,z4,z5,z148])],[(0,[z1,z701,z2,z3,z4,z5,z6]),(0,[z1,z2,z34,z4,z5,z149,z6]),(0,[z1,z702,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z125,z6])],[(0,[z153,z2,z123,z3,z4,z5,z6]),(0,[z1,z2,z34,z4,z5,z6,z168]),(0,[z1,z2,z3,z4,z5,z703,z6]),(0,[z1,z46,z37,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z704,z6]),(0,[z1,z175,z2,z3,z5,z125,z6])],[(0,[z1,z2,z55,z4,z35,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z705]),(0,[z1,z2,z3,z4,z5,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z2,z707,z34,z4,z5,z6]),(0,[z1,z2,z708,z4,z5,z6]),(0,[z1,z2,z34,z172,z5,z6]),(0,[z1,z2,z3,z4,z57,z148]),(0,[z1,z709,z3,z4,z5,z6]),(0,[z158,z1,z2,z4,z710,z6])],[(0,[z1,z140,z3,z4,z5,z6]),(0,[z1,z2,z73,z4,z5,z116]),(0,[z117,z167,z3,z205,z5,z6]),(0,[z1,z3,z4,z58,z16,z6]),(0,[z92,z1,z157,z207,z5,z6]),(0,[z1,z2,z3,z4,z241,z295]),(0,[z1,z2,z3,z172,z35,z6])],[(0,[z2,z34,z4,z5,z542,z6])],[(0,[z1,z2,z34,z4,z5,z150]),(0,[z2,z34,z213,z205,z5,z6]),(0,[z1,z711,z3,z4,z5,z6]),(0,[z1,z2,z631,z4,z107,z6]),(0,[z26,z2,z3,z4,z107,z168])],[(0,[z1,z2,z3,z712,z5,z6]),(0,[z1,z2,z176,z4,z5,z6]),(0,[z1,z2,z3,z713,z5,z6])],[(0,[z1,z2,z3,z4,z299,z54]),(0,[z2,z34,z4,z5,z547,z6]),(0,[z1,z2,z34,z4,z5,z714]),(0,[z1,z2,z3,z4,z715,z6])],[(0,[z8,z2,z34,z4,z5,z6]),(0,[z8,z2,z708,z4,z5,z6]),(0,[z1,z716,z2,z34,z4,z6]),(0,[z1,z2,z3,z410,z493,z6]),(0,[z375,z2,z3,z4,z5,z333])],[(0,[z1,z34,z4,z5,z22,z6]),(0,[z1,z2,z55,z4,z5,z717]),(0,[z1,z718,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z719]),(0,[z1,z720,z3,z4,z5,z6]),(0,[z26,z2,z3,z4,z5,z168]),(0,[z92,z1,z2,z721,z5,z6])]],
   [[(0,[z1,z722,z3,z4,z5,z6]),(0,[z1,z723,z2,z4,z5,z6]),(0,[z1,z2,z60,z4,z35,z6])],[(0,[z1,z2,z3,z4,z5,z724]),(0,[z1,z2,z34,z4,z5,z308]),(0,[z1,z2,z55,z212,z5,z6])],[(0,[z8,z2,z176,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z725]),(0,[z1,z239,z3,z4,z267,z6]),(0,[z1,z81,z3,z4,z82,z148])],[(0,[z209,z2,z34,z4,z5,z6]),(0,[z287,z2,z34,z4,z5,z6]),(0,[z1,z3,z4,z126,z22,z6]),(0,[z1,z2,z726,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z717]),(0,[z727,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z728,z5])],[(0,[z1,z2,z3,z4,z729,z6]),(0,[z1,z2,z176,z4,z5,z308]),(0,[z1,z2,z90,z212,z5,z6]),(0,[z1,z2,z730,z4,z5,z6]),(1,[z1,z3,z731,z5,z6]),(0,[z52,z2,z3,z4,z241,z6]),(0,[z1,z310,z2,z3,z125,z6]),(0,[z1,z2,z139,z4,z5,z266]),(0,[z1,z732,z3,z4,z5,z6])],[(0,[z153,z123,z3,z321,z5,z6]),(0,[z242,z2,z55,z4,z5,z6]),(0,[z1,z2,z733,z4,z5,z6]),(0,[z1,z2,z3,z212,z5,z6])],[(0,[z1,z2,z734,z4,z5,z6]),(0,[z1,z226,z55,z4,z5,z6]),(0,[z1,z2,z55,z735,z5,z6]),(0,[z1,z2,z3,z4,z736,z6]),(0,[z1,z2,z737,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z738,z5,z6]),(0,[z739,z123,z3,z4,z5,z6]),(0,[z1,z200,z34,z4,z5,z6]),(0,[z1,z2,z3,z5,z740,z6])],[(0,[z1,z2,z55,z4,z5,z741]),(0,[z1,z742,z55,z4,z5,z6]),(0,[z382,z2,z3,z4,z5,z111]),(0,[z1,z239,z2,z3,z4,z728])],[(0,[z1,z2,z3,z4,z743,z6]),(0,[z1,z2,z34,z4,z5,z420]),(0,[z1,z239,z2,z34,z4,z96]),(0,[z1,z744,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z745,z6])],[(0,[z296,z2,z34,z4,z5,z6]),(0,[z1,z226,z90,z4,z5,z6])],[(0,[z194,z2,z707,z4,z5,z6]),(0,[z117,z2,z3,z205,z5,z45]),(0,[z1,z3,z4,z19,z22,z6]),(0,[z1,z2,z3,z4,z126,z72]),(0,[z1,z746,z3,z4,z5,z6]),(0,[z1,z3,z4,z267,z6,z148])],[(0,[z2,z34,z4,z576,z5,z6]),(0,[z1,z747,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z748]),(0,[z1,z2,z3,z4,z241,z342])],[(0,[z1,z2,z749,z4,z5,z6]),(0,[z1,z41,z3,z4,z5,z454]),(0,[z1,z2,z3,z4,z5,z750]),(0,[z1,z167,z55,z4,z5,z6]),(0,[z1,z2,z3,z751,z5,z6]),(0,[z1,z2,z752,z4,z5,z6]),(0,[z1,z2,z3,z4,z753,z6]),(0,[z1,z2,z754,z4,z5,z6]),(0,[z1,z175,z2,z3,z125,z6])],[(0,[z153,z123,z3,z4,z5,z6]),(0,[z1,z115,z3,z321,z5,z6]),(0,[z1,z2,z34,z438,z5,z6]),(0,[z1,z2,z34,z4,z5,z342]),(0,[z1,z2,z3,z212,z5,z308]),(0,[z1,z93,z2,z4,z5,z755]),(0,[z1,z756,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z34,z4,z299,z6]),(0,[z1,z79,z270,z4,z5,z6]),(0,[z1,z41,z55,z4,z5,z114]),(0,[z1,z2,z3,z4,z757,z5]),(0,[z1,z2,z758,z4,z5,z6]),(0,[z1,z157,z3,z4,z5,z342]),(0,[z337,z2,z3,z4,z5,z104]),(0,[z1,z2,z3,z4,z5,z759])],[(0,[z1,z2,z3,z4,z5,z760]),(0,[z1,z2,z3,z62,z5,z761])],[(0,[z1,z2,z3,z4,z5,z762]),(0,[z1,z2,z55,z4,z467,z6]),(0,[z1,z2,z3,z213,z403,z6]),(0,[z1,z2,z763,z4,z5,z6])],[(0,[z117,z2,z74,z205,z5,z6]),(0,[z1,z2,z185,z4,z5,z150]),(0,[z1,z764,z3,z4,z5,z6]),(0,[z1,z765,z3,z4,z5,z6]),(0,[z1,z2,z4,z721,z5,z6]),(1,[z1,z2,z4,z5,z755])],[(0,[z1,z2,z3,z4,z5,z766]),(0,[z1,z340,z270,z4,z5,z6]),(0,[z1,z235,z3,z4,z5,z6]),(0,[z1,z46,z3,z4,z314,z6]),(0,[z1,z2,z3,z4,z5,z767]),(0,[z1,z3,z4,z768,z16,z6]),(0,[z52,z2,z311,z4,z5,z6]),(0,[z1,z2,z769,z4,z5,z6])],[(0,[z1,z123,z3,z321,z5,z6]),(0,[z1,z2,z442,z4,z5,z563]),(0,[z1,z226,z3,z4,z5,z308]),(0,[z1,z2,z3,z179,z5,z6])],[(0,[z1,z2,z268,z321,z5,z6]),(0,[z1,z2,z55,z321,z5,z6]),(0,[z153,z123,z3,z4,z5,z68]),(0,[z1,z2,z3,z770,z5,z6]),(0,[z1,z167,z3,z4,z5,z150]),(0,[z1,z2,z3,z4,z5,z771]),(0,[z1,z2,z3,z4,z772,z6]),(1,[z1,z3,z4,z768,z6]),(0,[z1,z2,z4,z5,z755,z266]),(0,[z1,z2,z3,z4,z96,z581])],[(0,[z105,z123,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z773]),(0,[z1,z2,z3,z4,z467,z6]),(0,[z1,z2,z3,z4,z5,z774]),(0,[z375,z2,z3,z4,z5,z104]),(1,[z1,z3,z4,z267,z148])]],
   [[(0,[z1,z271,z90,z4,z5,z6]),(0,[z1,z2,z3,z212,z5,z420]),(0,[z27,z2,z208,z4,z5,z111])],[(0,[z1,z271,z3,z4,z5,z6]),(0,[z1,z2,z3,z775,z5,z6]),(0,[z1,z2,z3,z4,z75,z264]),(0,[z1,z2,z3,z776,z5,z6])],[(0,[z1,z2,z3,z413,z5,z168]),(0,[z1,z130,z3,z100,z5,z6]),(0,[z1,z2,z3,z207,z241,z6]),(0,[z1,z2,z777,z4,z5,z6])],[(0,[z1,z2,z3,z321,z5,z6]),(0,[z1,z2,z3,z4,z5,z778]),(0,[z1,z2,z779,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z780]),(0,[z1,z2,z3,z4,z781,z6])],[(0,[z1,z115,z3,z4,z5,z54]),(0,[z2,z34,z4,z602,z5,z6]),(0,[z1,z2,z55,z4,z782,z6]),(0,[z1,z650,z3,z4,z16,z6])],[(0,[z9,z1,z3,z10,z5,z6])],[(0,[z1,z2,z3,z783,z5,z6]),(0,[z1,z2,z34,z784,z5,z6]),(0,[z2,z34,z606,z4,z5,z6]),(0,[z1,z2,z34,z4,z5,z333]),(0,[z1,z2,z55,z4,z785,z6]),(0,[z1,z226,z3,z4,z5,z420]),(0,[z1,z2,z3,z4,z467,z114]),(0,[z1,z786,z3,z4,z5,z6])],[(0,[z1,z2,z787,z4,z5,z6]),(0,[z387,z2,z34,z4,z5,z6]),(0,[z337,z2,z34,z4,z5,z6]),(0,[z1,z40,z55,z4,z5,z6]),(0,[z358,z2,z3,z4,z5,z168]),(0,[z387,z2,z3,z4,z183,z6]),(0,[z788,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z273,z4,z5,z6]),(0,[z2,z34,z205,z5,z6,z190]),(0,[z1,z2,z34,z4,z789,z6]),(0,[z2,z34,z4,z5,z610,z6]),(0,[z1,z2,z14,z4,z5,z6]),(0,[z1,z2,z3,z4,z107,z6]),(0,[z26,z177,z3,z4,z5,z168]),(0,[z1,z3,z4,z5,z16,z264]),(0,[z1,z2,z3,z4,z635,z148]),(0,[z387,z157,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z790,z6]),(0,[z2,z34,z4,z134,z19,z6]),(0,[z1,z2,z55,z4,z5,z45]),(0,[z1,z2,z3,z4,z5,z791]),(0,[z1,z130,z3,z353,z5,z6]),(0,[z1,z2,z3,z792,z5,z6]),(0,[z92,z52,z2,z207,z5,z6]),(0,[z793,z2,z3,z4,z5,z6])],[(0,[z550,z123,z3,z4,z5,z6]),(0,[z23,z115,z34,z4,z5,z6]),(0,[z1,z794,z3,z4,z5,z6]),(0,[z795,z2,z3,z4,z5,z6]),(0,[z375,z2,z516,z4,z5,z6]),(0,[z375,z427,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z267,z148])],[(0,[z1,z2,z268,z4,z5,z54]),(0,[z1,z2,z55,z4,z5,z54]),(0,[z1,z2,z796,z4,z5,z6]),(0,[z1,z2,z34,z4,z82,z148]),(0,[z1,z2,z3,z4,z785,z6]),(0,[z387,z2,z490,z4,z5,z6]),(0,[z1,z2,z3,z413,z493,z6]),(0,[z52,z235,z3,z4,z5,z6]),(0,[z1,z797,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z32,z4,z5,z6]),(0,[z1,z2,z73,z4,z5,z266]),(0,[z1,z162,z478,z4,z5,z6]),(0,[z1,z537,z15,z4,z5,z6])],[(0,[z511,z1,z3,z10,z5,z6]),(0,[z1,z2,z798,z4,z5,z6]),(0,[z1,z81,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z799,z6])],[(0,[z1,z2,z800,z4,z5,z6]),(0,[z375,z2,z34,z4,z5,z6]),(0,[z1,z2,z34,z801,z5,z6]),(0,[z1,z2,z34,z4,z65,z5]),(0,[z571,z2,z55,z4,z5,z6]),(0,[z2,z55,z632,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z45]),(0,[z1,z3,z4,z609,z5,z51]),(0,[z375,z2,z210,z4,z5,z6])],[(0,[z153,z123,z3,z4,z299,z6]),(0,[z1,z2,z3,z4,z802,z5]),(0,[z2,z34,z4,z627,z5,z6]),(0,[z1,z2,z55,z4,z5,z72]),(0,[z1,z2,z3,z4,z5,z295]),(0,[z1,z2,z803,z4,z5,z6])]],
   [[(0,[z1,z2,z55,z4,z5,z804]),(0,[z1,z2,z3,z4,z805,z6]),(0,[z1,z806,z3,z4,z5,z6])],[(0,[z8,z2,z34,z4,z19,z6]),(0,[z1,z2,z34,z410,z5,z6]),(0,[z807,z2,z3,z4,z5,z6]),(0,[z282,z1,z2,z207,z5,z6]),(0,[z1,z83,z2,z3,z5,z63]),(0,[z1,z2,z808,z4,z5,z6])],[(0,[z1,z2,z34,z4,z301,z6]),(0,[z1,z2,z3,z240,z5,z190]),(0,[z1,z809,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z493,z168]),(0,[z1,z2,z3,z4,z5,z810]),(0,[z1,z79,z668,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z811]),(0,[z1,z3,z4,z5,z812,z51]),(0,[z92,z1,z2,z207,z241,z6])],[(0,[z1,z2,z3,z4,z5,z68]),(0,[z1,z2,z268,z4,z87,z6]),(0,[z1,z2,z55,z4,z87,z6]),(0,[z393,z1,z3,z4,z5,z51])],[(0,[z1,z2,z86,z321,z5,z6]),(0,[z1,z2,z3,z4,z813,z6]),(0,[z1,z3,z4,z5,z114,z812]),(0,[z1,z2,z3,z4,z5,z72])],[(0,[z1,z2,z3,z4,z307,z6]),(0,[z1,z814,z3,z4,z5,z6])],[(0,[z1,z2,z815,z4,z5,z6]),(0,[z1,z2,z3,z213,z644,z6]),(0,[z816,z2,z3,z4,z5,z6]),(0,[z817,z2,z3,z4,z5,z6])],[(0,[z2,z439,z34,z205,z5,z6]),(0,[z50,z1,z34,z4,z5,z51]),(0,[z1,z2,z3,z4,z5,z818]),(0,[z1,z2,z3,z4,z819,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z820]),(0,[z2,z34,z205,z10,z5,z6]),(0,[z1,z255,z15,z4,z5,z6]),(0,[z1,z2,z74,z4,z5,z150]),(0,[z1,z2,z631,z410,z5,z6]),(0,[z26,z2,z3,z410,z5,z168]),(0,[z1,z2,z821,z4,z5,z6])],[(0,[z1,z2,z3,z4,z822,z6]),(0,[z1,z2,z3,z212,z19,z6]),(0,[z1,z83,z2,z3,z5,z262])],[(0,[z1,z97,z3,z4,z16,z6]),(0,[z1,z3,z4,z96,z5,z267])],[(0,[z1,z2,z3,z4,z823,z6]),(0,[z1,z2,z3,z321,z299,z6]),(0,[z52,z2,z3,z4,z5,z6]),(0,[z577,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z824]),(0,[z1,z427,z3,z4,z5,z104]),(0,[z825,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z606,z5,z190])],[(0,[z1,z2,z3,z4,z5,z826]),(0,[z1,z200,z3,z4,z5,z6]),(0,[z1,z2,z34,z213,z134,z6]),(0,[z1,z2,z3,z4,z5,z827]),(0,[z1,z127,z478,z4,z5,z6]),(0,[z98,z2,z3,z99,z19,z6]),(0,[z1,z127,z15,z4,z5,z6])],[(0,[z1,z2,z828,z4,z5,z6]),(0,[z1,z2,z829,z4,z5,z6]),(0,[z1,z2,z830,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z831]),(0,[z1,z2,z3,z731,z5,z6]),(0,[z1,z2,z832,z4,z5,z6])],[(0,[z1,z123,z3,z4,z299,z6]),(0,[z1,z200,z3,z4,z5,z45]),(0,[z1,z539,z2,z3,z125,z6]),(0,[z52,z2,z3,z4,z5,z295])],[(0,[z1,z140,z55,z4,z5,z6]),(0,[z1,z226,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z833,z6]),(0,[z1,z2,z3,z834,z5,z6]),(0,[z1,z2,z3,z4,z5,z835]),(0,[z1,z2,z836,z4,z5,z6]),(0,[z1,z837,z3,z4,z5,z6])]],
   [[(0,[z652,z2,z34,z4,z5,z6]),(0,[z489,z2,z34,z4,z5,z6]),(0,[z1,z838,z3,z4,z5,z6]),(0,[z1,z140,z3,z4,z107,z6]),(0,[z1,z3,z4,z5,z467,z51]),(0,[z1,z700,z2,z4,z5,z94])],[(0,[z1,z2,z86,z4,z5,z54]),(0,[z1,z2,z3,z4,z5,z839]),(0,[z2,z34,z4,z663,z5,z6]),(0,[z1,z2,z139,z4,z5,z755])],[(0,[z49,z2,z34,z4,z5,z6]),(0,[z1,z389,z2,z4,z5,z94]),(0,[z1,z2,z3,z4,z840,z6]),(0,[z92,z1,z2,z192,z5,z6]),(0,[z1,z841,z3,z4,z5,z6]),(0,[z1,z2,z139,z4,z5,z563]),(0,[z1,z842,z3,z4,z5,z6])],[(0,[z2,z843,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z844,z6]),(0,[z1,z2,z3,z4,z5,z342]),(0,[z1,z845,z3,z4,z5,z6]),(0,[z1,z2,z43,z721,z5,z6]),(0,[z1,z2,z3,z846,z5,z6])],[(0,[z1,z2,z3,z4,z299,z6]),(0,[z1,z2,z86,z4,z5,z68]),(0,[z1,z2,z3,z4,z847,z6]),(0,[z1,z55,z4,z5,z22,z6]),(0,[z1,z2,z3,z4,z5,z848]),(0,[z1,z2,z3,z849,z5,z6]),(0,[z1,z850,z3,z4,z5,z6])],[(0,[z1,z37,z34,z4,z16,z6]),(0,[z26,z2,z55,z4,z5,z168]),(0,[z1,z200,z74,z4,z5,z6]),(0,[z1,z200,z3,z4,z307,z6]),(0,[z1,z851,z3,z4,z5,z6]),(0,[z1,z2,z3,z99,z5,z420])],[(0,[z1,z2,z34,z4,z178,z6])],[(0,[z1,z2,z3,z438,z5,z54]),(0,[z118,z2,z843,z4,z5,z6]),(0,[z1,z34,z4,z5,z267,z6]),(0,[z347,z2,z34,z4,z5,z6]),(0,[z1,z127,z730,z4,z5,z6]),(0,[z1,z2,z3,z4,z852,z6]),(0,[z1,z3,z4,z5,z853,z6])]],
   [[(0,[z1,z177,z55,z4,z5,z6]),(0,[z1,z730,z15,z4,z5,z6]),(0,[z1,z2,z854,z4,z5,z6]),(0,[z1,z855,z3,z4,z5,z6])],[(0,[z1,z2,z86,z4,z87,z6]),(0,[z1,z2,z856,z4,z5,z6]),(0,[z358,z2,z3,z205,z5,z6]),(0,[z1,z177,z3,z4,z107,z6])],[(0,[z1,z427,z34,z4,z5,z6]),(0,[z1,z2,z185,z4,z301,z6]),(0,[z1,z2,z3,z4,z609,z148]),(0,[z857,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z299,z68]),(0,[z1,z554,z2,z3,z125,z6]),(0,[z1,z2,z3,z4,z710,z6]),(0,[z1,z2,z3,z4,z728,z82])],[(0,[z98,z2,z34,z4,z19,z6]),(0,[z2,z34,z4,z75,z19,z6]),(0,[z603,z2,z34,z4,z5,z6]),(0,[z2,z3,z4,z775,z5,z6]),(0,[z1,z159,z3,z179,z5,z6])],[(0,[z1,z177,z3,z4,z5,z6]),(0,[z124,z1,z2,z207,z5,z6]),(0,[z1,z167,z3,z4,z301,z6]),(0,[z1,z2,z3,z858,z5,z6]),(0,[z1,z2,z3,z859,z5,z6]),(0,[z860,z2,z3,z4,z5,z6]),(0,[z1,z2,z861,z4,z5,z6])],[(0,[z1,z2,z862,z4,z5,z6]),(0,[z153,z739,z3,z4,z5,z6]),(0,[z1,z2,z34,z4,z183,z6]),(0,[z1,z863,z3,z4,z5,z6]),(0,[z27,z2,z3,z4,z5,z864]),(0,[z1,z2,z3,z4,z768,z6]),(0,[z1,z2,z865,z4,z5,z6])],[(0,[z1,z2,z3,z438,z87,z6]),(0,[z1,z2,z34,z4,z5,z866]),(0,[z1,z2,z3,z4,z867,z6]),(0,[z1,z157,z3,z4,z183,z6]),(0,[z1,z83,z2,z3,z5,z761]),(0,[z1,z2,z3,z4,z267,z148])]],
   [[(0,[z117,z2,z55,z205,z5,z6]),(0,[z1,z868,z3,z4,z5,z6]),(0,[z98,z2,z176,z4,z19,z6]),(0,[z1,z37,z3,z4,z16,z233]),(0,[z1,z239,z2,z3,z4,z96])],[(0,[z458,z2,z34,z4,z5,z6]),(0,[z136,z2,z34,z4,z5,z6]),(0,[z8,z2,z14,z4,z126,z6]),(0,[z8,z2,z273,z4,z126,z6]),(0,[z1,z461,z2,z3,z125,z6])],[(0,[z1,z2,z3,z4,z869,z6]),(0,[z1,z870,z34,z4,z5,z6]),(0,[z52,z2,z3,z4,z5,z342])],[(0,[z1,z2,z3,z4,z871,z6]),(0,[z2,z34,z4,z5,z706,z6]),(0,[z1,z2,z3,z4,z5,z872]),(0,[z873,z2,z3,z4,z5,z6]),(0,[z1,z874,z3,z4,z5,z6])],[(0,[z1,z2,z875,z4,z5,z6]),(0,[z1,z2,z3,z4,z876,z6]),(0,[z27,z2,z390,z4,z5,z111]),(0,[z877,z2,z3,z4,z5,z6])],[(0,[z153,z123,z268,z4,z5,z6]),(0,[z1,z2,z3,z878,z5,z6]),(0,[z2,z34,z12,z4,z5,z6]),(0,[z117,z2,z3,z205,z5,z6]),(0,[z8,z2,z3,z4,z126,z6]),(0,[z1,z222,z2,z3,z5,z63]),(0,[z1,z93,z2,z4,z5,z94]),(0,[z1,z216,z2,z3,z4,z96])],[(0,[z23,z115,z32,z4,z5,z6]),(0,[z1,z2,z34,z413,z5,z6]),(0,[z50,z1,z3,z4,z467,z51]),(0,[z879,z2,z3,z4,z5,z6]),(0,[z1,z880,z3,z4,z5,z6]),(0,[z1,z2,z881,z4,z5,z6])],[(0,[z1,z2,z3,z42,z5,z190]),(0,[z1,z2,z882,z4,z5,z6])]],
   [[(0,[z83,z2,z34,z205,z5,z6]),(0,[z1,z2,z3,z4,z5,z883]),(0,[z1,z2,z884,z4,z5,z6])],[(0,[z1,z2,z885,z4,z5,z6]),(0,[z1,z538,z3,z4,z16,z6]),(0,[z2,z34,z4,z5,z33,z6]),(0,[z2,z311,z34,z4,z5,z6]),(0,[z1,z2,z34,z4,z5,z233]),(0,[z1,z886,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z887]),(0,[z1,z2,z176,z4,z5,z420])],[(0,[z1,z2,z3,z888,z5,z6]),(0,[z1,z235,z55,z4,z5,z6]),(0,[z98,z2,z3,z212,z19,z6]),(0,[z1,z2,z3,z4,z5,z889]),(0,[z1,z469,z2,z4,z5,z94]),(0,[z1,z40,z3,z4,z65,z5]),(0,[z1,z890,z3,z4,z5,z6])],[(0,[z1,z2,z55,z179,z5,z6]),(0,[z550,z2,z3,z4,z19,z6]),(0,[z1,z159,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z891,z6]),(0,[z1,z2,z3,z4,z892,z6]),(0,[z1,z2,z3,z4,z728,z148])],[(0,[z158,z1,z2,z4,z547,z6]),(0,[z1,z2,z893,z4,z5,z6]),(0,[z1,z2,z4,z5,z755,z6])],[(0,[z1,z2,z3,z4,z5,z894]),(0,[z1,z739,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z895,z6]),(0,[z1,z2,z3,z410,z5,z6]),(0,[z1,z2,z3,z896,z5,z6]),(0,[z1,z2,z631,z413,z5,z6]),(0,[z897,z2,z3,z4,z5,z6]),(0,[z1,z2,z898,z4,z5,z6])],[(0,[z1,z2,z3,z4,z899,z6]),(0,[z117,z2,z3,z205,z307,z6]),(0,[z1,z2,z900,z4,z5,z6]),(0,[z1,z901,z3,z4,z5,z6]),(0,[z9,z1,z3,z507,z5,z6]),(0,[z1,z2,z3,z4,z902,z5]),(0,[z903,z2,z3,z4,z5,z6]),(0,[z1,z904,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z761])],[(0,[z1,z271,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z72]),(0,[z158,z1,z2,z179,z211,z6]),(0,[z1,z674,z2,z3,z5,z63])]],
   [[(0,[z1,z2,z3,z4,z905,z6]),(0,[z1,z2,z3,z4,z906,z6]),(0,[z1,z130,z55,z100,z5,z6]),(0,[z1,z2,z3,z4,z301,z45]),(0,[z98,z226,z3,z4,z19,z6]),(1,[z1,z3,z4,z16,z264]),(0,[z92,z1,z2,z207,z5,z6]),(0,[z1,z2,z3,z5,z761,z190])],[(0,[z8,z2,z3,z4,z244,z6]),(0,[z1,z2,z3,z119,z5,z45]),(0,[z1,z46,z3,z4,z75,z6]),(0,[z1,z2,z3,z4,z907,z5]),(0,[z1,z2,z4,z5,z94,z755])],[(0,[z1,z2,z908,z4,z5,z6]),(0,[z1,z235,z3,z4,z5,z295]),(0,[z1,z2,z3,z44,z241,z6])],[(0,[z9,z1,z55,z10,z5,z6]),(0,[z1,z2,z909,z4,z5,z6]),(0,[z1,z140,z151,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z910]),(0,[z50,z1,z3,z4,z5,z51]),(0,[z1,z41,z3,z4,z5,z812]),(0,[z92,z1,z2,z207,z5,z295])],[(0,[z124,z2,z3,z205,z5,z6]),(0,[z681,z2,z55,z4,z5,z6]),(0,[z911,z2,z3,z4,z5,z6])],[(0,[z1,z485,z289,z4,z5,z6]),(0,[z117,z200,z3,z205,z5,z6]),(0,[z1,z2,z3,z4,z5,z755]),(1,[z1,z2,z3,z4,z728])],[(0,[z1,z2,z3,z4,z5,z912]),(0,[z1,z2,z34,z4,z493,z6]),(0,[z1,z2,z55,z4,z107,z6]),(0,[z1,z2,z913,z4,z5,z6])],[(0,[z1,z2,z74,z4,z301,z6]),(0,[z1,z2,z44,z721,z5,z6]),(0,[z1,z2,z3,z740,z125,z6])]],
   [[(0,[z2,z34,z4,z106,z5,z6]),(0,[z1,z914,z3,z4,z5,z6]),(0,[z387,z2,z3,z4,z241,z6]),(0,[z1,z40,z3,z213,z134,z6])],[(0,[z254,z1,z3,z4,z5,z51]),(0,[z1,z167,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z915]),(0,[z1,z916,z3,z4,z5,z6]),(0,[z1,z2,z917,z4,z5,z6]),(0,[z26,z2,z151,z4,z5,z168]),(0,[z1,z2,z3,z4,z5,z918]),(0,[z1,z2,z919,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z264]),(0,[z1,z3,z4,z5,z267,z6]),(0,[z920,z2,z3,z4,z5,z6])],[(0,[z1,z2,z268,z4,z5,z6]),(0,[z1,z2,z55,z4,z5,z6]),(0,[z1,z2,z55,z172,z5,z6]),(0,[z1,z2,z3,z4,z921,z6]),(0,[z50,z1,z3,z4,z5,z812]),(0,[z1,z2,z922,z4,z5,z6]),(0,[z1,z188,z3,z4,z5,z114]),(1,[z1,z2,z721,z5,z6])],[(0,[z153,z123,z86,z4,z5,z6]),(0,[z1,z2,z923,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z924]),(0,[z1,z2,z3,z925,z5,z6])],[(0,[z1,z584,z3,z4,z75,z6]),(0,[z1,z177,z151,z4,z5,z6]),(0,[z1,z458,z3,z4,z16,z6]),(0,[z1,z37,z3,z4,z768,z6])],[(0,[z1,z2,z926,z3,z4,z5]),(0,[z239,z2,z34,z4,z19,z6]),(0,[z1,z2,z55,z4,z5,z295]),(0,[z1,z271,z3,z4,z5,z308]),(0,[z98,z271,z3,z4,z19,z6]),(0,[z1,z2,z631,z4,z493,z6])],[(0,[z1,z2,z90,z4,z5,z6]),(0,[z1,z79,z730,z4,z5,z6]),(0,[z158,z1,z2,z4,z211,z6]),(0,[z158,z1,z2,z172,z211,z6])],[(0,[z367,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z927,z6]),(0,[z1,z2,z3,z928,z5,z6]),(0,[z1,z3,z730,z4,z5,z6]),(0,[z1,z2,z3,z172,z5,z6])]],
   [[(0,[z2,z516,z34,z4,z5,z6]),(0,[z1,z389,z2,z4,z5,z260]),(0,[z1,z929,z3,z4,z5,z6]),(0,[z1,z2,z3,z213,z134,z72])],[(0,[z1,z2,z268,z4,z5,z68]),(0,[z153,z123,z3,z438,z5,z6]),(0,[z1,z2,z55,z4,z5,z68]),(0,[z1,z2,z3,z4,z5,z930])],[(0,[z1,z2,z3,z4,z5,z931]),(0,[z1,z2,z3,z4,z5,z150]),(0,[z1,z423,z3,z4,z16,z6]),(0,[z1,z2,z3,z213,z740,z6])],[(0,[z1,z2,z55,z4,z307,z6]),(0,[z1,z2,z55,z4,z5,z308]),(0,[z1,z2,z3,z4,z20,z148]),(0,[z1,z2,z932,z4,z5,z6])],[(0,[z1,z2,z933,z4,z5,z6]),(0,[z209,z123,z3,z4,z5,z6]),(0,[z1,z934,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z714])],[(0,[z1,z2,z3,z935,z5,z6]),(0,[z2,z34,z4,z5,z6,z156]),(0,[z1,z2,z3,z4,z936,z5]),(0,[z1,z140,z3,z410,z5,z6]),(0,[z1,z2,z937,z4,z5,z6])],[(0,[z1,z658,z3,z100,z5,z6]),(0,[z1,z271,z3,z4,z5,z420]),(0,[z1,z235,z3,z4,z5,z342])],[(0,[z573,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z938,z5,z6]),(0,[z1,z2,z90,z4,z5,z308]),(0,[z939,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z940,z5,z6]),(0,[z1,z2,z3,z4,z5,z308]),(0,[z98,z2,z3,z4,z19,z6]),(1,[z1,z3,z4,z467,z51]),(0,[z1,z2,z3,z4,z941,z6]),(0,[z1,z2,z942,z4,z5,z6]),(0,[z943,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z944,z6])],[(0,[z52,z2,z55,z4,z5,z6])],[(0,[z1,z2,z3,z945,z5,z6]),(0,[z1,z40,z34,z4,z5,z6]),(0,[z1,z200,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z946,z6]),(0,[z1,z2,z947,z4,z5,z6])],[(0,[z1,z115,z3,z4,z299,z6]),(0,[z1,z2,z3,z4,z307,z150]),(0,[z1,z2,z3,z4,z5,z948]),(0,[z1,z2,z3,z4,z5,z949]),(0,[z1,z2,z950,z4,z5,z6])],[(0,[z1,z2,z3,z951,z5,z6]),(0,[z952,z2,z3,z4,z5,z6])],[(0,[z118,z2,z34,z4,z5,z6]),(0,[z2,z305,z55,z4,z5,z6]),(0,[z1,z3,z4,z75,z768,z6])],[(0,[z1,z2,z34,z4,z5,z54]),(0,[z1,z2,z953,z4,z5,z6]),(0,[z2,z34,z4,z192,z5,z6]),(0,[z1,z2,z3,z4,z5,z954]),(0,[z1,z177,z3,z410,z5,z6])],[(0,[z2,z34,z4,z19,z125,z6]),(0,[z651,z2,z3,z4,z126,z6]),(0,[z2,z3,z4,z5,z111,z864]),(0,[z1,z2,z955,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z956]),(0,[z158,z337,z2,z4,z211,z6])]],
   [[(0,[z1,z2,z86,z4,z5,z6]),(0,[z616,z115,z3,z4,z5,z6]),(0,[z2,z34,z4,z19,z6,z148]),(0,[z1,z2,z34,z4,z957,z6]),(0,[z622,z2,z34,z4,z5,z6]),(0,[z1,z841,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z958]),(0,[z1,z2,z3,z5,z63,z761])],[(0,[z1,z2,z34,z99,z5,z6]),(0,[z1,z2,z55,z4,z5,z342]),(0,[z1,z167,z185,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z420]),(0,[z1,z41,z3,z4,z5,z460]),(0,[z1,z159,z3,z4,z5,z333]),(0,[z1,z3,z4,z5,z959,z6])],[(0,[z1,z2,z268,z4,z299,z6]),(0,[z1,z2,z55,z4,z299,z6]),(0,[z27,z2,z34,z4,z5,z111]),(0,[z1,z2,z34,z4,z5,z104]),(0,[z2,z55,z221,z4,z5,z6]),(0,[z1,z200,z3,z4,z5,z150]),(0,[z530,z2,z3,z119,z5,z6]),(0,[z618,z2,z3,z4,z126,z6]),(0,[z960,z2,z3,z4,z5,z6]),(0,[z1,z3,z731,z10,z5,z6]),(0,[z1,z961,z3,z4,z5,z6])],[(0,[z52,z2,z4,z207,z5,z6])],[(0,[z1,z2,z34,z4,z962,z5]),(0,[z1,z963,z3,z4,z5,z6]),(0,[z1,z55,z4,z5,z267,z6]),(0,[z1,z3,z4,z16,z148,z51]),(0,[z1,z964,z3,z4,z5,z6]),(0,[z1,z2,z3,z134,z740,z6])],[(0,[z1,z2,z3,z965,z4,z5]),(0,[z17,z2,z34,z4,z5,z6]),(0,[z1,z2,z176,z99,z5,z6]),(0,[z1,z2,z3,z966,z5,z6]),(0,[z1,z2,z3,z5,z761,z6])],[(0,[z1,z2,z3,z438,z5,z6]),(0,[z1,z2,z34,z4,z87,z6]),(0,[z387,z235,z3,z4,z5,z6]),(0,[z158,z1,z427,z4,z211,z6]),(0,[z1,z2,z3,z179,z5,z333]),(0,[z1,z2,z3,z4,z967,z6])],[(0,[z1,z2,z3,z4,z5,z968]),(0,[z2,z34,z205,z5,z125,z6]),(0,[z1,z2,z843,z4,z5,z6]),(0,[z1,z716,z2,z3,z4,z6]),(0,[z117,z2,z3,z205,z301,z6]),(0,[z1,z2,z969,z4,z5,z6]),(0,[z2,z3,z4,z5,z864,z168]),(0,[z1,z2,z970,z4,z5,z6]),(0,[z52,z2,z43,z4,z5,z6]),(0,[z337,z2,z3,z179,z5,z6]),(0,[z1,z971,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z972]),(0,[z1,z132,z2,z4,z5,z592]),(0,[z117,z2,z3,z775,z5,z6]),(0,[z1,z2,z3,z4,z5,z973]),(0,[z1,z46,z3,z4,z768,z6]),(0,[z1,z974,z3,z4,z5,z6]),(0,[z1,z2,z975,z4,z5,z6])],[(0,[z1,z2,z439,z362,z5,z6]),(0,[z1,z2,z3,z4,z5,z976]),(0,[z1,z2,z3,z4,z977,z6]),(0,[z1,z978,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z979,z6])],[(0,[z1,z2,z3,z980,z5,z6]),(0,[z1,z2,z3,z4,z981,z6]),(0,[z110,z2,z3,z4,z19,z6]),(0,[z1,z2,z151,z4,z107,z6])],[(0,[z1,z2,z982,z4,z5,z6]),(0,[z1,z983,z34,z4,z5,z6]),(0,[z1,z2,z43,z583,z5,z6])],[(0,[z1,z2,z3,z984,z5,z6]),(1,[z739,z3,z4,z5,z6]),(0,[z1,z863,z55,z4,z5,z6]),(0,[z1,z175,z2,z55,z125,z6]),(0,[z985,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z812])],[(0,[z1,z2,z3,z438,z5,z68]),(0,[z1,z2,z986,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z987]),(0,[z1,z186,z3,z4,z5,z51]),(0,[z1,z2,z988,z4,z5,z6]),(0,[z1,z2,z3,z4,z96,z728])],[(0,[z1,z2,z151,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z989]),(0,[z1,z2,z3,z4,z990,z6]),(0,[z375,z2,z3,z179,z5,z6])],[(0,[z2,z708,z34,z4,z5,z6]),(0,[z1,z2,z34,z4,z241,z6]),(0,[z325,z1,z2,z4,z211,z6]),(0,[z1,z2,z3,z4,z5,z991]),(0,[z1,z2,z3,z4,z992,z6]),(0,[z1,z2,z3,z62,z317,z5])]],
   [[(0,[z1,z2,z55,z4,z5,z333]),(0,[z217,z2,z3,z119,z5,z6]),(0,[z313,z1,z3,z10,z5,z6]),(0,[z1,z2,z3,z4,z16,z264]),(0,[z1,z157,z3,z4,z241,z6])],[(0,[z337,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z993,z5,z6]),(0,[z1,z2,z4,z710,z211,z6])],[(0,[z1,z2,z3,z4,z994,z6]),(0,[z1,z2,z34,z62,z5,z190]),(0,[z597,z2,z34,z4,z5,z6]),(0,[z1,z157,z34,z4,z5,z6]),(0,[z337,z2,z273,z4,z5,z6]),(0,[z1,z3,z4,z5,z995,z6]),(0,[z1,z2,z996,z4,z5,z6])],[(0,[z23,z739,z3,z4,z5,z6]),(0,[z171,z115,z3,z4,z5,z6]),(0,[z1,z997,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z998,z6])],[(0,[z23,z115,z55,z4,z5,z6]),(0,[z1,z747,z2,z34,z4,z5]),(0,[z461,z2,z34,z4,z5,z6]),(0,[z1,z2,z185,z4,z5,z45]),(0,[z1,z367,z3,z10,z5,z6]),(0,[z158,z1,z2,z4,z211,z333]),(0,[z1,z2,z3,z534,z5,z190])],[(0,[z1,z175,z2,z34,z125,z6]),(0,[z1,z2,z3,z784,z5,z6]),(0,[z1,z2,z55,z4,z82,z148]),(0,[z1,z226,z3,z99,z5,z6]),(0,[z1,z2,z582,z44,z5,z6]),(0,[z1,z2,z3,z4,z5,z333]),(0,[z1,z2,z3,z172,z5,z333])],[(0,[z387,z2,z3,z4,z5,z6]),(0,[z2,z34,z4,z263,z5,z6]),(0,[z337,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z640,z148]),(0,[z337,z2,z3,z172,z5,z6])],[(0,[z1,z2,z3,z4,z789,z6]),(0,[z1,z167,z3,z4,z5,z45])]],
   [[(0,[z1,z2,z3,z999,z5,z6]),(0,[z1,z2,z86,z4,z299,z6]),(0,[z1,z46,z3,z4,z535,z6]),(0,[z26,z2,z34,z4,z5,z168]),(0,[z1,z2,z55,z4,z65,z5]),(0,[z2,z176,z4,z5,z19,z6]),(0,[z1,z79,z144,z4,z5,z6])],[(0,[z23,z115,z3,z4,z5,z6]),(0,[z1,z1000,z3,z4,z5,z6]),(0,[z1,z159,z55,z4,z5,z6]),(0,[z2,z3,z4,z126,z946,z6]),(0,[z387,z2,z3,z4,z5,z295]),(0,[z1001,z2,z3,z4,z5,z6])],[(0,[z1,z140,z3,z413,z5,z6]),(0,[z282,z1,z2,z4,z211,z6]),(0,[z1,z2,z3,z4,z82,z148]),(0,[z1,z2,z3,z4,z728,z6])],[(0,[z1,z2,z1002,z4,z5,z6]),(0,[z2,z34,z4,z283,z5,z6]),(0,[z1,z2,z55,z410,z5,z6]),(0,[z117,z2,z3,z205,z5,z150]),(0,[z1,z2,z3,z4,z126,z308]),(0,[z98,z2,z3,z4,z946,z6]),(0,[z1,z2,z3,z4,z1003,z6]),(0,[z1,z2,z3,z4,z142,z148])],[(0,[z174,z2,z34,z4,z5,z6]),(0,[z1,z2,z55,z4,z301,z6]),(0,[z1,z2,z3,z410,z107,z6]),(0,[z1,z81,z3,z4,z5,z6]),(0,[z1,z97,z3,z4,z5,z51]),(0,[z1,z3,z4,z5,z1004,z6])],[(0,[z1,z2,z3,z1005,z5,z6]),(0,[z327,z2,z34,z4,z5,z6]),(0,[z375,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z801,z5,z6]),(0,[z1,z1006,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1007,z6]),(0,[z1,z2,z3,z4,z65,z5]),(0,[z1,z1008,z3,z4,z5,z6])],[(0,[z1,z2,z3,z438,z299,z6]),(0,[z1,z2,z208,z4,z5,z6]),(0,[z1,z167,z74,z4,z5,z6]),(0,[z1,z2,z3,z413,z5,z111]),(0,[z1,z3,z4,z5,z6,z812]),(0,[z1,z1009,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1010]),(0,[z1,z159,z3,z172,z5,z6])],[(0,[z1,z2,z34,z212,z5,z6]),(0,[z1,z46,z55,z4,z75,z6]),(0,[z26,z2,z631,z4,z5,z168]),(0,[z1011,z2,z3,z4,z5,z6]),(0,[z1,z2,z1012,z4,z5,z6]),(0,[z1,z2,z1013,z4,z5,z6])]],
   [[(0,[z1,z2,z1014,z4,z5,z6]),(0,[z1,z1015,z3,z4,z5,z6]),(0,[z26,z2,z3,z413,z5,z168])],[(0,[z50,z1,z55,z4,z5,z51]),(0,[z1,z2,z3,z4,z301,z6]),(0,[z1,z140,z3,z4,z5,z168]),(0,[z1,z2,z3,z4,z5,z1016])],[(0,[z1,z2,z3,z1017,z5,z6]),(0,[z1,z271,z3,z99,z5,z6]),(0,[z1,z1018,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1019,z6]),(0,[z1,z3,z100,z731,z5,z6]),(0,[z1,z3,z100,z5,z676,z6])],[(0,[z1,z1020,z3,z4,z5,z6]),(0,[z1,z2,z1021,z4,z5,z6]),(0,[z1,z2,z176,z212,z5,z6]),(0,[z1,z2,z3,z4,z19,z308]),(0,[z1,z177,z3,z413,z5,z6]),(0,[z375,z2,z4,z5,z211,z6]),(0,[z1,z2,z1022,z4,z5,z6])],[(0,[z1,z2,z3,z1023,z5,z6]),(0,[z105,z2,z3,z205,z5,z6]),(0,[z2,z3,z4,z946,z19,z6]),(0,[z1,z2,z3,z1024,z5,z6]),(0,[z1,z3,z4,z5,z1025,z6])],[(0,[z1,z226,z34,z4,z5,z6]),(0,[z2,z74,z4,z205,z5,z6]),(0,[z1,z2,z3,z4,z5,z864]),(0,[z1,z2,z3,z4,z5,z761])],[(0,[z1,z2,z3,z4,z1026,z6]),(0,[z1,z2,z55,z213,z134,z6]),(0,[z1,z2,z1027,z4,z5,z6])],[(0,[z1,z2,z439,z44,z5,z6]),(0,[z1,z2,z55,z4,z5,z264]),(0,[z1,z2,z55,z4,z5,z915]),(0,[z1,z1028,z55,z4,z5,z6]),(0,[z1,z1029,z3,z4,z5,z6])]],
   [[(0,[z153,z123,z34,z4,z5,z6]),(0,[z1,z485,z144,z4,z5,z6]),(0,[z1,z2,z3,z4,z467,z51]),(0,[z1,z2,z1030,z4,z5,z6])],[(0,[z1,z553,z3,z4,z16,z6]),(0,[z1,z226,z176,z4,z5,z6]),(0,[z1,z3,z4,z5,z1031,z6]),(0,[z1,z3,z4,z467,z6,z51]),(0,[z1,z3,z213,z134,z22,z6])],[(0,[z1,z2,z1032,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1033]),(0,[z1,z2,z3,z1034,z5,z6]),(0,[z1,z2,z34,z4,z5,z760]),(0,[z1,z93,z2,z4,z5,z592]),(0,[z1,z140,z3,z4,z493,z6]),(0,[z1,z1035,z3,z4,z5,z6]),(0,[z1,z427,z3,z179,z5,z6]),(0,[z1,z1036,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1037,z6]),(0,[z1,z2,z3,z119,z307,z6]),(0,[z1,z2,z3,z213,z134,z6])],[(0,[z1,z2,z24,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1038]),(0,[z2,z34,z4,z5,z328,z6]),(0,[z359,z1,z2,z192,z5,z6]),(0,[z1,z1028,z3,z4,z5,z6]),(0,[z9,z1,z3,z731,z5,z6]),(0,[z1,z130,z3,z731,z5,z6])],[(0,[z515,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z205,z5,z45]),(0,[z1,z1039,z3,z4,z5,z6]),(0,[z1,z2,z3,z1040,z5,z6]),(0,[z1,z1041,z3,z4,z5,z6]),(0,[z1042,z2,z3,z4,z5,z6]),(0,[z387,z2,z3,z4,z5,z342]),(0,[z1,z235,z3,z4,z183,z6])],[(0,[z1,z41,z34,z4,z5,z114]),(0,[z124,z1,z2,z520,z5,z6]),(0,[z1,z2,z3,z4,z493,z111]),(0,[z1,z2,z3,z4,z5,z104])],[(0,[z1,z2,z3,z4,z1043,z6]),(0,[z1,z37,z55,z4,z16,z6]),(0,[z1,z533,z2,z3,z125,z6]),(0,[z1,z2,z3,z4,z5,z1044])]],
   [[(0,[z1,z2,z3,z4,z5,z1045]),(0,[z118,z2,z34,z119,z5,z6]),(0,[z1,z2,z34,z4,z467,z6]),(0,[z1,z2,z55,z4,z5,z150]),(0,[z1,z2,z55,z4,z178,z6]),(0,[z1,z2,z55,z4,z5,z931]),(0,[z26,z2,z3,z4,z493,z168]),(0,[z1,z2,z3,z4,z5,z1046]),(0,[z372,z1,z3,z4,z5,z51])],[(0,[z2,z34,z4,z338,z5,z6]),(0,[z1,z200,z3,z4,z301,z6]),(0,[z1,z2,z3,z4,z1047,z6])],[(0,[z1,z271,z34,z4,z5,z6]),(0,[z118,z2,z74,z4,z5,z6]),(0,[z1,z200,z3,z119,z5,z6])],[(0,[z1,z130,z34,z100,z5,z6]),(0,[z1,z226,z3,z212,z5,z6]),(0,[z1,z177,z3,z4,z493,z6])],[(0,[z1,z2,z34,z321,z5,z6]),(0,[z1,z2,z1048,z4,z5,z6]),(0,[z1,z1049,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1050]),(0,[z1,z427,z55,z4,z5,z6]),(0,[z1,z2,z3,z205,z307,z6]),(0,[z1,z2,z3,z4,z1051,z5]),(0,[z1,z37,z3,z4,z16,z6]),(0,[z1,z239,z2,z3,z4,z182])],[(0,[z1,z2,z3,z4,z5,z1052]),(0,[z2,z34,z4,z5,z19,z6]),(0,[z276,z2,z34,z4,z5,z6]),(0,[z1,z3,z4,z1053,z5,z6]),(0,[z1,z2,z3,z4,z178,z6]),(0,[z92,z1,z235,z207,z5,z6])],[(0,[z1,z2,z3,z4,z87,z54]),(0,[z2,z34,z4,z5,z352,z6]),(0,[z98,z2,z55,z4,z19,z6]),(0,[z1,z2,z3,z695,z125,z6]),(0,[z1,z3,z4,z82,z267,z148])],[(0,[z1,z2,z3,z1054,z5,z6]),(0,[z2,z490,z34,z4,z5,z6]),(0,[z195,z1,z3,z10,z5,z6]),(0,[z2,z3,z4,z5,z946,z6]),(1,[z1,z2,z3,z740,z6])]],
   [[(0,[z1,z1055,z3,z4,z5,z6]),(0,[z1,z255,z101,z4,z5,z6]),(0,[z1,z1056,z34,z4,z5,z6]),(0,[z1,z1057,z3,z4,z5,z6]),(0,[z1,z2,z55,z4,z183,z6]),(0,[z1058,z2,z3,z4,z5,z6]),(0,[z1,z1059,z3,z4,z5,z6]),(0,[z1,z2,z1060,z4,z5,z6])],[(0,[z1,z2,z1061,z4,z5,z6]),(0,[z1,z427,z3,z4,z5,z6]),(0,[z1,z46,z3,z4,z482,z6]),(0,[z1,z427,z3,z172,z5,z6]),(0,[z1,z1062,z3,z4,z5,z6])],[(0,[z98,z2,z90,z4,z19,z6]),(0,[z92,z1,z2,z207,z5,z342]),(0,[z1,z2,z3,z655,z134,z6])],[(0,[z1,z794,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z1063,z6])],[(0,[z1,z2,z3,z494,z5,z190]),(0,[z1,z2,z3,z1064,z5,z6]),(0,[z1,z2,z3,z4,z5,z812]),(0,[z1,z2,z1065,z4,z5,z6]),(0,[z337,z2,z3,z4,z5,z333])],[(0,[z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1066]),(0,[z325,z2,z34,z4,z19,z6]),(0,[z1,z2,z3,z4,z183,z6]),(0,[z1,z2,z3,z213,z65,z134])],[(0,[z1,z2,z3,z4,z1067,z6]),(0,[z1,z2,z3,z4,z5,z866]),(0,[z1,z157,z3,z4,z5,z6]),(0,[z1,z2,z3,z62,z5,z190])],[(0,[z2,z739,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1068,z6]),(0,[z2,z3,z707,z4,z5,z6]),(0,[z1,z2,z34,z4,z5,z45]),(0,[z1,z2,z55,z4,z5,z420]),(0,[z1,z1069,z3,z4,z5,z6]),(0,[z1,z2,z151,z410,z5,z6])]],
   [[(0,[z380,z1,z3,z4,z5,z51]),(0,[z1,z2,z34,z4,z5,z295]),(0,[z1,z2,z55,z413,z5,z6]),(0,[z1,z271,z3,z212,z5,z6]),(0,[z1,z2,z3,z4,z183,z295]),(0,[z1070,z2,z3,z4,z5,z6])],[(0,[z1,z2,z490,z4,z5,z6]),(0,[z1,z870,z3,z4,z5,z6]),(0,[z1,z2,z3,z413,z107,z6]),(0,[z1,z157,z3,z4,z5,z295])],[(0,[z1,z2,z1071,z4,z5,z6]),(0,[z1,z2,z1072,z4,z5,z6]),(0,[z1,z2,z3,z4,z1073,z6])],[(0,[z491,z2,z34,z4,z5,z6]),(0,[z1,z2,z55,z4,z5,z233]),(0,[z1,z3,z4,z5,z1074,z6]),(0,[z1,z2,z90,z4,z5,z420]),(0,[z8,z2,z3,z4,z946,z6]),(0,[z1,z3,z4,z731,z5,z6])],[(0,[z1,z2,z268,z438,z5,z6]),(0,[z1,z2,z55,z438,z5,z6]),(0,[z1,z2,z34,z4,z5,z68]),(0,[z1,z2,z631,z4,z5,z6]),(0,[z98,z2,z3,z4,z19,z308]),(0,[z1,z2,z4,z5,z710,z6])],[(0,[z1,z2,z3,z1075,z5,z6]),(0,[z1,z2,z34,z4,z5,z72]),(0,[z1,z2,z3,z413,z5,z6]),(0,[z1076,z2,z3,z4,z5,z6]),(0,[z337,z159,z3,z4,z5,z6])],[(0,[z1,z2,z34,z4,z307,z6]),(0,[z497,z1,z2,z4,z547,z6]),(0,[z1,z239,z2,z55,z4,z96]),(0,[z573,z2,z3,z4,z126,z6]),(0,[z1077,z2,z3,z4,z5,z6]),(0,[z1,z41,z3,z4,z467,z6]),(0,[z1,z2,z3,z4,z1078,z6]),(0,[z1,z2,z3,z1079,z5,z6]),(0,[z1,z2,z1080,z4,z5,z6])],[(0,[z2,z34,z4,z400,z5,z6]),(0,[z1,z2,z1081,z4,z5,z6]),(0,[z1,z2,z569,z4,z5,z266])]],
   [[(0,[z1,z130,z3,z346,z5,z6]),(0,[z1,z886,z3,z4,z5,z6]),(0,[z1,z1082,z3,z4,z5,z6]),(0,[z1,z366,z2,z3,z4,z96]),(0,[z1,z2,z3,z4,z5,z233]),(0,[z1,z2,z3,z4,z5,z1083])],[(0,[z1,z664,z15,z4,z5,z6]),(0,[z1,z2,z1084,z4,z5,z6]),(0,[z1,z2,z1085,z4,z5,z6])],[(0,[z1,z689,z2,z3,z125,z6]),(0,[z1,z1086,z3,z4,z5,z6]),(0,[z1,z1087,z3,z4,z5,z6])],[(0,[z1,z2,z55,z4,z5,z1088]),(0,[z92,z387,z2,z207,z5,z6]),(0,[z1,z2,z1089,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1090]),(0,[z52,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z1091,z6]),(0,[z1,z2,z3,z4,z5,z1092]),(0,[z52,z2,z3,z4,z183,z6]),(0,[z375,z159,z3,z4,z5,z6])],[(0,[z1,z2,z1093,z4,z5,z6]),(0,[z98,z2,z3,z4,z19,z420]),(0,[z1,z2,z1094,z4,z5,z6]),(0,[z52,z157,z3,z4,z5,z6]),(0,[z1095,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1096,z6]),(0,[z2,z273,z34,z4,z5,z6]),(0,[z1,z1097,z3,z4,z5,z6]),(0,[z1,z2,z3,z1098,z5,z6]),(0,[z1,z3,z4,z5,z1099,z6])],[(0,[z1,z2,z3,z4,z1100,z6]),(0,[z7,z2,z490,z4,z5,z6]),(0,[z1,z2,z1101,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1088]),(0,[z1,z2,z55,z4,z493,z6]),(0,[z1,z144,z730,z4,z5,z6])],[(0,[z1,z226,z3,z4,z5,z6]),(0,[z574,z115,z3,z4,z5,z6]),(0,[z2,z34,z422,z4,z5,z6]),(0,[z1,z2,z3,z735,z5,z6])],[(0,[z1,z2,z390,z4,z5,z6]),(0,[z1,z2,z3,z4,z1102,z6]),(0,[z1,z2,z3,z1103,z5,z6])],[(0,[z1,z2,z3,z1104,z5,z6]),(0,[z1,z2,z3,z1105,z5,z6]),(0,[z555,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z741]),(0,[z1,z742,z3,z4,z5,z6]),(0,[z1,z2,z1106,z4,z5,z6])],[(0,[z1,z2,z1107,z4,z5,z6]),(0,[z1,z744,z3,z4,z5,z6]),(0,[z1,z2,z1108,z4,z5,z6]),(1,[z2,z3,z4,z5,z864]),(0,[z421,z2,z3,z4,z5,z168]),(0,[z1,z2,z1109,z4,z5,z6]),(0,[z1,z2,z3,z4,z183,z342]),(0,[z158,z1,z159,z4,z211,z6])],[(0,[z1,z2,z3,z4,z5,z1110]),(0,[z1,z2,z185,z4,z5,z6]),(0,[z1,z140,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z493,z6]),(0,[z1,z2,z3,z1111,z5,z6]),(0,[z1,z2,z3,z4,z5,z1112])],[(0,[z23,z115,z24,z4,z5,z6]),(0,[z194,z2,z34,z4,z5,z6]),(0,[z2,z34,z100,z205,z5,z6]),(0,[z649,z2,z34,z4,z5,z6]),(0,[z1,z34,z4,z1053,z5,z6]),(0,[z479,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z1113,z6]),(0,[z1,z1114,z3,z4,z5,z6]),(0,[z1,z3,z4,z65,z5,z22])],[(0,[z209,z2,z3,z4,z5,z168]),(0,[z1,z1115,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1116])]],
   [[(0,[z1,z167,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1117]),(0,[z1,z2,z3,z4,z5,z1118]),(0,[z153,z123,z3,z4,z5,z54]),(0,[z21,z2,z34,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1119]),(0,[z1,z2,z3,z1120,z5,z6]),(0,[z1,z2,z3,z4,z5,z1121]),(0,[z1,z46,z3,z4,z121,z6]),(0,[z1,z2,z1122,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1123]),(0,[z1,z3,z4,z635,z16,z6])],[(0,[z1,z2,z86,z438,z5,z6]),(0,[z1,z2,z1124,z4,z5,z6]),(0,[z1,z81,z55,z4,z5,z6]),(0,[z1,z3,z4,z5,z1125,z6]),(0,[z1,z140,z3,z4,z5,z111]),(0,[z1,z41,z3,z4,z5,z114])],[(0,[z375,z2,z55,z4,z5,z6]),(0,[z78,z2,z3,z4,z5,z111]),(0,[z1,z2,z505,z4,z5,z266])],[(0,[z1,z140,z631,z4,z5,z6]),(0,[z26,z140,z3,z4,z5,z168]),(0,[z1,z2,z1126,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1127]),(0,[z1,z2,z43,z44,z5,z6]),(0,[z1,z2,z3,z4,z621,z148])],[(0,[z1,z2,z311,z583,z5,z6]),(0,[z1,z1128,z3,z4,z5,z6]),(1,[z1,z730,z4,z5,z6]),(0,[z158,z375,z2,z4,z211,z6]),(0,[z1,z159,z3,z4,z5,z104])],[(0,[z1,z177,z34,z4,z5,z6]),(0,[z1,z2,z185,z4,z307,z6]),(0,[z110,z2,z3,z205,z5,z6]),(0,[z1,z175,z2,z3,z740,z6]),(0,[z1,z2,z3,z1129,z5,z6])],[(0,[z1,z2,z3,z1130,z5,z6]),(0,[z2,z55,z34,z4,z5,z6]),(0,[z1,z1131,z3,z4,z5,z6]),(0,[z2,z34,z4,z19,z16,z6]),(0,[z1,z3,z4,z5,z6,z1132]),(0,[z1,z2,z3,z4,z5,z1133]),(0,[z1,z427,z3,z4,z5,z333])]],
   [[(0,[z153,z123,z3,z4,z87,z6]),(0,[z530,z2,z34,z4,z5,z6]),(0,[z26,z2,z3,z4,z5,z864]),(0,[z1134,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z409,z148]),(0,[z1,z665,z2,z3,z4,z96]),(0,[z375,z2,z3,z172,z5,z6]),(0,[z337,z427,z3,z4,z5,z6])],[(0,[z1,z167,z3,z4,z307,z6]),(0,[z1,z2,z3,z4,z1135,z6]),(0,[z1,z2,z3,z4,z663,z148])],[(0,[z1136,z2,z3,z4,z5,z6]),(0,[z1137,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1138]),(0,[z1,z2,z3,z179,z5,z104])],[(0,[z1,z2,z3,z4,z1139,z6])],[(0,[z1,z2,z3,z321,z5,z54]),(0,[z1,z1056,z3,z4,z5,z6]),(0,[z1,z2,z151,z413,z5,z6])],[(0,[z1,z2,z3,z4,z1140,z6]),(0,[z371,z2,z34,z4,z5,z6]),(0,[z1,z200,z185,z4,z5,z6]),(0,[z421,z2,z3,z4,z19,z6]),(0,[z1,z177,z631,z4,z5,z6]),(0,[z1,z3,z4,z16,z6,z264]),(0,[z1141,z2,z3,z4,z5,z6])],[(0,[z117,z2,z34,z205,z5,z6]),(0,[z8,z2,z34,z4,z126,z6]),(0,[z1,z2,z3,z4,z782,z6]),(0,[z1,z3,z4,z5,z22,z6]),(0,[z1,z46,z3,z4,z5,z264])],[(0,[z1,z2,z3,z321,z5,z68]),(0,[z1,z123,z3,z4,z5,z54]),(0,[z2,z34,z4,z5,z6,z480]),(0,[z1,z2,z3,z4,z301,z150]),(0,[z1,z2,z3,z351,z134,z6])]],
   [[(0,[z1,z2,z3,z4,z1142,z6])],[(0,[z1,z2,z34,z4,z5,z748]),(0,[z325,z2,z3,z4,z19,z6]),(0,[z2,z3,z4,z5,z6,z864]),(0,[z1,z40,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1143,z6])],[(0,[z1,z2,z1144,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1145]),(0,[z1,z2,z1146,z4,z5,z6])],[(0,[z325,z1,z2,z4,z149,z6]),(0,[z2,z34,z486,z4,z5,z6]),(0,[z1,z2,z55,z99,z5,z6]),(0,[z1,z83,z2,z3,z5,z64]),(0,[z189,z2,z3,z4,z5,z111])],[(0,[z1,z2,z3,z321,z87,z6]),(0,[z186,z2,z34,z4,z5,z6]),(0,[z1,z159,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z1147,z6]),(0,[z27,z2,z55,z4,z5,z111]),(0,[z1,z2,z55,z4,z5,z104]),(1,[z2,z3,z4,z946,z6]),(0,[z50,z1,z3,z4,z178,z51])],[(0,[z1,z2,z3,z4,z5,z54]),(0,[z693,z1,z3,z10,z5,z6]),(0,[z1,z2,z3,z4,z1148,z6]),(0,[z651,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z1149,z5,z6]),(0,[z1,z2,z3,z1150,z5,z6])],[(0,[z1,z2,z34,z4,z895,z6]),(0,[z217,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z212,z126,z6]),(0,[z1,z2,z1151,z4,z5,z6]),(0,[z1,z235,z3,z4,z241,z6]),(0,[z1,z2,z3,z4,z5,z1152]),(0,[z1,z3,z4,z5,z22,z72])],[(0,[z1,z2,z3,z4,z957,z6]),(0,[z1,z2,z3,z4,z5,z1153]),(0,[z2,z3,z775,z205,z5,z6]),(0,[z1,z2,z90,z99,z5,z6]),(0,[z1,z2,z1154,z4,z5,z6])]],
   [[(0,[z618,z2,z34,z4,z5,z6]),(0,[z1,z235,z34,z4,z5,z6]),(0,[z1,z2,z3,z99,z5,z6]),(0,[z1,z2,z1155,z4,z5,z6]),(0,[z158,z1,z2,z4,z211,z104])],[(0,[z2,z293,z34,z4,z19,z6]),(0,[z1,z2,z1156,z4,z5,z6]),(0,[z1,z2,z34,z179,z5,z6]),(0,[z1,z1157,z3,z4,z5,z6]),(0,[z27,z2,z3,z4,z5,z111]),(0,[z1,z37,z3,z4,z16,z264]),(0,[z1,z481,z3,z4,z75,z6]),(0,[z1,z2,z1158,z4,z5,z6]),(0,[z92,z1,z2,z207,z183,z6]),(0,[z1,z2,z721,z207,z5,z6]),(0,[z1,z2,z3,z172,z5,z104]),(0,[z1,z40,z3,z4,z5,z72])],[(0,[z1,z2,z3,z4,z5,z804]),(0,[z1,z46,z34,z4,z75,z6]),(0,[z1,z2,z74,z4,z5,z6]),(0,[z1,z231,z2,z3,z125,z6])],[(0,[z1,z2,z1159,z4,z5,z6]),(0,[z1,z2,z3,z4,z962,z5]),(0,[z1,z2,z1160,z4,z5,z6]),(0,[z1,z2,z1161,z4,z5,z6])],[(0,[z84,z2,z34,z4,z5,z6]),(0,[z1,z1162,z3,z4,z5,z6]),(0,[z1,z2,z74,z4,z5,z45]),(0,[z1,z2,z3,z4,z307,z45]),(0,[z1,z226,z3,z4,z126,z6]),(0,[z1,z2,z151,z4,z493,z6]),(0,[z1,z2,z1163,z4,z5,z6])],[(0,[z1,z2,z3,z4,z87,z6]),(0,[z1,z2,z1164,z4,z5,z6]),(0,[z1,z2,z3,z4,z1165,z6]),(0,[z115,z739,z3,z4,z5,z6]),(0,[z1,z1166,z3,z4,z5,z6]),(0,[z124,z2,z34,z205,z5,z6]),(0,[z1,z3,z4,z768,z5,z6])],[(0,[z1,z2,z1167,z4,z5,z6]),(0,[z1,z2,z1168,z4,z5,z6])],[(0,[z2,z34,z4,z205,z5,z6]),(0,[z1,z2,z102,z4,z5,z6]),(0,[z568,z2,z34,z4,z5,z6]),(0,[z1,z2,z1169,z4,z5,z6]),(0,[z1,z79,z455,z4,z5,z6]),(0,[z1,z2,z3,z721,z5,z6])]],
   [[(0,[z1,z2,z1170,z4,z5,z6]),(0,[z1,z1171,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1172]),(0,[z1,z2,z3,z4,z1173,z6]),(0,[z9,z1,z34,z10,z5,z6]),(0,[z1,z2,z55,z1174,z5,z6]),(0,[z1,z1175,z55,z4,z5,z6]),(0,[z1,z2,z55,z4,z241,z6]),(0,[z1,z271,z176,z4,z5,z6]),(0,[z1,z2,z3,z99,z5,z308])],[(0,[z1,z2,z34,z4,z5,z264]),(0,[z1,z983,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1176,z6])],[(0,[z1,z2,z707,z4,z5,z6]),(0,[z1,z2,z74,z4,z307,z6]),(0,[z1,z2,z1177,z4,z5,z6]),(0,[z1,z239,z2,z3,z4,z565])],[(0,[z1,z2,z3,z4,z87,z68]),(0,[z118,z2,z34,z205,z5,z6]),(0,[z1,z2,z34,z4,z107,z6]),(0,[z1,z2,z55,z62,z5,z190]),(0,[z1,z157,z55,z4,z5,z6]),(0,[z1,z386,z3,z4,z5,z114]),(0,[z1,z2,z3,z172,z211,z6])],[(0,[z1,z2,z3,z4,z5,z1178]),(0,[z2,z457,z55,z4,z5,z6]),(0,[z1,z2,z1179,z4,z5,z6]),(0,[z1,z1180,z3,z4,z5,z6]),(0,[z1,z2,z1181,z4,z5,z6]),(0,[z1,z1182,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1183,z6]),(0,[z165,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z1174,z5,z6]),(0,[z1,z1175,z3,z4,z5,z6]),(0,[z1,z200,z3,z205,z5,z6]),(0,[z117,z2,z185,z205,z5,z6]),(0,[z1,z285,z3,z4,z16,z6]),(0,[z1,z2,z1184,z4,z5,z6]),(0,[z1,z2,z3,z4,z241,z6]),(0,[z1185,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z740,z6]),(0,[z1,z1186,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1187])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 521).take 517) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1038).take 207) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1245)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [521, 517, 207] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 93).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 93).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 184).take 72).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [93, 91, 72] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_46322

theorem PEqualNP.Outside.L_meta_46322 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276809440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4276809440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_46322.solve