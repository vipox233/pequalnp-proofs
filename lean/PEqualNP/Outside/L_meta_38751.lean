import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38751

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4006142144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000090a2a61c71e5#64 ++ 0x2000121454c38e3c#64 ++ 0x9809f3e7ee3cf3e7#64 ++ 0xd3013e7cfdc79e7c#64 : BitVec 256),
   (0x0032458982c1b428#64 ++ 0x400648b130583685#64 ++ 0xf8764d9993c7fc7f#64 ++ 0xbf0ec9b33278ff8f#64 : BitVec 256),
   (0x03858a161c060ad1#64 ++ 0x8070b142c380c15a#64 ++ 0xd7878e1e1c071fff#64 ++ 0x7af0f1c3c380e3ff#64 : BitVec 256),
   (0x0dd80fe01b681f06#64 ++ 0x01bb01fc036d03e0#64 ++ 0xeff80fe01ff81f86#64 ++ 0xfdff01fc03ff03f0#64 : BitVec 256),
   (0x26eff0001db7c000#64 ++ 0x04ddfe0003b6f800#64 ++ 0xaffff0001fffe005#64 ++ 0xf5fffe0003fffc00#64 : BitVec 256),
   (0x177f6f5d40000000#64 ++ 0x02efedeba8000000#64 ++ 0xf7ffffffe0000003#64 ++ 0xfefffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [8, 4]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [7, 12]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x9809f3e7ee3cf3e7 0xd3013e7cfdc79e7c

def z1 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xf8764d9993c7fc7f 0xbf0ec9b33278ff8f

def z2 : W := mkw 0x03850a1418020a10 0x8070a14283004142 0x47860c1810030c18 0x28f0c18302006183

def z3 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xeff80fe01ff81f86 0xfdff01fc03ff03f0

def z4 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xf7ffffffe0000003 0xfefffffffc000000

def z5 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xaffff0001fffe005 0xf5fffe0003fffc00

def z6 : W := mkw 0x27effa161db7cad1 0x84fdff42c3b6f95a 0xfffffe1e1fffffff 0xffffffc3c3ffffff

def z7 : W := mkw 0x000000a2a20831e5 0x200000145441063c 0x100003e7e00013e2 0x0200007cfc00027c

def z8 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xd7878e1e1c071fff 0x7af0f1c3c380e3ff

def z9 : W := mkw 0x09100fe002481f06 0x012201fc004903e0 0x40000fe000001f82 0x080001fc000003f0

def z10 : W := mkw 0x2dfa7fe01bf9df06 0x05bf4ffc037f3be0 0xeff87fe01ff8ff86 0xfdff0ffc03ff1ff0

def z11 : W := mkw 0x09100fe2a2483fe7 0x212201fc544907fc 0x50000fe7e0001fe2 0x0a0001fcfc0003fc

def z12 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x0809b2666e3cf3e4 0x4101364ccdc79e7c

def z13 : W := mkw 0x0010058982403428 0x400200b130480685 0x50000d9980001c7a 0x0a0001b33000038f

def z14 : W := mkw 0x01b24f899ac1be28 0x403649f1335837c5 0xfff64f999fc7ffff 0xfffec9f333f8ffff

def z15 : W := mkw 0x0000900004144000 0x0000120000828800 0x080000000e3ce004 0x0100000001c79c00

def z16 : W := mkw 0x0000900004144000 0x0000120000828800 0x8809f0000e3ce005 0xd1013e0001c79c00

def z17 : W := mkw 0x26eff0a2bfbff1e5 0x24ddfe1457f7fe3c 0xbffff3e7fffff3e7 0xf7fffe7cfffffe7c

def z18 : W := mkw 0x1fff6ffddbe9bf2e 0x43ffedffbb7d37e5 0xffffffffffffffff 0xffffffffffffffff

def z19 : W := mkw 0x1fffefff5f6e1fd7 0x83fffdffebedc3fa 0xffffffffffff1fff 0xffffffffffffe3ff

def z20 : W := mkw 0x2227f0160497c0d1 0x8444fe02c092f81a 0x1007f01e0007e079 0x0200fe03c000fc0f

def z21 : W := mkw 0x00008002040400c1 0x0000100040808018 0x900182060c0413e7 0x52003040c180827c

def z22 : W := mkw 0x03859ab6be1e7bf5 0xa070b356d7c3cf7e 0xdf8ffffffe3fffff 0xfbf1ffffffc7ffff

def z23 : W := mkw 0x0dc80a6019280b06 0x01b9014c03250160 0xaff802601ff80384 0xf5ff004c03ff0070

def z24 : W := mkw 0x2227600000838000 0x0444ec0000107000 0x0006000000030000 0x0000c00000006000

def z25 : W := mkw 0x0032450900000000 0x000648a120000000 0x2070418180000000 0x840e083030000000

def z26 : W := mkw 0x001095a2a65c75e5 0x200212b454cb8ebc 0xf879ffe7fffcffe7 0xff0f3ffcffff9ffc

def z27 : W := mkw 0x0dfa4fe99be9bf2e 0x41bf49fd337d37e5 0xfffe4ff99fffffff 0xffffc9ff33ffffff

def z28 : W := mkw 0x2227f0000497c000 0x0444fe000092f800 0x0007f0000007e001 0x0000fe000000fc00

def z29 : W := mkw 0x02058016040600d1 0x8040b002c080c01a 0x1007801e00070079 0x0200f003c000e00f

def z30 : W := mkw 0x0880000019600e02 0x01100000032c01c0 0x0000000011c00c00 0x0000000002380180

def z31 : W := mkw 0x0fffcfff9fefbfff 0xc1fff9fff3fdf7ff 0xffffcfff9fffffff 0xfffff9fff3ffffff

def z32 : W := mkw 0x002240098081a028 0x4004480130103405 0x100640198007e079 0x0200c8033000fc0f

def z33 : W := mkw 0x26cdb0001d364000 0x04d9b60003a6c800 0x0789b0000c380000 0x40f1360001870000

def z34 : W := mkw 0x02059016a41660f1 0xa040b202d482cc1e 0x1007f01fe007e079 0x0200fe03fc00fc0f

def z35 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x080000000e3cf3e4 0x0100000001c79e7c

def z36 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0x67f60c1800000000 0x2cfec18300000000

def z37 : W := mkw 0x0010050000000000 0x000200a000000000 0xe0700d8000000002 0xbc0e01b000000000

def z38 : W := mkw 0x0000000000000000 0x0000000000000000 0x9009f3e7e0000003 0xd2013e7cfc000000

def z39 : W := mkw 0x0032458982c1b428 0x400648b130583685 0x68760c1813c7fc7c 0x2d0ec1830278ff8f

def z40 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x47860c181c071ffc 0x28f0c1830380e3ff

def z41 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0x2ff9f0000ff8e000 0xc5ff3e0001ff1c00

def z42 : W := mkw 0x0022400000818000 0x0004480000103000 0xa876400013c7e005 0xb50ec8000278fc00

def z43 : W := mkw 0x088000a01b681f06 0x01100014036d03e0 0x080000001ff81f84 0x0100000003ff03f0

def z44 : W := mkw 0x1227601d40000000 0x0244ec03a8000000 0x1007f01fe0000001 0x0200fe03fc000000

def z45 : W := mkw 0x26fff5899ff7f428 0x44dffeb133fefe85 0xfffffd999ffffc7f 0xffffffb333ffff8f

def z46 : W := mkw 0x04c8000019200000 0x0099000003240000 0xaff800001ff80004 0xf5ff000003ff0000

def z47 : W := mkw 0x24eaf0001db7c000 0x049d5e0003b6f800 0x287870001fffe004 0x850f0e0003fffc00

def z48 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xf8764d9983c0e003 0xbf0ec9b330781c00

def z49 : W := mkw 0x066f600000000000 0x00cdec0000000000 0xa7fff00000000001 0xf4fffe0000000000

def z50 : W := mkw 0x246a700001b1c000 0x048d4e0000363800 0x2878700003f8e000 0x850f0e00007f1c00

def z51 : W := mkw 0x000000a002081104 0x0000001400410220 0x880803e00e381386 0xd101007c01c70270

def z52 : W := mkw 0x00009002a41460e1 0x2000120054828c1c 0x1001f007e004e061 0x02003e00fc009c0c

def z53 : W := mkw 0x0032d58ba6d5f4e9 0x60065ab174dabe9d 0xf877fd9ff3c7fc7f 0xbf0effb3fe78ff8f

def z54 : W := mkw 0x0032d58986d5f428 0x40065ab130dabe85 0xf87ffd999ffffc7f 0xff0fffb333ffff8f

def z55 : W := mkw 0x0dc80a6019280b06 0x01b9014c03250160 0x078802600c380380 0x40f1004c01870070

def z56 : W := mkw 0x11100fddc2403428 0x422201fbb8480685 0x50000fffe0001c7a 0x0a0001fffc00038f

def z57 : W := mkw 0x00008002040400c1 0x0000100040808018 0x9009f3e7ec0413e7 0xd2013e7cfd80827c

def z58 : W := mkw 0x0fdd8fe01f6e1f06 0x01fbb1fc03edc3e0 0xefff8fe01fff1f87 0xfdfff1fc03ffe3f0

def z59 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x880803e00e3cf3e6 0xd101007c01c79e7c

def z60 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xf7f64d9980000003 0xbefec9b330000000

def z61 : W := mkw 0x003245aba2c9b5ed 0x600648b5745936bd 0xf8764ffff3c7ffff 0xbf0ec9fffe78ffff

def z62 : W := mkw 0x0c5895e2a77c75e7 0x218b12bc54ef8ebc 0xb879f3e7effcf3e7 0xd70f3e7cfdff9e7c

def z63 : W := mkw 0x0b858ab61f6e1fd7 0x8170b156c3edc3fa 0xdf878e1e1fff1fff 0x7bf0f1c3c3ffe3ff

def z64 : W := mkw 0x1237659dc2c1b428 0x4246ecb3b8583685 0xf877fd9ff3c7fc7f 0xbf0effb3fe78ff8f

def z65 : W := mkw 0x0000000000000000 0x0000000000000000 0xd0060c1810071c7f 0x3a00c1830200e38f

def z66 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0xd80ffffffe3fffff 0xfb01ffffffc7ffff

def z67 : W := mkw 0x002240098081a028 0x4004480130103405 0x000040018000e000 0x0000080030001c00

def z68 : W := mkw 0x00000022200801c5 0x2000000444010038 0x0000026660000380 0x0000004ccc000070

def z69 : W := mkw 0x0032d5aba6ddf5ed 0x60065ab574dbbebd 0xb879f3e7effcf3e7 0xd70f3e7cfdff9e7c

def z70 : W := mkw 0x208090021db7cad1 0x8410120043b6f95a 0x080000001ffffffc 0x0100000003ffffff

def z71 : W := mkw 0x000010a0a2187124 0x2000021414430e24 0x080871e1e238e000 0x81010e3c3c471c00

def z72 : W := mkw 0x27effa141db7ca10 0x84fdff4283b6f942 0xeffffc181fffec1d 0xfdffff8303fffd83

def z73 : W := mkw 0x0032450900000000 0x000648a120000000 0xf0764d9980000003 0xbe0ec9b330000000

def z74 : W := mkw 0x174d2a5440000000 0x02e9a54a88000000 0x0789b26660000000 0x40f1364ccc000000

def z75 : W := mkw 0x0d580fe003681506 0x01ab01fc006d02a0 0xeff80fe003f80002 0xfdff01fc007f0000

def z76 : W := mkw 0x008090a2be1e7bf5 0xa010121457c3cf7e 0x080000001e3ffffc 0x0100000003c7ffff

def z77 : W := mkw 0x0dd80f4019600e02 0x01bb01e8032c01c0 0x67f00c0011c00c00 0x2cfe018002380180

def z78 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xbffff3e7ffffe007 0xf7fffe7cfffffc00

def z79 : W := mkw 0x208090001db7c000 0x0410120003b6f800 0x080000001fffe004 0x0100000003fffc00

def z80 : W := mkw 0x176f6a5d40000000 0x02eded4ba8000000 0x178ff27fe0000001 0x42f1fe4ffc000000

def z81 : W := mkw 0x37ffff5d5db7c000 0x06ffffebabb6f800 0xffffffffffffe007 0xfffffffffffffc00

def z82 : W := mkw 0x11100f5d40000000 0x022201eba8000000 0x50000fffe0000002 0x0a0001fffc000000

def z83 : W := mkw 0x1dd80ffd5b681f06 0x03bb01ffab6d03e0 0xfff80ffffff81f86 0xffff01ffffff03f0

def z84 : W := mkw 0x03850a1418020a10 0x8070a14283004142 0x0780000000000000 0x00f0000000000000

def z85 : W := mkw 0x03058a16040400c1 0x0060b142c0808018 0xd7878e1e0c0413e7 0x7af0f1c3c180827c

def z86 : W := mkw 0x0448000001200000 0x0089000000240000 0x2878000003f80000 0x850f0000007f0000

def z87 : W := mkw 0x008080001c060000 0x001010000380c000 0x000000001c070004 0x000000000380e000

def z88 : W := mkw 0x028580001c060000 0x0050b0000380c000 0x878780001c070005 0x70f0f0000380e000

def z89 : W := mkw 0x147a654940000000 0x028f4ca928000000 0xb079f3e7e0000003 0xd60f3e7cfc000000

def z90 : W := mkw 0x0032458982003020 0x000648b130400604 0xf8764d998204f067 0xbf0ec9b330409e0c

def z91 : W := mkw 0x0fcd8a761d2e0bd7 0x81f9b14ec3a5c17a 0xd78f8e7e1c3f1fff 0x7af1f1cfc387e3ff

def z92 : W := mkw 0x05580fc002401400 0x00ab01f800480280 0xeff80fe013c01c06 0xfdff01fc02780380

def z93 : W := mkw 0x2227f0098497e028 0x4444fe013092fc05 0x1007f0198007e079 0x0200fe033000fc0f

def z94 : W := mkw 0x0b958ff61e4e1fd7 0x8172b1fec3c9c3fa 0xd7878ffe1c071fff 0x7af0f1ffc380e3ff

def z95 : W := mkw 0x174d2a5440000000 0x02e9a54a88000000 0x0780000000000000 0x00f0000000000000

def z96 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xf7f78e1e00000003 0x7efef1c3c0000000

def z97 : W := mkw 0x177fff5d44144000 0x02efffeba8828800 0xffffffffee3ce007 0xfffffffffdc79c00

def z98 : W := mkw 0x1fff6ffd5b681f06 0x03ffedffab6d03e0 0xfffffffffff81f87 0xffffffffffff03f0

def z99 : W := mkw 0x003245098081a028 0x400648a130103405 0xf0764d998007e07b 0xbe0ec9b33000fc0f

def z100 : W := mkw 0x26ef600019a38000 0x04ddec0003347000 0x27f6000011c30000 0x24fec00002386000

def z101 : W := mkw 0x0c5805e003681506 0x018b00bc006d02a0 0x287801e003f80000 0x850f003c007f0000

def z102 : W := mkw 0x0fdd8ff61f6e1fd7 0x81fbb1fec3edc3fa 0xffff8ffe1fff1fff 0xfffff1ffc3ffe3ff

def z103 : W := mkw 0x208090809ff7f428 0x4410121013fefe85 0x080000001ffffc7c 0x0100000003ffff8f

def z104 : W := mkw 0x1fcd2a7459280b06 0x03f9a54e8b250160 0x0789b2666c380380 0x40f1364ccd870070

def z105 : W := mkw 0x0000008082003020 0x0000001010400604 0x980041818204f067 0x9300083030409e0c

def z106 : W := mkw 0x0010050000400400 0x000200a000080080 0x60700c0011c00c00 0x2c0e018002380180

def z107 : W := mkw 0x0dd80f4019600e02 0x01bb01e8032c01c0 0xeff80c001ff80c04 0xfdff018003ff0180

def z108 : W := mkw 0x03b74f1d18c38e18 0xc076e9e3a31871c3 0x67f60c1811c30c18 0x2cfec18302386183

def z109 : W := mkw 0x00009082a61470e1 0x2000121054c28e1c 0x9801f187e204f067 0x93003e30fc409e0c

def z110 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x1009b3e7ec3813e2 0x4201367cfd87027c

def z111 : W := mkw 0x09109fe2a65c7fe7 0x212213fc54cb8ffc 0xd809ffe7ee3cffe7 0xdb013ffcfdc79ffc

def z112 : W := mkw 0x0000008082c1b428 0x4000001010583685 0x0800000003c0e000 0x0100000000781c00

def z113 : W := mkw 0x0458054000000000 0x008b00a800000000 0x207801e000000000 0x840f003c00000000

def z114 : W := mkw 0x0000000000000000 0x0000000000000000 0x1006001800070079 0x0200c0030000e00f

def z115 : W := mkw 0x0000008002401400 0x0000001000480280 0x0800000013c01c04 0x0100000002780380

def z116 : W := mkw 0x028580021c0600c1 0x0050b0004380c018 0x978782061c0713e7 0x72f0f040c380e27c

def z117 : W := mkw 0x0fdd8ff61f6e1fd7 0x81fbb1fec3edc3fa 0xeff98fe61ff81f86 0xfdff31fcc3ff03f0

def z118 : W := mkw 0x177f6f5d40818000 0x02efedeba8103000 0xfffffffff3c7e007 0xfffffffffe78fc00

def z119 : W := mkw 0x00009022241c41c5 0x2000120444838838 0x8809f2666e3ce385 0xd1013e4ccdc79c70

def z120 : W := mkw 0x27cdba161d364ad1 0x84f9b742c3a6c95a 0x0789b2060c380380 0x40f13640c1870070

def z121 : W := mkw 0x05589fe2a61c71e5 0x20ab13fc54c38e3c 0xfff9ffe7ee3cf3e7 0xffff3ffcfdc79e7c

def z122 : W := mkw 0x11100fffe20831e5 0x222201fffc41063c 0x50000fffe00013e2 0x0a0001fffc00027c

def z123 : W := mkw 0x208090a2bfbff1e5 0x2410121457f7fe3c 0x080000001ffff3e4 0x0100000003fffe7c

def z124 : W := mkw 0x0032458982c1b428 0x400648b130583685 0x2870418183c0e000 0x850e083030781c00

def z125 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x078182060c000380 0x40f03040c1800070

def z126 : W := mkw 0x01800a0018000a00 0x0030014003000140 0xd7860e181c071fff 0x7af0c1c30380e3ff

def z127 : W := mkw 0x01800a0018000a00 0x0030014003000140 0xc7800e001c001f86 0x78f001c0038003f0

def z128 : W := mkw 0x26eff0161db7c0d1 0x84ddfe02c3b6f81a 0xbffff01e1fffe07d 0xf7fffe03c3fffc0f

def z129 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x1801f007ee3cf3e5 0x03003e00fdc79e7c

def z130 : W := mkw 0x03058a16040600d1 0x8060b142c080c01a 0xd7878e1e0007007b 0x7af0f1c3c000e00f

def z131 : W := mkw 0x177fffffe6ddf5ed 0x62effffffcdbbebd 0xffffffffffffffff 0xffffffffffffffff

def z132 : W := mkw 0x0000100000104000 0x0000020000020800 0x080870000238e000 0x81010e0000471c00

def z133 : W := mkw 0x04c890001d344000 0x0099120003a68800 0xaff9f0001ffce005 0xf5ff3e0003ff9c00

def z134 : W := mkw 0x0dd89fe2bf7c7fe7 0x21bb13fc57ef8ffc 0xfff9ffe7fffcffe7 0xffff3ffcffff9ffc

def z135 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xf87ffffff3c7fc7f 0xff0ffffffe78ff8f

def z136 : W := mkw 0x177f6fdd42401400 0x02efedfba8480280 0xfffffffff3c01c07 0xfffffffffe780380

def z137 : W := mkw 0x0dc80ae01b681f06 0x01b9015c036d03e0 0x0f8802601ff81f84 0x41f1004c03ff03f0

def z138 : W := mkw 0x0dd80fe99b683f2e 0x41bb01fd336d07e5 0xfff80ff99ff81ffe 0xffff01ff33ff03ff

def z139 : W := mkw 0x167f654940000000 0x02cfeca928000000 0xa7fff1e1e0000001 0xf4fffe3c3c000000

def z140 : W := mkw 0x03050a1400000000 0x0060a14280000000 0x47860c1800000000 0x28f0c18300000000

def z141 : W := mkw 0x088090a2bf7c7fe7 0x2110121457ef8ffc 0x080000001ffcffe4 0x0100000003ff9ffc

def z142 : W := mkw 0x0000000000000000 0x0000000000000000 0x8009f00000000001 0xd0013e0000000000

def z143 : W := mkw 0x11100f5f40000ad1 0x822201ebe800015a 0x50000fffe0001ffa 0x0a0001fffc0003ff

def z144 : W := mkw 0x01808a161c060ad1 0x80301142c380c15a 0x50000e1e1c071ffe 0x0a0001c3c380e3ff

def z145 : W := mkw 0x0032450900c18408 0x400648a120183081 0x60760c1811c30c18 0x2c0ec18302386183

def z146 : W := mkw 0x177f6fddc2c1b428 0x42efedfbb8583685 0xfffffffff3c7fc7f 0xfffffffffe78ff8f

def z147 : W := mkw 0x0032450980c1a428 0x400648a130183485 0x70764c1991c7ec79 0x2e0ec9833238fd8f

def z148 : W := mkw 0x01800a1618000ad1 0x80300142c300015a 0xd7800e1e1c001ffe 0x7af001c3c38003ff

def z149 : W := mkw 0x028580001c060000 0x0050b0000380c000 0x078180000c000000 0x40f0300001800000

def z150 : W := mkw 0x147a654940000000 0x028f4ca928000000 0x207871e1e0000000 0x840f0e3c3c000000

def z151 : W := mkw 0x066ff0a2a61c71e5 0x20cdfe1454c38e3c 0xbffff3e7ee3cf3e7 0xf7fffe7cfdc79e7c

def z152 : W := mkw 0x26eff0021db7c0c1 0x04ddfe0043b6f818 0xbffff2061ffff3e7 0xf7fffe40c3fffe7c

def z153 : W := mkw 0x0fdd0ff41b681f06 0x01fba1fe836d03e0 0xffff8ffe1ff81f87 0xfffff1ffc3ff03f0

def z154 : W := mkw 0x09900fe01b681f06 0x013201fc036d03e0 0x48000fe01ff81f86 0x090001fc03ff03f0

def z155 : W := mkw 0x0d580fe002481f06 0x01ab01fc004903e0 0xe7f80fe000001f82 0xfcff01fc000003f0

def z156 : W := mkw 0x174d2a5440000000 0x02e9a54a88000000 0x9789f3e7e0000003 0xd2f13e7cfc000000

def z157 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x980041818e3cf3e7 0x9300083031c79e7c

def z158 : W := mkw 0x04fa45899be1b428 0x409f48b1337c3685 0xfffe4d999ffffc7f 0xffffc9b333ffff8f

def z159 : W := mkw 0x0000000000000000 0x0000000000000000 0x0009b26660000000 0x4001364ccc000000

def z160 : W := mkw 0x03859ab6be1e7bf5 0xa070b356d7c3cf7e 0xdf878e1e1e3fffff 0x7bf0f1c3c3c7ffff

def z161 : W := mkw 0x03858a141c060000 0x0070b1428380c000 0xd7878e1e1c070007 0x7af0f1c3c380e000

def z162 : W := mkw 0x377f7f5d41b1c000 0x06efefeba8363800 0xffffffffe3f8e003 0xfffffffffc7f1c00

def z163 : W := mkw 0x23859a161db7cad1 0x8470b342c3b6f95a 0xdf878e1e1fffffff 0x7bf0f1c3c3ffffff

def z164 : W := mkw 0x0022400900818008 0x4004480120103001 0x0006001800030018 0x0000c00300006003

def z165 : W := mkw 0x04ea400019a18000 0x009d480003343000 0xaffe40001fffe005 0xf5ffc80003fffc00

def z166 : W := mkw 0x175d2f5d40000000 0x02eba5eba8000000 0x5789bfffe0000002 0x4af137fffc000000

def z167 : W := mkw 0x24ea700019b1c000 0x049d4e0003363800 0xaff870001ff8e004 0xf5ff0e0003ff1c00

def z168 : W := mkw 0x002240808281b020 0x0004481010503604 0xb876418193c7f067 0xb70ec8303278fe0c

def z169 : W := mkw 0x03a7ca161c878ad1 0x8074f942c390f15a 0xfff7ce1e1fc7ffff 0xfffef9c3c3f8ffff

def z170 : W := mkw 0x05580f4000000000 0x00ab01e800000000 0xe7f80fe000000002 0xfcff01fc00000000

def z171 : W := mkw 0x0032d5aba6ddf5ed 0x60065ab574dbbebd 0xf87fffffffffffff 0xff0fffffffffffff

def z172 : W := mkw 0x0000008082c1b428 0x4000001010583685 0x9800418193c7fc7f 0x930008303278ff8f

def z173 : W := mkw 0x09100ff602481fd7 0x812201fec04903fa 0x50000ffe00001ffa 0x0a0001ffc00003ff

def z174 : W := mkw 0x200090000497c000 0x040012000092f800 0x000000000007e000 0x000000000000fc00

def z175 : W := mkw 0x2227f0000497c000 0x0444fe000092f800 0x880ff0000e3fe005 0xd101fe0001c7fc00

def z176 : W := mkw 0x0000008082c1b428 0x4000001010583685 0x0800000013c7fc7c 0x010000000278ff8f

def z177 : W := mkw 0x11324f5d40000000 0x022649eba8000000 0xf0764fffe0000003 0xbe0ec9fffc000000

def z178 : W := mkw 0x0032d5aba6ddf5ed 0x60065ab574dbbebd 0xf8764d999fffffff 0xbf0ec9b333ffffff

def z179 : W := mkw 0x0cc800a01b681f06 0x01990014036d03e0 0xaff800001ff81f84 0xf5ff000003ff03f0

def z180 : W := mkw 0x0000000000000000 0x0000000000000000 0x800803e000000002 0xd001007c00000000

def z181 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0x6ff00c001ff81f84 0x2dfe018003ff03f0

def z182 : W := mkw 0x00009022241c41c5 0x2000120444838838 0x9009f3e7ec380383 0xd2013e7cfd870070

def z183 : W := mkw 0x0dd80fc01b601e02 0x01bb01f8036c03c0 0xeff00d8013c01c06 0xbdfe01b002780380

def z184 : W := mkw 0x066f600000000000 0x00cdec0000000000 0xb7fff3e7e0000003 0xf6fffe7cfc000000

def z185 : W := mkw 0x177f6fddc2403428 0x42efedfbb8480685 0xf7ffffffe0001c7b 0xfefffffffc00038f

def z186 : W := mkw 0x1227e01f440600d1 0x8244fc03e880c01a 0x1007f01fe0070079 0x0200fe03fc00e00f

def z187 : W := mkw 0x36fff5495db7c000 0x06dffea92bb6f800 0xaffff1e1ffffe005 0xf5fffe3c3ffffc00

def z188 : W := mkw 0x0000008082003020 0x0000001010400604 0x1000018180001062 0x020000303000020c

def z189 : W := mkw 0x02058016040600d1 0x8040b002c080c01a 0x9007821e0c0713ff 0x5200f043c180e27f

def z190 : W := mkw 0x01100f9f82403ef9 0xc02201f3f04807df 0x50000f9f80001ffa 0x0a0001f3f00003ff

def z191 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x0809f3e7ee38e380 0xc1013e7cfdc71c70

def z192 : W := mkw 0x0dd80fe09be9bf2e 0x41bb01fc137d37e5 0xeff80fe01ffffffe 0xfdff01fc03ffffff

def z193 : W := mkw 0x008080021c060ad1 0x801010004380c15a 0x000000001c071ffc 0x000000000380e3ff

def z194 : W := mkw 0x03050a1400000000 0x0060a14280000000 0xd7878e1e00000003 0x7af0f1c3c0000000

def z195 : W := mkw 0x01000a1600000ad1 0x80200142c000015a 0x50000e1e00001ffa 0x0a0001c3c00003ff

def z196 : W := mkw 0x00009022241c41c5 0x2000120444838838 0x0009b2666c380380 0x4001364ccd870070

def z197 : W := mkw 0x11000a5440000000 0x0220014a88000000 0x0000026660000000 0x0000004ccc000000

def z198 : W := mkw 0x167f655d40000000 0x02cfecaba8000000 0x307ff1ffe0000001 0x860ffe3ffc000000

def z199 : W := mkw 0x03050a1400000000 0x0060a14280000000 0xd78fffffe0000003 0xfaf1fffffc000000

def z200 : W := mkw 0x03b7cf1f1c060ad1 0x8076f9e3e380c15a 0xf7f7cf9f9c071fff 0xfefef9f3f380e3ff

def z201 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x47878e1e1c030f98 0x68f0f1c3c38061f3

def z202 : W := mkw 0x17ff6f5d58020a10 0x82ffedebab004142 0xf7fffffff0030c1b 0xfefffffffe006183

def z203 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xfffe0ff81fff1fff 0xffffc1ff03ffe3ff

def z204 : W := mkw 0x01800a0018000a00 0x0030014003000140 0x078002000c000380 0x40f0004001800070

def z205 : W := mkw 0x0000008082403428 0x4000001010480685 0x0000000000001c78 0x000000000000038f

def z206 : W := mkw 0x0dd80fe09b683f26 0x01bb01fc136d07e4 0xfff84fe19ffcffe7 0xffff09fc33ff9ffc

def z207 : W := mkw 0x03850a1618020ad1 0x8070a142c300415a 0x57860e1e10031ffa 0x2af0c1c3c20063ff

def z208 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xf7fffffff0071c7f 0xfefffffffe00e38f

def z209 : W := mkw 0x0010058002401400 0x000200b000480280 0x2870018003c00000 0x850e003000780000

def z210 : W := mkw 0x01000a0000000000 0x0020014000000000 0xc7800e0000000002 0x78f001c000000000

def z211 : W := mkw 0x01000a1400000000 0x0020014280000000 0x50000e1e00000002 0x0a0001c3c0000000

def z212 : W := mkw 0x046a600000000000 0x008d4c0000000000 0x2078700000000000 0x840f0e0000000000

def z213 : W := mkw 0x27ef6a1419a38a10 0x84fded4283347142 0x67f60c1811c30c18 0x2cfec18302386183

def z214 : W := mkw 0x00008002040400c1 0x0000100040808018 0x000182060c000380 0x40003040c1800070

def z215 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x57878c1e10070c79 0x2af0f183c200e18f

def z216 : W := mkw 0x05580f4000000000 0x00ab01e800000000 0xf7f9ffe7e0000003 0xfeff3ffcfc000000

def z217 : W := mkw 0x1237651d40000000 0x0246eca3a8000000 0xf077fd9fe0000003 0xbe0effb3fc000000

def z218 : W := mkw 0x0022400000000000 0x0004480000000000 0xa076400000000001 0xb40ec80000000000

def z219 : W := mkw 0x04c800a01b281104 0x0099001403650220 0xaff803e01ff81386 0xf5ff007c03ff0270

def z220 : W := mkw 0x3227f01d4497c000 0x0644fe03a892f800 0x1007f01fe007e001 0x0200fe03fc00fc00

def z221 : W := mkw 0x01800aa01a081b04 0x0030015403410360 0xcf880fe01e381f86 0xf9f101fc03c703f0

def z222 : W := mkw 0x37ffffffffbff1e5 0x26fffffffff7fe3c 0xfffffffffffff3e7 0xfffffffffffffe7c

def z223 : W := mkw 0x03374f1d00000000 0x0066e9e3a0000000 0xf7f7cf9f80000003 0xfefef9f3f0000000

def z224 : W := mkw 0x26ef700019b3c000 0x04ddee0003367800 0x2ffe700013fbe000 0xa5ffce00027f7c00

def z225 : W := mkw 0x1fff6f5d59600e02 0x03ffedebab2c01c0 0xf7fffffff1c00c03 0xfefffffffe380180

def z226 : W := mkw 0x06ef600019200000 0x00ddec0003240000 0xaffff0001ff80005 0xf5fffe0003ff0000

def z227 : W := mkw 0x000010a0a2187124 0x2000021414430e24 0x080000000238e000 0x0100000000471c00

def z228 : W := mkw 0x0000000000000000 0x0000000000000000 0x1001f007e0000001 0x02003e00fc000000

def z229 : W := mkw 0x11100f5d40000000 0x022201eba8000000 0xd009ffffe0000003 0xda013ffffc000000

def z230 : W := mkw 0x17ffef5f5c060ad1 0x82fffdebeb80c15a 0xf7ffffffec000383 0xfefffffffd800070

def z231 : W := mkw 0x157a6f5d40000000 0x02af4deba8000000 0x70787fffe0000002 0x8e0f0ffffc000000

def z232 : W := mkw 0x166f601d40000000 0x02cdec03a8000000 0xb7fff01fe0000001 0xf6fffe03fc000000

def z233 : W := mkw 0x208090a2bfbff1e5 0x2410121457f7fe3c 0x9809f3e7fffff3e7 0xd3013e7cfffffe7c

def z234 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000c0010001c06 0x3800018002000380

def z235 : W := mkw 0x0010058002401400 0x000200b000480280 0x40000d8000001c02 0x080001b000000380

def z236 : W := mkw 0x13150f5d40000000 0x0262a1eba8000000 0xd7878fffe0000003 0x7af0f1fffc000000

def z237 : W := mkw 0x26ef600019a38000 0x04ddec0003347000 0xaff6400013c7e005 0xb5fec8000278fc00

def z238 : W := mkw 0x0000008082003020 0x0000001010400604 0xd8064d999207fc7f 0xbb00c9b33240ff8f

def z239 : W := mkw 0x1205201440000000 0x0240a40288000000 0x0001b00660000000 0x00003600cc000000

def z240 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x980182060e3cf3e7 0x53003040c1c79e7c

def z241 : W := mkw 0x1227601d40000000 0x0244ec03a8000000 0x900ff3ffe0000003 0xd201fe7ffc000000

def z242 : W := mkw 0x0227c01f8487a0f9 0xc044f803f090f41f 0x1007c01f8007e079 0x0200f803f000fc0f

def z243 : W := mkw 0x177f6f5dc081a028 0x42efedebb8103405 0xf7ffffffe007e07b 0xfefffffffc00fc0f

def z244 : W := mkw 0x177fef5f440600d1 0x82effdebe880c01a 0xf7ffffffe007007b 0xfefffffffc00e00f

def z245 : W := mkw 0x000010a2a21871e5 0x2000021454430e3c 0x180873e7e238f3e2 0x83010e7cfc471e7c

def z246 : W := mkw 0x03858a001c060a00 0x0070b1400380c140 0xc7878e001c071f87 0x78f0f1c00380e3f0

def z247 : W := mkw 0x0dd80f6019680f06 0x01bb01ec032d01e0 0x67f80e601df80f80 0x6cff01cc03bf01f0

def z248 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0x27f7f00011c7e001 0x24fefe000238fc00

def z249 : W := mkw 0x2fffffe01fffdf06 0x05fffffc03fffbe0 0xefffffe01fffff87 0xfdfffffc03fffff0

def z250 : W := mkw 0x26eff0a0bfbff124 0x24ddfe1417f7fe24 0xaffff1e1ffffe005 0xf5fffe3c3ffffc00

def z251 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xa876418193c7e005 0xb50ec8303278fc00

def z252 : W := mkw 0x03859a161c164ad1 0x8070b342c382c95a 0xdf8ffe1e1e3fffff 0xfbf1ffc3c3c7ffff

def z253 : W := mkw 0x000000a2a20831e5 0x200000145441063c 0x9009f3e7e00013e3 0xd2013e7cfc00027c

def z254 : W := mkw 0x177fffffe61c71e5 0x22effffffcc38e3c 0xffffffffee3cf3e7 0xfffffffffdc79e7c

def z255 : W := mkw 0x008080021c060ad1 0x801010004380c15a 0x000000000c000380 0x0000000001800070

def z256 : W := mkw 0x0022d00ba495e0e9 0x60045a017492bc1d 0x1007f01fe007e079 0x0200fe03fc00fc0f

def z257 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x978182060c0413e7 0x52f03040c180827c

def z258 : W := mkw 0x03b7cf9f9ec7bef9 0xc076f9f3f3d8f7df 0xfff7cf9f9fc7ffff 0xfffef9f3f3f8ffff

def z259 : W := mkw 0x174d2a5440000000 0x02e9a54a88000000 0xd78fbe7e60000003 0x7af1f7cfcc000000

def z260 : W := mkw 0x0010058982403428 0x400200b130480685 0x0000018180000000 0x0000003030000000

def z261 : W := mkw 0x26cdb0001d364000 0x04d9b60003a6c800 0xaff9b0001ff80004 0xf5ff360003ff0000

def z262 : W := mkw 0x0032d5aba61c71e5 0x20065ab574c38e3c 0xf87fffffee3cf3e7 0xff0ffffffdc79e7c

def z263 : W := mkw 0x0dd80ff61b681fd7 0x81bb01fec36d03fa 0xfff80ffe1ff81ffe 0xffff01ffc3ff03ff

def z264 : W := mkw 0x1f7f6ffd42481f06 0x03efedffa84903e0 0xf7ffffffe0001f83 0xfefffffffc0003f0

def z265 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0x67fe7df9e0000000 0xacffcfbf3c000000

def z266 : W := mkw 0x008080829ec7bef9 0xc010101053d8f7df 0x080000001fc7fffc 0x0100000003f8ffff

def z267 : W := mkw 0x26fff5801ff7d400 0x04dffeb003fefa80 0xeffffd801ffffc07 0xfdffffb003ffff80

def z268 : W := mkw 0x00009002241440c1 0x2000120044828818 0x0001b00660000000 0x00003600cc000000

def z269 : W := mkw 0x0000800004040000 0x0000100000808000 0x800180000c040005 0x5000300001808000

def z270 : W := mkw 0x177f6fffe20831e5 0x22efedfffc41063c 0xf7ffffffe00013e3 0xfefffffffc00027c

def z271 : W := mkw 0x26ff650919e38408 0x44dfeca1233c7081 0x67f60c1811c30c18 0x2cfec18302386183

def z272 : W := mkw 0x04d805801b601400 0x009b00b0036c0280 0xeff80d801ff81c06 0xfdff01b003ff0380

def z273 : W := mkw 0x0000000000000000 0x0000000000000000 0x000871e1e0000000 0x80010e3c3c000000

def z274 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xfff9ffe7fff81f87 0xffff3ffcffff03f0

def z275 : W := mkw 0x26cd200019220000 0x04d9a40003244000 0x0780000000000000 0x00f0000000000000

def z276 : W := mkw 0x0032458982c1b428 0x400648b130583685 0x70760d9991c31c7a 0x2e0ec1b33238638f

def z277 : W := mkw 0x0c7a45e983e9b52e 0x418f48bd307d36a5 0x287841e183f8e000 0x850f083c307f1c00

def z278 : W := mkw 0x080000a003681506 0x01000014006d02a0 0x0800000003f80000 0x01000000007f0000

def z279 : W := mkw 0x04c8000019200000 0x0099000003240000 0x27f0000011c00000 0x24fe000002380000

def z280 : W := mkw 0x003245a982c9b52c 0x400648b5305936a5 0xf87e4ff99fffffff 0xff0fc9ff33ffffff

def z281 : W := mkw 0x0032450900000000 0x000648a120000000 0x60760c1800000000 0x2c0ec18300000000

def z282 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xfffffc181ffffc7f 0xffffff8303ffff8f

def z283 : W := mkw 0x01000a0000000a00 0x0020014000000140 0x40000e0000001f82 0x080001c0000003f0

def z284 : W := mkw 0x37cdba545d364000 0x06f9b74a8ba6c800 0x0789b2666c380000 0x40f1364ccd870000

def z285 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0x27f9f3e7e0000000 0xc4ff3e7cfc000000

def z286 : W := mkw 0x081005e002481506 0x010200bc004902a0 0x000001e000000000 0x0000003c00000000

def z287 : W := mkw 0x0dfa4fe99be9bf2e 0x41bf49fd337d37e5 0xeff84fe19ff8ff86 0xfdff09fc33ff1ff0

def z288 : W := mkw 0x000010a0a2187124 0x2000021414430e24 0x980871e1e23cf067 0x93010e3c3c479e0c

def z289 : W := mkw 0x05d80f4019200000 0x00bb01e803240000 0xeff80fe01ff80006 0xfdff01fc03ff0000

def z290 : W := mkw 0x26eff0a2bfbff1e5 0x24ddfe1457f7fe3c 0xaffff0001ffff3e5 0xf5fffe0003fffe7c

def z291 : W := mkw 0x37ffffdddff7f428 0x46fffffbbbfefe85 0xfffffffffffffc7f 0xffffffffffffff8f

def z292 : W := mkw 0x228590001db7c000 0x0450b20003b6f800 0x8f8780001fffe005 0x71f0f00003fffc00

def z293 : W := mkw 0x0000008082c1b428 0x4000001010583685 0xd8060c1813c7fc7f 0x3b00c1830278ff8f

def z294 : W := mkw 0x2227f002a497e0e1 0x2444fe005492fc1c 0x1007f007e007e061 0x0200fe00fc00fc0c

def z295 : W := mkw 0x0022d0a2a69df1e5 0x20045a1454d3be3c 0xb87ff3e7fffff3e7 0xf70ffe7cfffffe7c

def z296 : W := mkw 0x0fdd8f561d660ed3 0x81fbb1eac3acc1da 0xf7f78e1e1dc71fff 0x7efef1c3c3b8e3ff

def z297 : W := mkw 0x064d200000000000 0x00c9a40000000000 0x0789b00000000000 0x40f1360000000000

def z298 : W := mkw 0x36eff01d5db7c000 0x06ddfe03abb6f800 0xbffff01fffffe005 0xf7fffe03fffffc00

def z299 : W := mkw 0x0010058982403428 0x400200b130480685 0xf8700d9993c01c7e 0xbf0e01b33278038f

def z300 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xd7878e1e0c000383 0x7af0f1c3c1800070

def z301 : W := mkw 0x00008002040400c1 0x0000100040808018 0x1001800600040061 0x02003000c000800c

def z302 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0x2ff803e00ff80380 0xc5ff007c01ff0070

def z303 : W := mkw 0x0dfa4fe91b681f06 0x01bf49fd236d03e0 0xfffe4ff99ff81f87 0xffffc9ff33ff03f0

def z304 : W := mkw 0x202270000091c000 0x04044e0000123800 0x000070000000e000 0x00000e0000001c00

def z305 : W := mkw 0x0032458982c1b428 0x400648b130583685 0x2870418193c7fc7c 0x850e08303278ff8f

def z306 : W := mkw 0x0000008082003020 0x0000001010400604 0x080000000204f064 0x0100000000409e0c

def z307 : W := mkw 0x0c48006001280106 0x0189000c00250020 0x0008006000380000 0x0001000c00070000

def z308 : W := mkw 0x01009ab6a61c7bf5 0xa0201356d4c38f7e 0xd809ffffee3cffff 0xdb013ffffdc79fff

def z309 : W := mkw 0x0010058082c1b428 0x400200b010583685 0xe8700d8013c7fc7e 0xbd0e01b00278ff8f

def z310 : W := mkw 0x17ffef5f5c060ad1 0x82fffdebeb80c15a 0xf7f78e1e1c071fff 0x7efef1c3c380e3ff

def z311 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xc7818e061c001f86 0x78f031c0c38003f0

def z312 : W := mkw 0x080000a002481f06 0x01000014004903e0 0x0000000000001f80 0x00000000000003f0

def z313 : W := mkw 0x0000000000000000 0x0000000000000000 0x9001820600000003 0x52003040c0000000

def z314 : W := mkw 0x05c80a0019200a00 0x00b9014003240140 0xeff80e001ff81f86 0xfdff01c003ff03f0

def z315 : W := mkw 0x0205001400000000 0x0040a00280000000 0x1007801e00000001 0x0200f003c0000000

def z316 : W := mkw 0x077f6f4000000000 0x00efede800000000 0xe7ffffe000000003 0xfcfffffc00000000

def z317 : W := mkw 0x01808a021c060ad1 0x803011404380c15a 0xc7800e001c071ffe 0x78f001c00380e3ff

def z318 : W := mkw 0x03859a16bc166af1 0xa070b342d782cd5e 0xd787fe1ffc07ffff 0x7af0ffc3ff80ffff

def z319 : W := mkw 0x26ef600019a38000 0x04ddec0003347000 0xa7fff00011c30001 0xf4fffe0002386000

def z320 : W := mkw 0x0dd80f6019280b06 0x01bb01ec03250160 0xe7f80fe00c380382 0xfcff01fc01870070

def z321 : W := mkw 0x09100fe002481f06 0x012201fc004903e0 0xc8080fe00e381f86 0xd90101fc01c703f0

def z322 : W := mkw 0x0022400000818000 0x0004480000103000 0x2076000011c30000 0x240ec00002386000

def z323 : W := mkw 0x05d80f4018000a00 0x00bb01e803000140 0xe7f80fe01c001f86 0xfcff01fc038003f0

def z324 : W := mkw 0x008090a2be1e7bf5 0xa010121457c3cf7e 0x9809f3e7fe3fffff 0xd3013e7cffc7ffff

def z325 : W := mkw 0x13958f5f5c060ad1 0x8272b1ebeb80c15a 0xd7878ffffc071fff 0x7af0f1ffff80e3ff

def z326 : W := mkw 0x09000a6000080b06 0x0120014c00010160 0x0000026000000380 0x0000004c00000070

def z327 : W := mkw 0x177f6f5d40c18408 0x42efedeba8183081 0xf7fffffff1c30c1b 0xfefffffffe386183

def z328 : W := mkw 0x17ffef5f5c060ad1 0x82fffdebeb80c15a 0xf7fffffffc071fff 0xfeffffffff80e3ff

def z329 : W := mkw 0x26fff5899ff7f428 0x44dffeb133fefe85 0xaffff1819fffe005 0xf5fffe3033fffc00

def z330 : W := mkw 0x0dc89ae2bf3c7be7 0x21b9135c57e78f7c 0x9f89f3e7ee3cf3e7 0xd3f13e7cfdc79e7c

def z331 : W := mkw 0x177f6f5d40c18408 0x42efedeba8183081 0x67f60c1811c30c18 0x2cfec18302386183

def z332 : W := mkw 0x088080a21f6e1fd7 0x8110101443edc3fa 0x080000001fff1ffc 0x0100000003ffe3ff

def z333 : W := mkw 0x177f6f5f40000ad1 0x82efedebe800015a 0xf7ffffffe0001ffb 0xfefffffffc0003ff

def z334 : W := mkw 0x22a7f0001db7c000 0x0454fe0003b6f800 0x0807f0001fffe005 0x0100fe0003fffc00

def z335 : W := mkw 0x2237f58986d7f428 0x4446feb130dafe85 0xf877fd9993c7fc7f 0xbf0effb33278ff8f

def z336 : W := mkw 0x37ffff5f5db7cad1 0x86ffffebebb6f95a 0xffffffffffffffff 0xffffffffffffffff

def z337 : W := mkw 0x0032450900818000 0x000648a120103000 0xf8764d9993c7e007 0xbf0ec9b33278fc00

def z338 : W := mkw 0x000000a0a2083124 0x2000001414410624 0x000001e1e0000000 0x0000003c3c000000

def z339 : W := mkw 0x2fddbfe01f7e5f06 0x05fbb7fc03efcbe0 0xeff9bfe01ff81f86 0xfdff37fc03ff03f0

def z340 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x180003e7ee3cf3e6 0x0300007cfdc79e7c

def z341 : W := mkw 0x1fdd2ff45b681f06 0x03fba5fe8b6d03e0 0xeff9bfe67ff81f86 0xfdff37fccfff03f0

def z342 : W := mkw 0x176f6a5440000000 0x02eded4a88000000 0xa7fff26660000001 0xf4fffe4ccc000000

def z343 : W := mkw 0x157a6f4940000000 0x02af4de928000000 0xe7f87fe1e0000002 0xfcff0ffc3c000000

def z344 : W := mkw 0x2227f0000497c000 0x0444fe000092f800 0xa877f00013c7e005 0xb50efe000278fc00

def z345 : W := mkw 0x177f7ffde2187124 0x22efefffbc430e24 0xffffffffe238e003 0xfffffffffc471c00

def z346 : W := mkw 0x26eff0809ff7f428 0x44ddfe1013fefe85 0xaffff0001ffffc7d 0xf5fffe0003ffff8f

def z347 : W := mkw 0x00008002040600d1 0x800010004080c01a 0x0000000000070078 0x000000000000e00f

def z348 : W := mkw 0x000080a2a60c31e5 0x2000101454c1863c 0x900183e7ec0413e7 0x5200307cfd80827c

def z349 : W := mkw 0x19100ffd42481f06 0x032201ffa84903e0 0x50000fffe0001f82 0x0a0001fffc0003f0

def z350 : W := mkw 0x26cdb0001d364000 0x04d9b60003a6c800 0x8f89f0000e3ce005 0xd1f13e0001c79c00

def z351 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xd78ffffffc071fff 0xfaf1ffffff80e3ff

def z352 : W := mkw 0x03a7ca1f9c87aaf9 0xc074f943f390f55f 0xd787ce1f9c07ffff 0x7af0f9c3f380ffff

def z353 : W := mkw 0x0010050900000000 0x000200a120000000 0x50000d9980000002 0x0a0001b330000000

def z354 : W := mkw 0x03858ab61e0e1bd5 0x8070b156c3c1c37a 0xdf8f8ffe1e3f1fff 0xfbf1f1ffc3c7e3ff

def z355 : W := mkw 0x0000000000000000 0x0000000000000000 0xd0060c1800000003 0x3a00c18300000000

def z356 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x57818e1e0c001ffa 0x4af031c3c18003ff

def z357 : W := mkw 0x028580161c0600d1 0x8050b002c380c01a 0x9787801e1c07007d 0x72f0f003c380e00f

def z358 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000c1800001c7a 0x0a0001830000038f

def z359 : W := mkw 0x0dd88fe21f6e1fd7 0x81bb11fc43edc3fa 0xeff80fe01fff1ffe 0xfdff01fc03ffe3ff

def z360 : W := mkw 0x0000000000000000 0x0000000000000000 0x880040000204e005 0x9100080000409c00

def z361 : W := mkw 0x0000002000080104 0x0000000400010020 0x000802600c380380 0x4001004c01870070

def z362 : W := mkw 0x00008002040400c1 0x0000100040808018 0xd0078e1e1c071fff 0x7a00f1c3c380e3ff

def z363 : W := mkw 0x0032458902401400 0x000648b120480280 0xf8764d9993c01c07 0xbf0ec9b332780380

def z364 : W := mkw 0x17ff6f5d59200000 0x02ffedebab240000 0xfffffffffff80007 0xffffffffffff0000

def z365 : W := mkw 0x0032450900c18408 0x400648a120183081 0xf0764d9991c30c1b 0xbe0ec9b332386183

def z366 : W := mkw 0x177f6fddc2c1b428 0x42efedfbb8583685 0xffffffffe3c0e003 0xfffffffffc781c00

def z367 : W := mkw 0x247a758983f1f428 0x448f4eb1307e3e85 0xf87e7d9993fffc7f 0xbf0fcfb3327fff8f

def z368 : W := mkw 0x0032458982c1b428 0x400648b130583685 0x68764d9993c3ec18 0xad0ec9b332787d83

def z369 : W := mkw 0x00008002040400c1 0x0000100040808018 0x000000000c0413e4 0x000000000180827c

def z370 : W := mkw 0x26cdb0001db7c000 0x04d9b60003b6f800 0x0f89b0001fffe004 0x41f1360003fffc00

def z371 : W := mkw 0x27cdba161d364ad1 0x84f9b742c3a6c95a 0xd78fbe1e1c3f1fff 0x7af1f7c3c387e3ff

def z372 : W := mkw 0x03859a363c1e4bd5 0xa070b346c783c97a 0x0789b2666c380380 0x40f1364ccd870070

def z373 : W := mkw 0x09100f4000400e02 0x012201e8000801c0 0x40000c0000000c00 0x0800018000000180

def z374 : W := mkw 0x1022600940000000 0x02044c0128000000 0x00007001e0000000 0x00000e003c000000

def z375 : W := mkw 0x2c7a75e003f9d506 0x058f4ebc007f3aa0 0x287871e003f8e000 0x850f0e3c007f1c00

def z376 : W := mkw 0x2205b00004164000 0x0440b6000082c800 0x0001b00000000000 0x0000360000000000

def z377 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0x47880fe00c381f82 0x48f101fc018703f0

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0x800002000c001386 0x5000004001800270

def z379 : W := mkw 0x26fff5091db7c000 0x04dffea123b6f800 0xfffffd999fffe007 0xffffffb333fffc00

def z380 : W := mkw 0x0000908086147020 0x0000121010c28e04 0x9809f1818e3cf067 0xd3013e3031c79e0c

def z381 : W := mkw 0x0032458002c19400 0x000648b000583280 0xe8764d8013c7fc07 0xbd0ec9b00278ff80

def z382 : W := mkw 0x002240098081a028 0x4004480130103405 0xb876401993c7e07d 0xb70ec8033278fc0f

def z383 : W := mkw 0x03050a1400000000 0x0060a14280000000 0xd7878e1e10071c7f 0x7af0f1c3c200e38f

def z384 : W := mkw 0x0032450900000000 0x000648a120000000 0xf0764d9990071c7f 0xbe0ec9b33200e38f

def z385 : W := mkw 0x27effab6bfbffbf5 0xa4fdff56d7f7ff7e 0xffffffffffffffff 0xffffffffffffffff

def z386 : W := mkw 0x03374f9d82c1b428 0x4066e9f3b0583685 0xfff7cf9f93c7fc7f 0xfffef9f3f278ff8f

def z387 : W := mkw 0x177f6ffd42081104 0x02efedffa8410220 0xffffffffee381387 0xfffffffffdc70270

def z388 : W := mkw 0x2fffff401df7ce02 0x05ffffe803bef9c0 0xeffffc001fffec05 0xfdffff8003fffd80

def z389 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0x77f60fffe0000002 0x2efec1fffc000000

def z390 : W := mkw 0x27effa001db7ca00 0x04fdff4003b6f940 0xeffffe001fffff87 0xfdffffc003fffff0

def z391 : W := mkw 0x03859a363c1e4bd5 0xa070b346c783c97a 0xd78fbe7e7c3f1fff 0x7af1f7cfcf87e3ff

def z392 : W := mkw 0x0c5815e0a3787526 0x218b02bc146f0ea4 0x287871e1e3f8e000 0x850f0e3c3c7f1c00

def z393 : W := mkw 0x001095aba65c75ed 0x600212b574cb8ebd 0xd809ffffee3cffff 0xdb013ffffdc79fff

def z394 : W := mkw 0x0032458982c1b428 0x400648b130583685 0x3876419983c7e079 0x870ec8333078fc0f

def z395 : W := mkw 0x0cd805e01b681f06 0x019b00bc036d03e0 0x287801e01ff81f84 0x850f003c03ff03f0

def z396 : W := mkw 0x246af0a2a7bdf1e5 0x248d5e1454f7be3c 0xb879f3e7effcf3e7 0xd70f3e7cfdff9e7c

def z397 : W := mkw 0x27ffff401db7c000 0x04ffffe803b6f800 0xefffffe01fffe007 0xfdfffffc03fffc00

def z398 : W := mkw 0x0000900004144000 0x0000120000828800 0x0001f0000004e001 0x00003e0000009c00

def z399 : W := mkw 0x066f600000000000 0x00cdec0000000000 0x27f6000000000000 0x24fec00000000000

def z400 : W := mkw 0x26eff0021db7cad1 0x84ddfe0043b6f95a 0xaffff0001ffffffd 0xf5fffe0003ffffff

def z401 : W := mkw 0x0022d0000495c000 0x00045a000092b800 0xa87ff0001fffe005 0xf50ffe0003fffc00

def z402 : W := mkw 0x000000a002081104 0x0000001400410220 0x000003e000001382 0x0000007c00000270

def z403 : W := mkw 0x01900f801a401e00 0x003201f0034803c0 0xeff00f801fc01f86 0xfdfe01f003f803f0

def z404 : W := mkw 0x0000102020184104 0x2000020404030820 0x0008306060380000 0x0001060c0c070000

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000418180000003 0x9200083030000000

def z406 : W := mkw 0x028590001c164000 0x0050b2000382c800 0x8f8ff0001e3fe005 0xf1f1fe0003c7fc00

def z407 : W := mkw 0x2448300001304000 0x0489060000260800 0x0008300000380000 0x0001060000070000

def z408 : W := mkw 0x0227600000000000 0x0044ec0000000000 0x0007f00000000001 0x0000fe0000000000

def z409 : W := mkw 0x2dd89fe01fffdf06 0x05bb13fc03fffbe0 0xeff80fe01fffff86 0xfdff01fc03fffff0

def z410 : W := mkw 0x000090a2a6ddf5ed 0x6000121454dbbebd 0x080000001ffffffc 0x0100000003ffffff

def z411 : W := mkw 0x00009022241c41c5 0x2000120444838838 0x9009b2666c3c13e7 0x5201364ccd87827c

def z412 : W := mkw 0x26eff0001d364000 0x04ddfe0003a6c800 0xa7fff0000c380001 0xf4fffe0001870000

def z413 : W := mkw 0x2080000019a38000 0x0410000003347000 0x0000000011c30000 0x0000000002386000

def z414 : W := mkw 0x000000a002081104 0x0000001400410220 0x9809f3e7ee381387 0xd3013e7cfdc70270

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z416 : W := mkw 0x0000000000000000 0x0000000000000000 0x100003e7e0000002 0x0200007cfc000000

def z417 : W := mkw 0x01809aa2be1c7be5 0x2030135457c38f7c 0xdf89ffe7fe3cffe7 0xfbf13ffcffc79ffc

def z418 : W := mkw 0x0032458982c1b428 0x400648b130583685 0x50064d998007fc7b 0x0a00c9b33000ff8f

def z419 : W := mkw 0x028580161c060ad1 0x8050b002c380c15a 0x1007801e1c071ffd 0x0200f003c380e3ff

def z420 : W := mkw 0x0022408082c1b428 0x4004481010583685 0xa876400013c7fc7d 0xb50ec8000278ff8f

def z421 : W := mkw 0x028580021c060ad1 0x8050b0004380c15a 0x878780001c071ffd 0x70f0f0000380e3ff

def z422 : W := mkw 0x0010058002401400 0x000200b000480280 0xe8700d8013c01c06 0xbd0e01b002780380

def z423 : W := mkw 0x02058016040600d1 0x8040b002c080c01a 0xd0078c1e10071c7f 0x3a00f183c200e38f

def z424 : W := mkw 0x11109fffe61c71e5 0x222213fffcc38e3c 0xd809ffffee3cf3e7 0xdb013ffffdc79e7c

def z425 : W := mkw 0x00000016000000d1 0x80000002c000001a 0x1000001e00000078 0x02000003c000000f

def z426 : W := mkw 0x0448000000000000 0x0089000000000000 0xa7f8000000000000 0xf4ff000000000000

def z427 : W := mkw 0x0000000980002028 0x4000000130000405 0x1000001980000078 0x020000033000000f

def z428 : W := mkw 0x0237c59f86c7b4f9 0xc046f8b3f0d8f69f 0xf877cd9f93c7fc7f 0xbf0ef9b3f278ff8f

def z429 : W := mkw 0x067f658982c1b428 0x40cfecb130583685 0xfffffd9993c7fc7f 0xffffffb33278ff8f

def z430 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0x67ffbe7e60000000 0x6cfff7cfcc000000

def z431 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0x27ffb0001dfb0000 0x64fff60003bf6000

def z432 : W := mkw 0x00009002a41460e1 0x2000120054828c1c 0x9009f3e7e004e063 0xd2013e7cfc009c0c

def z433 : W := mkw 0x0080000019200000 0x0010000003240000 0x080000001ff80004 0x0100000003ff0000

def z434 : W := mkw 0x26fff5abbffff5ed 0x64dffeb577fffebd 0xffffffffffffffff 0xffffffffffffffff

def z435 : W := mkw 0x247a758983f1f428 0x448f4eb1307e3e85 0x2878718183f8e000 0x850f0e30307f1c00

def z436 : W := mkw 0x0fdd9ff6bf7e7ff7 0xa1fbb3fed7efcffe 0xffffffffffffffff 0xffffffffffffffff

def z437 : W := mkw 0x0dfa4fe01be99f06 0x01bf49fc037d33e0 0xeffe4fe01fffff87 0xfdffc9fc03fffff0

def z438 : W := mkw 0x03858a969e063af1 0x8070b152d3c0c75e 0xdf87cf9f9e07ffff 0xfbf0f9f3f3c0ffff

def z439 : W := mkw 0x01800a0018000a00 0x0030014003000140 0x47800c0010000c00 0x28f0018002000180

def z440 : W := mkw 0x17cdaa565c060ad1 0x82f9b54acb80c15a 0xd78fbe7e7c071fff 0x7af1f7cfcf80e3ff

def z441 : W := mkw 0x076f6a1400000000 0x00eded4280000000 0xf7fffe1e00000003 0xfeffffc3c0000000

def z442 : W := mkw 0x03850a1418020a10 0x8070a14283004142 0xc7860e181c031f9e 0x78f0c1c3038063f3

def z443 : W := mkw 0x02a7c0001c878000 0x0054f8000390f000 0xaff7c0001fc7e005 0xf5fef80003f8fc00

def z444 : W := mkw 0x067f650900000000 0x00cfeca120000000 0xf7fffd9980000003 0xfeffffb330000000

def z445 : W := mkw 0x1227f01fe41460e1 0x2244fe03fc828c1c 0x1007f01fe004e061 0x0200fe03fc009c0c

def z446 : W := mkw 0x066ff00004144000 0x00cdfe0000828800 0xaffff0000e3ce005 0xf5fffe0001c79c00

def z447 : W := mkw 0x0010058982403428 0x400200b130480685 0xd8004d998204fc7f 0x9b0009b330409f8f

def z448 : W := mkw 0x00009022a41c61e5 0x2000120454838c3c 0x1009f267ec3ce3e1 0x42013e4cfd879c7c

def z449 : W := mkw 0x0000900004144000 0x0000120000828800 0x9809f3e7ee3ce007 0xd3013e7cfdc79c00

def z450 : W := mkw 0x177f6fddc2c1b428 0x42efedfbb8583685 0xfff64d9993c7fc7f 0xbffec9b33278ff8f

def z451 : W := mkw 0x000090a2261c51c5 0x2000121444c38a38 0x8809b3e66e381386 0xd101367ccdc70270

def z452 : W := mkw 0x000000a2a20831e5 0x200000145441063c 0x980043e7e204f3e7 0x9300087cfc409e7c

def z453 : W := mkw 0x0c7a45e983e9b52e 0x418f48bd307d36a5 0xf87e4df993fffc7f 0xbf0fc9bf327fff8f

def z454 : W := mkw 0x00009022241c41c5 0x2000120444838838 0x000000000c380380 0x0000000001870070

def z455 : W := mkw 0x17fffffffe1e7bf5 0xa2ffffffffc3cf7e 0xfffffffffe3fffff 0xffffffffffc7ffff

def z456 : W := mkw 0x03858a141c060a10 0x8070b1428380c142 0xc7878c181c070c1d 0x78f0f1830380e183

def z457 : W := mkw 0x26ff65899be3b428 0x44dfecb1337c7685 0xfff64d9993c7fc7f 0xbffec9b33278ff8f

def z458 : W := mkw 0x0fff6fe01b681f06 0x01ffedfc036d03e0 0xefffffe01ff81f87 0xfdfffffc03ff03f0

def z459 : W := mkw 0x088000a09be9bf2e 0x41100014137d37e5 0x080000001ffffffc 0x0100000003ffffff

def z460 : W := mkw 0x09800aa01b681f06 0x01300154036d03e0 0xcf800e001ff81f86 0x79f001c003ff03f0

def z461 : W := mkw 0x26eff0223dbfc1c5 0x24ddfe0447b7f838 0xaffff2667fffe385 0xf5fffe4ccffffc70

def z462 : W := mkw 0x0c5805e003681506 0x018b00bc006d02a0 0xa87803e00ff81386 0xd50f007c01ff0270

def z463 : W := mkw 0x266ff00005b7c000 0x04cdfe0000b6f800 0x287ff00003ffe001 0x850ffe00007ffc00

def z464 : W := mkw 0x0dfadfebbffdffef 0x61bf5bfd77ffbffd 0xffffffffffffffff 0xffffffffffffffff

def z465 : W := mkw 0x0000000000c18408 0x4000000000183081 0x0000000011c30c18 0x0000000002386183

def z466 : W := mkw 0x147a65c9c2c1b428 0x428f4cb938583685 0x287871e1e3c0e000 0x850f0e3c3c781c00

def z467 : W := mkw 0x3ffffffd5fffdf06 0x07ffffffabfffbe0 0xffffffffffffff87 0xfffffffffffffff0

def z468 : W := mkw 0x23a7fa161c97cad1 0x8474ff42c392f95a 0xd787fe1e1c07ffff 0x7af0ffc3c380ffff

def z469 : W := mkw 0x03b7cf1f1cc78ed9 0xc076f9e3e398f1db 0xf7f78e1e1dc71fff 0x7efef1c3c3b8e3ff

def z470 : W := mkw 0x0000000000000000 0x0000000000000000 0x880800000e380004 0xd101000001c70000

def z471 : W := mkw 0x11100f5d40000000 0x022201eba8000000 0x40000c1800000000 0x0800018300000000

def z472 : W := mkw 0x0022400900000000 0x0004480120000000 0x1006401980000001 0x0200c80330000000

def z473 : W := mkw 0x1fff6f7d59280b06 0x03ffedefab250160 0xf7ffffffec380383 0xfefffffffd870070

def z474 : W := mkw 0x00009002a41460e1 0x2000120054828c1c 0x9001f207ec04f3e7 0x52003e40fd809e7c

def z475 : W := mkw 0x20b2d5899ff7f428 0x44165ab133fefe85 0xf8764d999ffffc7f 0xbf0ec9b333ffff8f

def z476 : W := mkw 0x1fffffffff7c7fe7 0x23ffffffffef8ffc 0xfffffffffffcffe7 0xffffffffffff9ffc

def z477 : W := mkw 0x0880002019280b06 0x0110000403250160 0x000000000c380380 0x0000000001870070

def z478 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000000000041067 0x120000000000820c

def z479 : W := mkw 0x17ffefdfdec7bef9 0xc2fffdfbfbd8f7df 0xffffffffffc7ffff 0xfffffffffff8ffff

def z480 : W := mkw 0x37effa545db7c000 0x06fdff4a8bb6f800 0xaffff2667fffe005 0xf5fffe4ccffffc00

def z481 : W := mkw 0x09900fe01a481f06 0x013201fc034903e0 0xc7800fe01c001f86 0x78f001fc038003f0

def z482 : W := mkw 0x26eff0099db7e028 0x44ddfe0133b6fc05 0xbffff0199fffe07d 0xf7fffe0333fffc0f

def z483 : W := mkw 0x01000a1600000ad1 0x80200142c000015a 0xd0060e1e10071fff 0x3a00c1c3c200e3ff

def z484 : W := mkw 0x09324fe982c9bf2e 0x412649fd305937e5 0xf8764ff993c7ffff 0xbf0ec9ff3278ffff

def z485 : W := mkw 0x0032450900000000 0x000648a120000000 0xf07fffffe0000003 0xfe0ffffffc000000

def z486 : W := mkw 0x20a2d0001db7c000 0x04145a0003b6f800 0xa87640001fffe005 0xb50ec80003fffc00

def z487 : W := mkw 0x0205800004060000 0x0040b0000080c000 0x0007800000070001 0x0000f0000000e000

def z488 : W := mkw 0x0d580fe003681f06 0x01ab01fc006d03e0 0x68780fe003f81f82 0x8d0f01fc007f03f0

def z489 : W := mkw 0x2fcdba601d3e4b06 0x05f9b74c03a7c960 0x0789b2600c380380 0x40f1364c01870070

def z490 : W := mkw 0x002240898281b028 0x4004481130503605 0x980641998207f07f 0x9300c8333040fe0f

def z491 : W := mkw 0x008080021c060ad1 0x801010004380c15a 0x900182061c071fff 0x52003040c380e3ff

def z492 : W := mkw 0x2fff6fe01beb9f06 0x05ffedfc037d73e0 0xeffe0fe01ffb1f86 0xfdffc1fc03ff63f0

def z493 : W := mkw 0x0205000000000000 0x0040a00000000000 0x8787800000000001 0x70f0f00000000000

def z494 : W := mkw 0x01324f9f82c1bef9 0xc02649f3f05837df 0xf8764f9f93c7ffff 0xbf0ec9f3f278ffff

def z495 : W := mkw 0x088090a2bf7c7fe7 0x2110121457ef8ffc 0x9809f3e7fffcffe7 0xd3013e7cffff9ffc

def z496 : W := mkw 0x177f6fddc2003020 0x02efedfbb8400604 0xffffffffe204f067 0xfffffffffc409e0c

def z497 : W := mkw 0x003255a9a2d9f52c 0x60064ab5345b3ea5 0xf87e7df9f3fffc7f 0xbf0fcfbf3e7fff8f

def z498 : W := mkw 0x0032450900c18408 0x400648a120183081 0xf0760c1811c71c7f 0x3e0ec1830238e38f

def z499 : W := mkw 0x27ffff9f9ff7fef9 0xc4fffff3f3feffdf 0xffffff9f9fffffff 0xfffffff3f3ffffff

def z500 : W := mkw 0x0022400000818000 0x0004480000103000 0x000640000007e001 0x0000c8000000fc00

def z501 : W := mkw 0x001005aba24835ed 0x600200b5744906bd 0x50000fffe0001ffa 0x0a0001fffc0003ff

def z502 : W := mkw 0x0022400000818000 0x0004480000103000 0xf8764c1813c7fc7f 0xbf0ec9830278ff8f

def z503 : W := mkw 0x000000a002081104 0x0000001400410220 0x080801e002380000 0x8101003c00470000

def z504 : W := mkw 0x0080000018000a00 0x0010000003000140 0x000000001c001f84 0x00000000038003f0

def z505 : W := mkw 0x147af5ebe61c71e5 0x228f5ebd7cc38e3c 0xb879f3e7ee3cf3e7 0xd70f3e7cfdc79e7c

def z506 : W := mkw 0x1448204040000000 0x0289040808000000 0x0008306060000000 0x0001060c0c000000

def z507 : W := mkw 0x01000a1400000a10 0x8020014280000142 0x40000c1800000c18 0x0800018300000183

def z508 : W := mkw 0x26eff002bdb7e0e1 0x24ddfe0057b6fc1c 0xbffff007ffffe065 0xf7fffe00fffffc0c

def z509 : W := mkw 0x05580fe002081104 0x00ab01fc00410220 0xeff80fe00e381386 0xfdff01fc01c70270

def z510 : W := mkw 0x000080a2060c11c5 0x0000101440c18238 0x980983e60e3c13e7 0xd301307cc1c7827c

def z511 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xb870418183c4f067 0x970e083030789e0c

def z512 : W := mkw 0x24c890001db7c000 0x0499120003b6f800 0xaff800001fffe004 0xf5ff000003fffc00

def z513 : W := mkw 0x208090001db7c000 0x0410120003b6f800 0x8809f0001fffe005 0xd1013e0003fffc00

def z514 : W := mkw 0x0dc80a6019280b06 0x01b9014c03250160 0xc7880e601c381f86 0x78f101cc038703f0

def z515 : W := mkw 0x020590b6a61e71f5 0xa040b216d4c3ce3e 0x980ff3ffee3ff3ff 0xd301fe7ffdc7fe7f

def z516 : W := mkw 0x27effa141db7c000 0x04fdff4283b6f800 0xfffffe1e1fffe007 0xffffffc3c3fffc00

def z517 : W := mkw 0x0000900004144000 0x0000120000828800 0x0009b0000c380000 0x4001360001870000

def z518 : W := mkw 0x0dd80fe2bb683fe7 0x21bb01fc576d07fc 0xfff80fe7fff81fe6 0xffff01fcffff03fc

def z519 : W := mkw 0x0000008002001000 0x0000001000400200 0x8800018002001006 0x9100003000400200

def z520 : W := mkw 0x246af00005b5c000 0x048d5e0000b6b800 0xa879f0000ffce005 0xd50f3e0001ff9c00

def z521 : W := mkw 0x000000a2a20831e5 0x200000145441063c 0x00000000000013e0 0x000000000000027c

def z522 : W := mkw 0x27effa161db7cad1 0x84fdff42c3b6f95a 0xaffff2061fffe385 0xf5fffe40c3fffc70

def z523 : W := mkw 0x208090001d364000 0x0410120003a6c800 0x000000000c380000 0x0000000001870000

def z524 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0x2ff600001fffe004 0x25fec00003fffc00

def z525 : W := mkw 0x05480a4000000000 0x00a9014800000000 0x0788026000000000 0x40f1004c00000000

def z526 : W := mkw 0x0dd88fe21f6c1fc7 0x01bb11fc43ed83f8 0xfff98fe61ffc1fe7 0xffff31fcc3ff83fc

def z527 : W := mkw 0x0c58054001600402 0x018b00a8002c0080 0x2070000001c00000 0x040e000000380000

def z528 : W := mkw 0x0080000018020a10 0x8010000003004142 0x0000000010030c18 0x0000000002006183

def z529 : W := mkw 0x27efea161da78ad1 0x84fdfd42c3b4f15a 0xf7f78e1e1dc71fff 0x7efef1c3c3b8e3ff

def z530 : W := mkw 0x17cdaa565c060ad1 0x82f9b54acb80c15a 0x0789b2666c000380 0x40f1364ccd800070

def z531 : W := mkw 0x03050a1600000ad1 0x8060a142c000015a 0xd7878e1e00001ffb 0x7af0f1c3c00003ff

def z532 : W := mkw 0x03b7dfbfbedffffd 0xe076fbf7f7dbffff 0xffffffffffffffff 0xffffffffffffffff

def z533 : W := mkw 0x37ff6f5d59a38000 0x06ffedebab347000 0xf7fffffff1c30003 0xfefffffffe386000

def z534 : W := mkw 0x0032c58b86c5b4e9 0x400658b170d8b69d 0xf877cf9f9fc7ffff 0xff0ef9f3f3f8ffff

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0x40060c1810030c18 0x2800c18302006183

def z536 : W := mkw 0x177fff7f641c41c5 0x22efffefec838838 0xf7ffffffec380383 0xfefffffffd870070

def z537 : W := mkw 0x0dc80ae01b281b06 0x01b9015c03650360 0x8f8803e00e381386 0xd1f1007c01c70270

def z538 : W := mkw 0x00000002a00020e1 0x200000005400041c 0x10000007e0000060 0x02000000fc00000c

def z539 : W := mkw 0x147a654940000000 0x028f4ca928000000 0x2070000000000000 0x040e000000000000

def z540 : W := mkw 0x2eeff0a01fffdf06 0x05ddfe1403fffbe0 0xaffff0001fffff85 0xf5fffe0003fffff0

def z541 : W := mkw 0x0dc89a623d3c4bc7 0x21b9134c47a78978 0x0789b2666c380380 0x40f1364ccd870070

def z542 : W := mkw 0x0032458902c19408 0x400648b120583281 0xe8760d9813c31c1e 0xbd0ec1b302786383

def z543 : W := mkw 0x147a65c9c2c1b428 0x428f4cb938583685 0xf87e7df9f3c7fc7f 0xbf0fcfbf3e78ff8f

def z544 : W := mkw 0x000090a0a61c7124 0x2000121414c38e24 0x8809f1e1ee3ce005 0xd1013e3c3dc79c00

def z545 : W := mkw 0x2227f0a2a69ff1e5 0x2444fe1454d3fe3c 0x980ff3e7ee3ff3e7 0xd301fe7cfdc7fe7c

def z546 : W := mkw 0x26eff0a01fbfd104 0x04ddfe1403f7fa20 0xaffff3e01ffff387 0xf5fffe7c03fffe70

def z547 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0x078ff0000c3fe001 0x40f1fe000187fc00

def z548 : W := mkw 0x075d0f5400000000 0x00eba1ea80000000 0xf7ff8ffe00000003 0xfefff1ffc0000000

def z549 : W := mkw 0x2efff5e01fffd506 0x05dffebc03fffaa0 0xaffff1e01fffe005 0xf5fffe3c03fffc00

def z550 : W := mkw 0x17ffef5d5c060000 0x02fffdebab80c000 0xf7fffffffc070007 0xfeffffffff80e000

def z551 : W := mkw 0x13a7ea1f5c060ad1 0x8274fd43eb80c15a 0xd787fe1ffc071fff 0x7af0ffc3ff80e3ff

def z552 : W := mkw 0x00009002a41460e1 0x2000120054828c1c 0x000000000004e060 0x0000000000009c0c

def z553 : W := mkw 0x266f700001b1c000 0x04cdee0000363800 0xaffff00003f8e001 0xf5fffe00007f1c00

def z554 : W := mkw 0x246a700001b1c000 0x048d4e0000363800 0xa87e700013ffe005 0xb50fce00027ffc00

def z555 : W := mkw 0x0c5805e003681506 0x018b00bc006d02a0 0xe8780de013f81c06 0xbd0f01bc027f0380

def z556 : W := mkw 0x03858a969ec7bef9 0xc070b152d3d8f7df 0xdf878e1e1fc7ffff 0x7bf0f1c3c3f8ffff

def z557 : W := mkw 0x0010058982403428 0x400200b130480685 0xd0060d9990071c7f 0x3a00c1b33200e38f

def z558 : W := mkw 0x05580f4000000000 0x00ab01e800000000 0x67f00c0000000000 0x2cfe018000000000

def z559 : W := mkw 0x174dbaf6e61c71e5 0x22e9b75edcc38e3c 0x9f89f3e7ee3cf3e7 0xd3f13e7cfdc79e7c

def z560 : W := mkw 0x00008082860430e1 0x0000101050c0861c 0x9801c3878e04f3e7 0xd3003870f1c09e7c

def z561 : W := mkw 0x02058016040600d1 0x8040b002c080c01a 0x0001800600000000 0x00003000c0000000

def z562 : W := mkw 0x1c7a65e943681506 0x038f4cbd286d02a0 0x287871e1e3f80000 0x850f0e3c3c7f0000

def z563 : W := mkw 0x00009002a41460e1 0x2000120054828c1c 0x9809f007ee3ce065 0xd3013e00fdc79c0c

def z564 : W := mkw 0x000000a2a20831e5 0x200000145441063c 0x980803e7ee3813e6 0xd301007cfdc7027c

def z565 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x878782061c070385 0x70f0f040c380e070

def z566 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0x77f7fc1fe0000001 0x2efeff83fc000000

def z567 : W := mkw 0x03850a1418020a10 0x8070a14283004142 0xd7878e1e10030c1b 0x7af0f1c3c2006183

def z568 : W := mkw 0x03958f961e461ed1 0x8072b1f2c3c8c3da 0xfff78f9e1fc71fff 0xfffef1f3c3f8e3ff

def z569 : W := mkw 0x0010058982c1b428 0x400200b130583685 0x58000d9993c7fc7e 0x0b0001b33278ff8f

def z570 : W := mkw 0x03b74f9d9ac3be38 0xc076e9f3b35877c7 0xfff64d9993c7fc7f 0xbffec9b33278ff8f

def z571 : W := mkw 0x26eff0809fb7f020 0x04ddfe1013f6fe04 0xbffff1819ffff067 0xf7fffe3033fffe0c

def z572 : W := mkw 0x246a70a0a3b9f124 0x248d4e1414773e24 0x287871e1e3f8e000 0x850f0e3c3c7f1c00

def z573 : W := mkw 0x0000000000818000 0x0000000000103000 0x0800000013c7e004 0x010000000278fc00

def z574 : W := mkw 0x002240098081a028 0x4004480130103405 0xd0064c199007fc7f 0x3a00c9833200ff8f

def z575 : W := mkw 0x09100fe002481f06 0x012201fc004903e0 0xe8700fe013c01f86 0xbd0e01fc027803f0

def z576 : W := mkw 0x13376f5d40000000 0x0266edeba8000000 0x5007ffffe0000003 0x0a00fffffc000000

def z577 : W := mkw 0x01808a021c040ac1 0x0030114043808158 0xd7818e061c041fe7 0x7af031c0c38083fc

def z578 : W := mkw 0x0dd80f4019600e02 0x01bb01e8032c01c0 0xe7f80fe011c00c02 0xfcff01fc02380180

def z579 : W := mkw 0x37ffff5d5db7c000 0x06ffffebabb6f800 0xeffffc181fffe005 0xfdffff8303fffc00

def z580 : W := mkw 0x03958f9f9e463ef9 0xc072b1f3f3c8c7df 0xd7878f9f9c071fff 0x7af0f1f3f380e3ff

def z581 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x1809f1e7e23ce061 0x83013e3cfc479c0c

def z582 : W := mkw 0x0dc80a4019200a02 0x01b9014803240140 0x0780000000000000 0x00f0000000000000

def z583 : W := mkw 0x174dba76641c41c5 0x22e9b74ecc838838 0x0789b2666c380380 0x40f1364ccd870070

def z584 : W := mkw 0x22a7f0001c97c000 0x0454fe000392f800 0x8787f0001c07e005 0x70f0fe000380fc00

def z585 : W := mkw 0x008080021c060ad1 0x801010004380c15a 0xd0060c181c071fff 0x3a00c1830380e3ff

def z586 : W := mkw 0x0080000018000000 0x0010000003000000 0x878000001c000004 0x70f0000003800000

def z587 : W := mkw 0x000010a0a2187124 0x2000021414430e24 0x9809f3e7e238e003 0xd3013e7cfc471c00

def z588 : W := mkw 0x246a600001a18000 0x048d4c0000343000 0x2070000001c00000 0x040e000000380000

def z589 : W := mkw 0x26cdb0223d3e41c5 0x24d9b60447a7c838 0x0789b2666c380380 0x40f1364ccd870070

def z590 : W := mkw 0x00000002000000c1 0x0000000040000018 0x10000206000013e2 0x02000040c000027c

def z591 : W := mkw 0x0032450900c18408 0x400648a120183081 0xe8764c1813c7ec1d 0xbd0ec9830278fd83

def z592 : W := mkw 0x00b2c58b9ec7bef9 0xc01658b173d8f7df 0xf8764d999fc7ffff 0xbf0ec9b333f8ffff

def z593 : W := mkw 0x07cd8a161d260ad1 0x80f9b142c3a4c15a 0xffff8e1e1fff1fff 0xfffff1c3c3ffe3ff

def z594 : W := mkw 0x26ef600019a38000 0x04ddec0003347000 0xaffe00001ffb0004 0xf5ffc00003ff6000

def z595 : W := mkw 0x0022d0aba69df1ed 0x60045a1574d3be3d 0x980ff3ffee3ff3ff 0xd301fe7ffdc7fe7f

def z596 : W := mkw 0x03059ab6a61c71e5 0x2060b356d4c38e3c 0xdf8fffffee3cf3e7 0xfbf1fffffdc79e7c

def z597 : W := mkw 0x000090a0061c5104 0x0000121400c38a20 0x8809f3e00e3cf387 0xd1013e7c01c79e70

def z598 : W := mkw 0x03858ab6be0e3bf5 0xa070b156d7c1c77e 0xd7878ffffc071fff 0x7af0f1ffff80e3ff

def z599 : W := mkw 0x13276a1d40000000 0x0264ed43a8000000 0xd787fe1fe0000003 0x7af0ffc3fc000000

def z600 : W := mkw 0x01000a1600000ad1 0x80200142c000015a 0x0000020600000380 0x00000040c0000070

def z601 : W := mkw 0x0010050900400408 0x400200a120080081 0x40000c1800000c18 0x0800018300000183

def z602 : W := mkw 0x1227f0bfe61c71e5 0x2244fe17fcc38e3c 0x980ff3ffee3cf3e7 0xd301fe7ffdc79e7c

def z603 : W := mkw 0x0010058082403420 0x000200b010480684 0xf8704d8193c4fc67 0xbf0e09b032789f8c

def z604 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x1787821e0c0703f9 0x42f0f043c180e07f

def z605 : W := mkw 0x0000000200000ad1 0x800000004000015a 0x0000000000001ff8 0x00000000000003ff

def z606 : W := mkw 0x07dd8f561c060ad1 0x80fbb1eac380c15a 0xf7ff8ffe1c071fff 0xfefff1ffc380e3ff

def z607 : W := mkw 0x0000000000000000 0x0000000000000000 0xa870000013c00004 0xb50e000002780000

def z608 : W := mkw 0x003255a9a2d9f52c 0x60064ab5345b3ea5 0x287871e1e3f8e000 0x850f0e3c3c7f1c00

def z609 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xe7fe0ff800000002 0xfcffc1ff00000000

def z610 : W := mkw 0x1f7f6ffd43681506 0x03efedffa86d02a0 0xffffffffe3f80003 0xfffffffffc7f0000

def z611 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xe7fffc1800000001 0xfcffff8300000000

def z612 : W := mkw 0x09100fe982483f2e 0x412201fd304907e5 0x50000ff980001ffa 0x0a0001ff300003ff

def z613 : W := mkw 0x08b245a99be9bf2e 0x411648b5337d37e5 0xf8764d999fffffff 0xbf0ec9b333ffffff

def z614 : W := mkw 0x000090a2a6ddf5ed 0x6000121454dbbebd 0x9809f3e7ffffffff 0xd3013e7cffffffff

def z615 : W := mkw 0x028590a2be1e71e5 0x2050b21457c3ce3c 0x9f8ff3e7fe3ff3e7 0xf3f1fe7cffc7fe7c

def z616 : W := mkw 0x0032458982403428 0x400648b130480685 0xf0764d9980001c7b 0xbe0ec9b33000038f

def z617 : W := mkw 0x177fff5fe41460e1 0x22efffebfc828c1c 0xf7ffffffe004e063 0xfefffffffc009c0c

def z618 : W := mkw 0x06efe0001c060000 0x00ddfc000380c000 0xa7fff0001c070005 0xf4fffe000380e000

def z619 : W := mkw 0x00009002041440c1 0x0000120040828818 0x9809f2060e3cf3e7 0xd3013e40c1c79e7c

def z620 : W := mkw 0x0dd89fe2bf7c7fe7 0x21bb13fc57ef8ffc 0xeff80fe01ffcffe6 0xfdff01fc03ff9ffc

def z621 : W := mkw 0x01100f4000000000 0x002201e800000000 0x40000fe000000002 0x080001fc00000000

def z622 : W := mkw 0x03850a1418020a10 0x8070a14283004142 0xd7860c1810071c7f 0x3af0c1830200e38f

def z623 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x078182061c071ffc 0x40f03040c380e3ff

def z624 : W := mkw 0x288090a01fffdf06 0x0510121403fffbe0 0x080000001fffff84 0x0100000003fffff0

def z625 : W := mkw 0x00001000a0106020 0x2000020014020c04 0x00007001e000e000 0x00000e003c001c00

def z626 : W := mkw 0x01008a1604040ad1 0x80201142c080815a 0xd0018e1e0c041fff 0x5a0031c3c18083ff

def z627 : W := mkw 0x26fff5091df7c408 0x44dffea123bef881 0xeffffc181fffec1d 0xfdffff8303fffd83

def z628 : W := mkw 0x0dd81fe0bb787f26 0x21bb03fc176f0fe4 0xeff87fe1fff8ff86 0xfdff0ffc3fff1ff0

def z629 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0x67f00fe011c01f82 0x2cfe01fc023803f0

def z630 : W := mkw 0x0032458982c1b428 0x400648b130583685 0x78704d9983c0fc7a 0x8f0e09b330781f8f

def z631 : W := mkw 0x0fdd0ff41b6a1f16 0x81fba1fe836d43e2 0xeffe0ff81ffb1f9e 0xfdffc1ff03ff63f3

def z632 : W := mkw 0x0dd89fe01f7c5f06 0x01bb13fc03ef8be0 0xeff9ffe01ffcff87 0xfdff3ffc03ff9ff0

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x8006000010070005 0x3000c0000200e000

def z634 : W := mkw 0x17ff6f5d58000a00 0x02ffedebab000140 0xf7fffffffc001f87 0xfeffffffff8003f0

def z635 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xe8704d8193c0fc06 0xbd0e09b032781f80

def z636 : W := mkw 0x2000100001b1c000 0x0400020000363800 0x0800000003f8e000 0x01000000007f1c00

def z637 : W := mkw 0x1010054940000000 0x020200a928000000 0x000001e1e0000000 0x0000003c3c000000

def z638 : W := mkw 0x377fff5d4497c000 0x06efffeba892f800 0xf7ffffffe007e003 0xfefffffffc00fc00

def z639 : W := mkw 0x0285000018020000 0x0050a00003004000 0x0786000010030000 0x20f0c00002006000

def z640 : W := mkw 0x000000008081a028 0x4000000010103405 0x000000000007e078 0x000000000000fc0f

def z641 : W := mkw 0x0dfa4fc99be1be2a 0x41bf49f9337c37c5 0xfff64d9993c7fc7f 0xbffec9b33278ff8f

def z642 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000010071c7c 0x000000000200e38f

def z643 : W := mkw 0x147a654940000000 0x028f4ca928000000 0xf07e7df9e0000003 0xbe0fcfbf3c000000

def z644 : W := mkw 0x001005a002481504 0x000200b4004902a0 0xe8780fe01ff81f86 0xfd0f01fc03ff03f0

def z645 : W := mkw 0x1227601d40000000 0x0244ec03a8000000 0x0006001800000000 0x0000c00300000000

def z646 : W := mkw 0x1fff6ffd5b681f06 0x03ffedffab6d03e0 0xeffe0ff81ff81f86 0xfdffc1ff03ff03f0

def z647 : W := mkw 0x03859ab6be1e7bf5 0xa070b356d7c3cf7e 0x9f89f3e7ee3cf3e7 0xd3f13e7cfdc79e7c

def z648 : W := mkw 0x17ff6f5d58020a10 0x82ffedebab004142 0x67f60c1810030c18 0x2cfec18302006183

def z649 : W := mkw 0x0fdd0f5419620e12 0x81fba1ea832c41c2 0x67f60c1811c30c18 0x2cfec18302386183

def z650 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x080871e1ee3cf3e4 0x81010e3c3dc79e7c

def z651 : W := mkw 0x2fffffe99fffff2e 0x45fffffd33ffffe5 0xfffffff99fffffff 0xffffffff33ffffff

def z652 : W := mkw 0x04c8000019200000 0x0099000003240000 0x078800000c380000 0x40f1000001870000

def z653 : W := mkw 0x1227601dc081a028 0x4244ec03b8103405 0x1007f01fe007e079 0x0200fe03fc00fc0f

def z654 : W := mkw 0x0032450900c18408 0x400648a120183081 0x2070000001c00000 0x040e000000380000

def z655 : W := mkw 0x000010a0a2187124 0x2000021414430e24 0x880873e1ee38f386 0xd1010e7c3dc71e70

def z656 : W := mkw 0x057a4fc982c1b428 0x40af49f930583685 0xfffe4ff993c7fc7f 0xffffc9ff3278ff8f

def z657 : W := mkw 0x04c890a2bf3c71e5 0x2099121457e78e3c 0xbff9f3e7fffcf3e7 0xf7ff3e7cffff9e7c

def z658 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x1001f3e7e004f3e3 0x02003e7cfc009e7c

def z659 : W := mkw 0x2fff6f4019e38e02 0x05ffede8033c71c0 0x67f60c0011c30c00 0x2cfec18002386180

def z660 : W := mkw 0x347a754941b1c000 0x068f4ea928363800 0x287871e1e3f8e000 0x850f0e3c3c7f1c00

def z661 : W := mkw 0x0dfa4fe91be99f0e 0x41bf49fd237d33e1 0xeffe0ff81ffb1f9e 0xfdffc1ff03ff63f3

def z662 : W := mkw 0x1fff6f5d59600e02 0x03ffedebab2c01c0 0x67f60c1811c00c00 0x2cfec18302380180

def z663 : W := mkw 0x028580001c060000 0x0050b0000380c000 0xd7878c181c071c7f 0x7af0f1830380e38f

def z664 : W := mkw 0x177fef5f440400c1 0x02effdebe8808018 0xf7ffffffec0413e7 0xfefffffffd80827c

def z665 : W := mkw 0x175d2f5440000000 0x02eba5ea88000000 0xe7f9bfe660000002 0xfcff37fccc000000

def z666 : W := mkw 0x0cd805e01b681506 0x019b00bc036d02a0 0xaff801e01ff80004 0xf5ff003c03ff0000

def z667 : W := mkw 0x057a4f4900000000 0x00af49e920000000 0xf7fe4ff980000003 0xfeffc9ff30000000

def z668 : W := mkw 0x0010058002401400 0x000200b000480280 0xf8760d9813c71c7f 0xbf0ec1b30278e38f

def z669 : W := mkw 0x02b7c5899ec7b428 0x4056f8b133d8f685 0xfff7cd999fc7fc7f 0xfffef9b333f8ff8f

def z670 : W := mkw 0x2fffffe2bfffffe7 0x25fffffc57fffffc 0xffffffe7ffffffe7 0xfffffffcfffffffc

def z671 : W := mkw 0x0dfa4f4919e18e0a 0x41bf49e9233c31c1 0x67f60c1811c30c18 0x2cfec18302386183

def z672 : W := mkw 0x0000008082003020 0x0000001010400604 0x9809f3e7e204f067 0xd3013e7cfc409e0c

def z673 : W := mkw 0x37ff6f5d59a38000 0x06ffedebab347000 0x67f60c1811c30000 0x2cfec18302386000

def z674 : W := mkw 0x0000000080002020 0x0000000010000404 0x100040018004e061 0x0200080030009c0c

def z675 : W := mkw 0x088000a01b681f06 0x01100014036d03e0 0x880803e01ff81f86 0xd101007c03ff03f0

def z676 : W := mkw 0x1dfa6fe95b681f06 0x03bf4dfd2b6d03e0 0xeff87fe1fff81f86 0xfdff0ffc3fff03f0

def z677 : W := mkw 0x0dd89fe23f7c5fc7 0x21bb13fc47ef8bf8 0xeff9bfe67ff81f86 0xfdff37fccfff03f0

def z678 : W := mkw 0x2feffa601dbfcb06 0x05fdff4c03b7f960 0xaffff2601fffe385 0xf5fffe4c03fffc70

def z679 : W := mkw 0x03050a1400000000 0x0060a14280000000 0x0781820600000000 0x40f03040c0000000

def z680 : W := mkw 0x03058a1604060ad1 0x8060b142c080c15a 0x50078e1e00071ffb 0x0a00f1c3c000e3ff

def z681 : W := mkw 0x15580f5d40000000 0x02ab01eba8000000 0xf7f80fffe0000002 0xfeff01fffc000000

def z682 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0x6ff80de013f80c00 0xadff01bc027f0180

def z683 : W := mkw 0x147a75e9e2187124 0x228f4ebd3c430e24 0x287871e1e238e000 0x850f0e3c3c471c00

def z684 : W := mkw 0x0022408982c1b428 0x4004481130583685 0x1806401993c7fc7d 0x0300c8033278ff8f

def z685 : W := mkw 0x07efea161c060ad1 0x80fdfd42c380c15a 0xf7fffe1e1c071fff 0xfeffffc3c380e3ff

def z686 : W := mkw 0x0fcd8a761d2e0bd7 0x81f9b14ec3a5c17a 0x078982660c380380 0x40f1304cc1870070

def z687 : W := mkw 0x2ffffff61fffdfd7 0x85fffffec3fffbfa 0xfffffffe1fffffff 0xffffffffc3ffffff

def z688 : W := mkw 0x000000a002081104 0x0000001400410220 0x080000000e381384 0x0100000001c70270

def z689 : W := mkw 0x26cdb0001d364000 0x04d9b60003a6c800 0x878fb0001c3f0005 0x70f1f6000387e000

def z690 : W := mkw 0x0205001400020010 0x8040a00280004002 0x0006001800030018 0x0000c00300006003

def z691 : W := mkw 0x0022400000818000 0x0004480000103000 0x2870400003c0e000 0x850e080000781c00

def z692 : W := mkw 0x066f600000818000 0x00cdec0000103000 0xaffff00013c7e005 0xf5fffe000278fc00

def z693 : W := mkw 0x06cd80001d260000 0x00d9b00003a4c000 0xafff80001fff0005 0xf5fff00003ffe000

def z694 : W := mkw 0x01000ab6a2083bf5 0xa0200156d441077e 0x50000fffe0001ffa 0x0a0001fffc0003ff

def z695 : W := mkw 0x26efe0001da78000 0x04ddfc0003b4f000 0xa7f780001dc70005 0x74fef00003b8e000

def z696 : W := mkw 0x000000a082083124 0x0000001410410624 0x980843e18e3cf3e7 0xd301087c31c79e7c

def z697 : W := mkw 0x37ffff5d5d364000 0x06ffffebaba6c800 0xf7ffffffec380003 0xfefffffffd870000

def z698 : W := mkw 0x03850a1418000a00 0x0070a14283000140 0xd7878e1e1c001f87 0x7af0f1c3c38003f0

def z699 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x8809f0000e3cf3e5 0xd1013e0001c79e7c

def z700 : W := mkw 0x11324fddc2c1b428 0x422649fbb8583685 0xf8764ffff3c7fc7f 0xbf0ec9fffe78ff8f

def z701 : W := mkw 0x26cdb0a2bf3e71e5 0x24d9b61457e7ce3c 0x9f89f3e7ee3cf3e7 0xd3f13e7cfdc79e7c

def z702 : W := mkw 0x0000008082003020 0x0000001010400604 0x080041818200e000 0x8100083030401c00

def z703 : W := mkw 0x0dd80f4019600e02 0x01bb01e8032c01c0 0xe7f00e001dc01f86 0x7cfe01c003b803f0

def z704 : W := mkw 0x089005a01b681f06 0x011200b4036d03e0 0xe8700d801ff81f86 0xbd0e01b003ff03f0

def z705 : W := mkw 0x266ff0000497c000 0x04cdfe000092f800 0xa7fff0000007e001 0xf4fffe000000fc00

def z706 : W := mkw 0x1000001d40000000 0x02000003a8000000 0x1000001fe0000000 0x02000003fc000000

def z707 : W := mkw 0x1f7f6f5d41600402 0x03efedeba82c0080 0xf7ffffffe1c00003 0xfefffffffc380000

def z708 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xc7878c181c071ffd 0x78f0f1830380e3ff

def z709 : W := mkw 0x000000a082083124 0x0000001410410624 0x9809f3e7ee3cf3e7 0xd3013e7cfdc79e7c

def z710 : W := mkw 0x177f6f5d40c18408 0x42efedeba8183081 0xf7fffffff1c71c7f 0xfefffffffe38e38f

def z711 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xffffffffee380007 0xfffffffffdc70000

def z712 : W := mkw 0x177fffffe61c71e5 0x22effffffcc38e3c 0x6ff60c180e3cf3e4 0x2dfec18301c79e7c

def z713 : W := mkw 0x26eff0161db7cad1 0x84ddfe02c3b6f95a 0xbffff01e1ffffffd 0xf7fffe03c3ffffff

def z714 : W := mkw 0x1aa760bd5b681f06 0x0354ec17ab6d03e0 0x1807f01ffff81f85 0x0300fe03ffff03f0

def z715 : W := mkw 0x028580021c0600c1 0x0050b0004380c018 0xd7878e1e1c071fff 0x7af0f1c3c380e3ff

def z716 : W := mkw 0x03851ab4ba1a7b34 0xa070a35697434f66 0x4f8e7df9f23bec18 0xa9f1cfbf3e477d83

def z717 : W := mkw 0x0dea4a6999a9ab2e 0x41bd494d33353565 0x178e42798c3fe3f9 0x42f1c84f3187fc7f

def z718 : W := mkw 0x26ddb5899f767428 0x44dbb6b133eece85 0x5789bd998c381c7a 0x4af137b33187038f

def z719 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0x77f7ffffe0000003 0x2efefffffc000000

def z720 : W := mkw 0x03058a16040400c1 0x0060b142c0808018 0xd7878e1e1c071fff 0x7af0f1c3c380e3ff

def z721 : W := mkw 0x05d80f801b601e00 0x00bb01f0036c03c0 0xeff80f801ff81f86 0xfdff01f003ff03f0

def z722 : W := mkw 0x177f6f5d40000a00 0x02efedeba8000140 0xf7ffffffe0001f83 0xfefffffffc0003f0

def z723 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xd78fbe7e7c071fff 0x7af1f7cfcf80e3ff

def z724 : W := mkw 0x03850a1618020ad1 0x8070a142c300415a 0xd7860e1e1c031ffe 0x7af0c1c3c38063ff

def z725 : W := mkw 0x177f6f5d40818000 0x02efedeba8103000 0xf7ffffffe007e003 0xfefffffffc00fc00

def z726 : W := mkw 0x0cc8002019280b06 0x0199000403250160 0xaff800001ff80384 0xf5ff000003ff0070

def z727 : W := mkw 0x177f6f5d40818000 0x02efedeba8103000 0xfffffffff3c7fc7f 0xfffffffffe78ff8f

def z728 : W := mkw 0x0dd80fe91b681f0e 0x41bb01fd236d03e1 0xeff80ff81ff81f9e 0xfdff01ff03ff03f3

def z729 : W := mkw 0x288090a2bfffffe7 0x2510121457fffffc 0x080000001fffffe4 0x0100000003fffffc

def z730 : W := mkw 0x24c8100019b1c000 0x0499020003363800 0xaff800001ff8e004 0xf5ff000003ff1c00

def z731 : W := mkw 0x26eff0021db7c0d1 0x84ddfe0043b6f81a 0xaffff0001fffe07d 0xf5fffe0003fffc0f

def z732 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xfff84fe19ff81f87 0xffff09fc33ff03f0

def z733 : W := mkw 0x03050a1600000ad1 0x8060a142c000015a 0xd7878e1e10071fff 0x7af0f1c3c200e3ff

def z734 : W := mkw 0x0dd89f42bd746ee3 0x21bb13e857ae8ddc 0x77f1fc07f1c4ec61 0x2efe3f80fe389d8c

def z735 : W := mkw 0x37cdba565d364ad1 0x86f9b74acba6c95a 0x0789b2666c380380 0x40f1364ccd870070

def z736 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xaffff3e01fffe007 0xf5fffe7c03fffc00

def z737 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x1809f3e7ee38f3e2 0xc3013e7cfdc71e7c

def z738 : W := mkw 0x1dd80ff45b681f06 0x03bb01fe8b6d03e0 0xeff80fe67ff81f86 0xfdff01fccfff03f0

def z739 : W := mkw 0x246a700001b1c000 0x048d4e0000363800 0xaff8700003f8e000 0xf5ff0e00007f1c00

def z740 : W := mkw 0x2b37ffe006dfdf06 0x0566fffc00dbfbe0 0x4007ffe00007ff83 0x0800fffc0000fff0

def z741 : W := mkw 0x19100fffe2483fe7 0x232201fffc4907fc 0x50000fffe0001fe2 0x0a0001fffc0003fc

def z742 : W := mkw 0x174d2ad4c2c1b428 0x42e9a55a98583685 0x0f89b26673c7fc7c 0x41f1364cce78ff8f

def z743 : W := mkw 0x2227f0020497c0d1 0x8444fe004092f81a 0x0007f0000007e079 0x0000fe000000fc0f

def z744 : W := mkw 0x3227f01fe497e0e1 0x2644fe03fc92fc1c 0x1007f01fe007e061 0x0200fe03fc00fc0c

def z745 : W := mkw 0x0dd80fe09b683f2e 0x41bb01fc136d07e5 0xeff80fe01ff81ffe 0xfdff01fc03ff03ff

def z746 : W := mkw 0x208090a2bfbffbf5 0xa410121457f7ff7e 0x080000001ffffffc 0x0100000003ffffff

def z747 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x1009f3e7ec3cf3e3 0x42013e7cfd879e7c

def z748 : W := mkw 0x31909f5d5db7c000 0x063213ebabb6f800 0x58000fffffffe006 0x0b0001fffffffc00

def z749 : W := mkw 0x247a75a9a3f9f52c 0x648f4eb5347f3ea5 0x287871e1e3f8e000 0x850f0e3c3c7f1c00

def z750 : W := mkw 0x003245a9a2c9b52c 0x600648b5345936a5 0xf8764df9f3c7fc7f 0xbf0ec9bf3e78ff8f

def z751 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xbffff007ffffe005 0xf7fffe00fffffc00

def z752 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xaff9f0001ff8e004 0xf5ff3e0003ff1c00

def z753 : W := mkw 0x14fae54b5c060ad1 0x829f5ca96b80c15a 0x207871e1fc071ffc 0x840f0e3c3f80e3ff

def z754 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0x2ff803e01ff81f84 0xc5ff007c03ff03f0

def z755 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xaffff0000ff8e001 0xf5fffe0001ff1c00

def z756 : W := mkw 0x00009022241c41c5 0x2000120444838838 0x9809f3e7ee3ce387 0xd3013e7cfdc79c70

def z757 : W := mkw 0x26eff0091db7c000 0x04ddfe0123b6f800 0xbffff0199fffe005 0xf7fffe0333fffc00

def z758 : W := mkw 0x0dd80fe99b683f2e 0x41bb01fd336d07e5 0xfffe0ff99fff1fff 0xffffc1ff33ffe3ff

def z759 : W := mkw 0x008090a2bf3c71e5 0x2010121457e78e3c 0x080000001ffcf3e4 0x0100000003ff9e7c

def z760 : W := mkw 0x26eff0021db7c0c1 0x04ddfe0043b6f818 0xfffffe1e1fffffff 0xffffffc3c3ffffff

def z761 : W := mkw 0x24c890001db7c000 0x0499120003b6f800 0xaff9f0001fffe005 0xf5ff3e0003fffc00

def z762 : W := mkw 0x04c8000019a18000 0x0099000003343000 0xaff800001fffe004 0xf5ff000003fffc00

def z763 : W := mkw 0x26ef600019a38000 0x04ddec0003347000 0xaffe40001fffe005 0xf5ffc80003fffc00

def z764 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x980ff3e7fe3ff3e7 0xf301fe7cffc7fe7c

def z765 : W := mkw 0x0e5d85f6076e15d7 0x81cbb0bec0edc2ba 0x387f81fe03ff0079 0x870ff03fc07fe00f

def z766 : W := mkw 0x0dc80a6019280b06 0x01b9014c03250160 0x2ff802600ff80380 0xc5ff004c01ff0070

def z767 : W := mkw 0x09100ff6a2483ff7 0xa12201fed44907fe 0x50000fffe0001ffa 0x0a0001fffc0003ff

def z768 : W := mkw 0x26ef60a2bbabb1e5 0x24ddec145775763c 0x37f603e7f1c313e2 0x26fec07cfe38627c

def z769 : W := mkw 0x09900fa01b681f06 0x013201f4036d03e0 0xeff00f801ff81f86 0xfdfe01f003ff03f0

def z770 : W := mkw 0x0dd80f6019680f06 0x01bb01ec032d01e0 0xeff80e601ff80f84 0xfdff01cc03ff01f0

def z771 : W := mkw 0x06efc0001da78000 0x00ddf80003b4f000 0xafffc0001fffe005 0xf5fff80003fffc00

def z772 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xdf87ce1e1e07ffff 0xfbf0f9c3c3c0ffff

def z773 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0x6ff80e601ff81f84 0x6dff01cc03ff03f0

def z774 : W := mkw 0x1227f01fe495e0e9 0x6244fe03fc92bc1d 0x1007f01fe007e079 0x0200fe03fc00fc0f

def z775 : W := mkw 0x167f654940000000 0x02cfeca928000000 0xb7fff3e7e0000003 0xf6fffe7cfc000000

def z776 : W := mkw 0x0032458982c1b428 0x400648b130583685 0x70764d9991c7fc7b 0x2e0ec9b33238ff8f

def z777 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xeff87fe1fff81f86 0xfdff0ffc3fff03f0

def z778 : W := mkw 0x175d2f5d40000000 0x02eba5eba8000000 0x0789b3e7e0000000 0x40f1367cfc000000

def z779 : W := mkw 0x0dd80fe91b681f06 0x01bb01fd236d03e0 0xfff80ff99ff81f86 0xffff01ff33ff03f0

def z780 : W := mkw 0x26cdb0001d364000 0x04d9b60003a6c800 0xaff9f0001ffce005 0xf5ff3e0003ff9c00

def z781 : W := mkw 0x028580021c060ad1 0x8050b0004380c15a 0xd7878c181c071fff 0x7af0f1830380e3ff

def z782 : W := mkw 0x26ef700019b3c000 0x04ddee0003367800 0xaffe70001ffbe004 0xf5ffce0003ff7c00

def z783 : W := mkw 0x088090a2bf7e7ff7 0xa110121457efcffe 0x080000001ffffffc 0x0100000003ffffff

def z784 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xe8760d9813c7fc7e 0xbd0ec1b30278ff8f

def z785 : W := mkw 0x24ea700019b1c000 0x049d4e0003363800 0x2ff870000ff8e000 0xc5ff0e0001ff1c00

def z786 : W := mkw 0x04c8000019200a00 0x0099000003240140 0xaff800001ff81f84 0xf5ff000003ff03f0

def z787 : W := mkw 0x0d580fe003681506 0x01ab01fc006d02a0 0xeff80fe00ff81386 0xfdff01fc01ff0270

def z788 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xaff640001fffe005 0xb5fec80003fffc00

def z789 : W := mkw 0x0dd80fe09b683f26 0x01bb01fc136d07e4 0xfff80fe19ff81fe6 0xffff01fc33ff03fc

def z790 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xe8764c1813c7fc7d 0xbd0ec9830278ff8f

def z791 : W := mkw 0x157a6f4940000000 0x02af4de928000000 0xf7f9ffe7e0000003 0xfeff3ffcfc000000

def z792 : W := mkw 0x0dd80ff41b681f16 0x81bb01fe836d03e2 0xeff80ff81ff81f9e 0xfdff01ff03ff03f3

def z793 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xd78f8ffe1c071fff 0xfaf1f1ffc380e3ff

def z794 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xd787fe1ffc071fff 0x7af0ffc3ff80e3ff

def z795 : W := mkw 0x174d2a5440000000 0x02e9a54a88000000 0xd78fffffe0000003 0xfaf1fffffc000000

def z796 : W := mkw 0x04c800a01b281104 0x0099001403650220 0xaff800001ff81384 0xf5ff000003ff0270

def z797 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0x77f9ffffe0000002 0xceff3ffffc000000

def z798 : W := mkw 0x26eff0021db7cad1 0x84ddfe0043b6f95a 0xfffffc181fffffff 0xffffff8303ffffff

def z799 : W := mkw 0x167f655d40000000 0x02cfecaba8000000 0xb7fff1ffe0000001 0xf6fffe3ffc000000

def z800 : W := mkw 0x0032458982c1b428 0x400648b130583685 0x68764d9993c7fc7c 0xad0ec9b33278ff8f

def z801 : W := mkw 0x088090a2bffdffef 0x6110121457ffbffd 0x080000001ffffffc 0x0100000003ffffff

def z802 : W := mkw 0x23859a161d364ad1 0x8470b342c3a6c95a 0xd7878e1e1c3f1fff 0x7af0f1c3c387e3ff

def z803 : W := mkw 0x147a75e9e2d9f52c 0x628f4ebd3c5b3ea5 0x287871e1e3f8e000 0x850f0e3c3c7f1c00

def z804 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xeff00d801ff81f86 0xbdfe01b003ff03f0

def z805 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xaffff2667fffe005 0xf5fffe4ccffffc00

def z806 : W := mkw 0x26eff0021db7c0c1 0x04ddfe0043b6f818 0xbffff0061fffe065 0xf7fffe00c3fffc0c

def z807 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0xd809ffffee3cffff 0xdb013ffffdc79fff

def z808 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xf877fd9ff3c7fc7f 0xbf0effb3fe78ff8f

def z809 : W := mkw 0x09100fff82483fff 0xc12201fff04907ff 0x50000fff80001ffa 0x0a0001fff00003ff

def z810 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0x2fffb0001fffe004 0x65fff60003fffc00

def z811 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xfff80fe7fff81f86 0xffff01fcffff03f0

def z812 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0x578fffffe0000003 0x4af1fffffc000000

def z813 : W := mkw 0x0dc80aa01b681f06 0x01b90154036d03e0 0xeff80e001ff81f86 0xfdff01c003ff03f0

def z814 : W := mkw 0x03850a1618020ad1 0x8070a142c300415a 0xd7878e1e10031ffb 0x7af0f1c3c20063ff

def z815 : W := mkw 0x0cc800a01b681f06 0x01990014036d03e0 0xaff803e01ff81f86 0xf5ff007c03ff03f0

def z816 : W := mkw 0x000090a0061c5104 0x0000121400c38a20 0x9809f3e7ee3cf387 0xd3013e7cfdc79e70

def z817 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xbffff0181fffe07d 0xf7fffe0303fffc0f

def z818 : W := mkw 0x0227d01fa497e0f9 0xe044fa03f492fc1f 0x1007f01fe007e079 0x0200fe03fc00fc0f

def z819 : W := mkw 0x26eff0001db7ca10 0x84ddfe0003b6f942 0xaffff0001fffec1d 0xf5fffe0003fffd83

def z820 : W := mkw 0x266f700001b1c000 0x04cdee0000363800 0xaffff00013ffe005 0xf5fffe00027ffc00

def z821 : W := mkw 0x0dd80fe09b683f26 0x01bb01fc136d07e4 0xeff84fe19ff8ff86 0xfdff09fc33ff1ff0

def z822 : W := mkw 0x26ef700019b3c000 0x04ddee0003367800 0x2ff6000013fbe000 0x25fec000027f7c00

def z823 : W := mkw 0x0dc80ae01b281b06 0x01b9015c03650360 0xaff803e01ff81386 0xf5ff007c03ff0270

def z824 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0xd80fffffee3cf3e7 0xfb01fffffdc79e7c

def z825 : W := mkw 0x256a7a1601b1cad1 0x84ad4f42c036395a 0x78787e1e03f8fffa 0x8f0f0fc3c07f1fff

def z826 : W := mkw 0x04c8000019200000 0x0099000003240000 0xaff840001ffce005 0xf5ff080003ff9c00

def z827 : W := mkw 0x26eff0091db7c008 0x44ddfe0123b6f801 0xaffff0181fffe01d 0xf5fffe0303fffc03

def z828 : W := mkw 0x2fcdba761d3e4bd7 0x85f9b74ec3a7c97a 0x0789b2660c380380 0x40f1364cc1870070

def z829 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x57878e1e1c031ffa 0x6af0f1c3c38063ff

def z830 : W := mkw 0x175d2f5d40000000 0x02eba5eba8000000 0xd789ffffe0000003 0xdaf13ffffc000000

def z831 : W := mkw 0x03859a161c164ad1 0x8070b342c382c95a 0xdf878e1e1e3fffff 0x7bf0f1c3c3c7ffff

def z832 : W := mkw 0x3fff6f5d59e38e02 0x07ffedebab3c71c0 0x67f60c1811c30c00 0x2cfec18302386180

def z833 : W := mkw 0x01808a021c040ac1 0x0030114043808158 0xd7878e1e1c071fff 0x7af0f1c3c380e3ff

def z834 : W := mkw 0x00009002041440c1 0x0000120040828818 0x9809f3e7ee3cf3e7 0xd3013e7cfdc79e7c

def z835 : W := mkw 0x03374f1d00000000 0x0066e9e3a0000000 0xf7ffffffe0000003 0xfefffffffc000000

def z836 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xeff80fe00ff80382 0xfdff01fc01ff0070

def z837 : W := mkw 0x176f6a5440000000 0x02eded4a88000000 0xb7fff3e7e0000003 0xf6fffe7cfc000000

def z838 : W := mkw 0x15580f5d40000000 0x02ab01eba8000000 0xf7f9ffffe0000003 0xfeff3ffffc000000

def z839 : W := mkw 0x0dd80f6019280b06 0x01bb01ec03250160 0xeff80fe01ff80386 0xfdff01fc03ff0070

def z840 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x57878c1e1c071ffd 0x2af0f183c380e3ff

def z841 : W := mkw 0x000090a2a65c75e5 0x2000121454cb8ebc 0x9809f3e7fffcffe7 0xd3013e7cffff9ffc

def z842 : W := mkw 0x26cd90001db7c000 0x04d9b20003b6f800 0xafff80001fffe005 0xf5fff00003fffc00

def z843 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0x77ffbfffe0000002 0x6efff7fffc000000

def z844 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x1809f3e7ee3ce3e1 0xc3013e7cfdc79c7c

def z845 : W := mkw 0x26eff0001db7ca00 0x04ddfe0003b6f940 0xaffff0001fffff85 0xf5fffe0003fffff0

def z846 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xaffff1e1ffffe005 0xf5fffe3c3ffffc00

def z847 : W := mkw 0x26eff0141db7c010 0x84ddfe0283b6f802 0xaffff0181fffe01d 0xf5fffe0303fffc03

def z848 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xaff780001fffe005 0x75fef00003fffc00

def z849 : W := mkw 0x26ef700019b3c000 0x04ddee0003367800 0xaffe700013ffe005 0xb5ffce00027ffc00

def z850 : W := mkw 0x01800a1618000ad1 0x80300142c300015a 0xd7860e1e1c071fff 0x7af0c1c3c380e3ff

def z851 : W := mkw 0x36eff0145db7c000 0x06ddfe028bb6f800 0xaffff0067fffe005 0xf5fffe00cffffc00

def z852 : W := mkw 0x2c7a75e983f9f52e 0x458f4ebd307f3ea5 0x287871e183f8e000 0x850f0e3c307f1c00

def z853 : W := mkw 0x24ea700019b1c000 0x049d4e0003363800 0x2ff8700013f8e000 0xa5ff0e00027f1c00

def z854 : W := mkw 0x03b7cf9f9ec7bef9 0xc076f9f3f3d8f7df 0x2ff1c3878fc0e380 0xc5fe3870f1f81c70

def z855 : W := mkw 0x05c80a0019200a00 0x00b9014003240140 0xaff802001ff80384 0xf5ff004003ff0070

def z856 : W := mkw 0x36eff01d5db7c000 0x06ddfe03abb6f800 0xaffff0181fffe005 0xf5fffe0303fffc00

def z857 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xf7ffffffe007007b 0xfefffffffc00e00f

def z858 : W := mkw 0x175d2f5d40000000 0x02eba5eba8000000 0xf7f9bfffe0000002 0xfeff37fffc000000

def z859 : W := mkw 0x0032458002c19400 0x000648b000583280 0xf8764d9813c7fc7f 0xbf0ec9b30278ff8f

def z860 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xd787cf9f9c071fff 0xfaf0f9f3f380e3ff

def z861 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xf7ffffffe0001c7b 0xfefffffffc00038f

def z862 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xf87ffd9993c7fc7f 0xff0fffb33278ff8f

def z863 : W := mkw 0x26cdb0001db7c000 0x04d9b60003b6f800 0xaff9b0001fffe004 0xf5ff360003fffc00

def z864 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xb7f9f3e7e0000003 0xd6ff3e7cfc000000

def z865 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0x2ffe70001fffe004 0xa5ffce0003fffc00

def z866 : W := mkw 0x0032d52b24ddc5cd 0x60065aa5649bb8b9 0x607fbe7e7dfb0f98 0x6c0ff7cfcfbf61f3

def z867 : W := mkw 0x1c7a65e9c3e9b52e 0x438f4cbd387d36a5 0x287871e1e3f8e000 0x850f0e3c3c7f1c00

def z868 : W := mkw 0x0448000000000000 0x0089000000000000 0xb7f9f3e7e0000003 0xf6ff3e7cfc000000

def z869 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xc7860e181c071ffe 0x78f0c1c30380e3ff

def z870 : W := mkw 0x175d2f5d40000000 0x02eba5eba8000000 0xd78fbfffe0000003 0x7af1f7fffc000000

def z871 : W := mkw 0x03858a001c060a00 0x0070b1400380c140 0xd7878e181c071fff 0x7af0f1c30380e3ff

def z872 : W := mkw 0x0c7a55e9a3f9f52e 0x618f4abd347f3ea5 0x287871e1e3f8e000 0x850f0e3c3c7f1c00

def z873 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xeffffc001ffffc07 0xfdffff8003ffff80

def z874 : W := mkw 0x0dd80f6019680f06 0x01bb01ec032d01e0 0x27f802600df80380 0x44ff004c01bf0070

def z875 : W := mkw 0x26eff0021db7c0c1 0x04ddfe0043b6f818 0xaffff0001ffff3e5 0xf5fffe0003fffe7c

def z876 : W := mkw 0x05480a4000000000 0x00a9014800000000 0x9789f3e7e0000003 0xd2f13e7cfc000000

def z877 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xfff80fe01ffc1fe7 0xffff01fc03ff83fc

def z878 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xbffff0001ffff067 0xf7fffe0003fffe0c

def z879 : W := mkw 0x1dd80ffd5b681f06 0x03bb01ffab6d03e0 0xeff80ff81ff81f86 0xfdff01ff03ff03f0

def z880 : W := mkw 0x0032450980c1a428 0x400648a130183485 0xf8764c1993c7ec7d 0xbf0ec9833278fd8f

def z881 : W := mkw 0x26eff0021db7cad1 0x84ddfe0043b6f95a 0xbffff2061fffffff 0xf7fffe40c3ffffff

def z882 : W := mkw 0x24eaf0001db5c000 0x049d5e0003b6b800 0xaff9f0001ffce005 0xf5ff3e0003ff9c00

def z883 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xa7fff3e7e0000001 0xf4fffe7cfc000000

def z884 : W := mkw 0x1dd82fe05b681f06 0x03bb05fc0b6d03e0 0xeff83fe07ff81f86 0xfdff07fc0fff03f0

def z885 : W := mkw 0x09100fe082483f2e 0x412201fc104907e5 0x40000fe000001ffa 0x080001fc000003ff

def z886 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0x2ff9f0001fffe004 0xc5ff3e0003fffc00

def z887 : W := mkw 0x04c890001d344000 0x0099120003a68800 0xaff800001ffce004 0xf5ff000003ff9c00

def z888 : W := mkw 0x0022408082c1b428 0x4004481010583685 0xf8764c1813c7fc7f 0xbf0ec9830278ff8f

def z889 : W := mkw 0x03850a1418020a10 0x8070a14283004142 0xd7860e181c071fff 0x7af0c1c30380e3ff

def z890 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0x2ffff0000fffe001 0xc5fffe0001fffc00

def z891 : W := mkw 0x36eff01f5db7c0d1 0x86ddfe03ebb6f81a 0xbffff01fffffe07d 0xf7fffe03fffffc0f

def z892 : W := mkw 0x088090a2bf3c7be7 0x2110121457e78f7c 0x080000000e3cf3e4 0x0100000001c79e7c

def z893 : W := mkw 0x13376f5d40000000 0x0266edeba8000000 0xd787ffffe0000003 0x7af0fffffc000000

def z894 : W := mkw 0x177f6f5d40400400 0x02efedeba8080080 0xf7fffffff1c00c03 0xfefffffffe380180

def z895 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0x2ff7f0001fffe005 0x25fefe0003fffc00

def z896 : W := mkw 0x36eff01d5db7c000 0x06ddfe03abb6f800 0xbffff3ffffffe007 0xf7fffe7ffffffc00

def z897 : W := mkw 0x057a4f4900000000 0x00af49e920000000 0xf7ffffffe0000003 0xfefffffffc000000

def z898 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xd78ffe1e1c071fff 0xfaf1ffc3c380e3ff

def z899 : W := mkw 0x04d805a01b681504 0x009b00b4036d02a0 0xeff80fe01ff81f86 0xfdff01fc03ff03f0

def z900 : W := mkw 0x00009022a41c61e5 0x2000120454838c3c 0x9009f3e7ec3ce3e3 0xd2013e7cfd879c7c

def z901 : W := mkw 0x075d0f5400000000 0x00eba1ea80000000 0xf7ffffffe0000003 0xfefffffffc000000

def z902 : W := mkw 0x000010a0a2187124 0x2000021414430e24 0x9809f3e7ee38f387 0xd3013e7cfdc71e70

def z903 : W := mkw 0x03859a163c164ad1 0xa070b342c782c95a 0xd787be1e7c071fff 0x7af0f7c3cf80e3ff

def z904 : W := mkw 0x003245a982c9b52c 0x400648b5305936a5 0xf87e4df993fffc7f 0xbf0fc9bf327fff8f

def z905 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xf7fffffff0030c1b 0xfefffffffe006183

def z906 : W := mkw 0x05d80fe01b281104 0x00bb01fc03650220 0xeff80fe01ff81386 0xfdff01fc03ff0270

def z907 : W := mkw 0x37ff6f5d59a38a10 0x86ffedebab347142 0x67f60c1811c30c18 0x2cfec18302386183

def z908 : W := mkw 0x01100fbfa2483ffd 0xe02201f7f44907ff 0x50000fffe0001ffa 0x0a0001fffc0003ff

def z909 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xe7f9ffe7e0000002 0xfcff3ffcfc000000

def z910 : W := mkw 0x26eff0021db7c0c1 0x04ddfe0043b6f818 0xbffff3e7fffff3e7 0xf7fffe7cfffffe7c

def z911 : W := mkw 0x26eff0161db7c0d1 0x84ddfe02c3b6f81a 0xbffff21e1ffff3ff 0xf7fffe43c3fffe7f

def z912 : W := mkw 0x03050a1400000000 0x0060a14280000000 0x9789f3e7e0000003 0xd2f13e7cfc000000

def z913 : W := mkw 0x0dd80fe09b683f26 0x01bb01fc136d07e4 0xfff9ffe7fffcffe7 0xffff3ffcffff9ffc

def z914 : W := mkw 0x0010058082c1b428 0x400200b010583685 0xf8760d9813c7fc7f 0xbf0ec1b30278ff8f

def z915 : W := mkw 0x3227f01f4497c0d1 0x8644fe03e892f81a 0x1007f01fe007e079 0x0200fe03fc00fc0f

def z916 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0x77fffdffe0000001 0xaeffffbffc000000

def z917 : W := mkw 0x174d2a5440000000 0x02e9a54a88000000 0x0789f3e7e0000000 0xc0f13e7cfc000000

def z918 : W := mkw 0x24ea700019b1c000 0x049d4e0003363800 0xaffe70001fffe005 0xf5ffce0003fffc00

def z919 : W := mkw 0x26eff0141db7c000 0x04ddfe0283b6f800 0xbffff01e1fffe005 0xf7fffe03c3fffc00

def z920 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xfffffffff3c00007 0xfffffffffe780000

def z921 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0xb879f3e7fffcf3e7 0xf70f3e7cffff9e7c

def z922 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xeff9ffe01ff81f87 0xfdff3ffc03ff03f0

def z923 : W := mkw 0x177f6f5d40400408 0x42efedeba8080081 0xf7ffffffe0000c1b 0xfefffffffc000183

def z924 : W := mkw 0x01900fa01a481f04 0x003201f4034903e0 0xeff80fe01ff81f86 0xfdff01fc03ff03f0

def z925 : W := mkw 0x09100fe082483f26 0x012201fc104907e4 0x50000fe180001fe2 0x0a0001fc300003fc

def z926 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xaff803e00ff81386 0xd5ff007c01ff0270

def z927 : W := mkw 0x05580fe002481504 0x00ab01fc004902a0 0xeff80fe01ff81f86 0xfdff01fc03ff03f0

def z928 : W := mkw 0x066ff0000495c000 0x00cdfe000092b800 0xaffff0001fffe005 0xf5fffe0003fffc00

def z929 : W := mkw 0x0010058082403420 0x000200b010480684 0xf8764d9993c7fc7f 0xbf0ec9b33278ff8f

def z930 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xf87e7df9f3c7fc7f 0xbf0fcfbf3e78ff8f

def z931 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xf8760c1813c7fc7f 0x3f0ec1830278ff8f

def z932 : W := mkw 0x0cc800a01b681f06 0x01990014036d03e0 0x2ff000001ff81f84 0x25fe000003ff03f0

def z933 : W := mkw 0x1f7f6f5d40400e02 0x03efedeba80801c0 0xf7ffffffe0000c03 0xfefffffffc000180

def z934 : W := mkw 0x002240808281b020 0x0004481010503604 0xf8764d9993c7fc7f 0xbf0ec9b33278ff8f

def z935 : W := mkw 0x076f6a1400000000 0x00eded4280000000 0xf7ffffffe0000003 0xfefffffffc000000

def z936 : W := mkw 0x0dd80f6019680f06 0x01bb01ec032d01e0 0xe7f80fe01df80f82 0xfcff01fc03bf01f0

def z937 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xfff78e1e1fc71fff 0xfffef1c3c3f8e3ff

def z938 : W := mkw 0x04c8000019200000 0x0099000003240000 0xaff802001ff81386 0xf5ff004003ff0270

def z939 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x8809f3e7ee3ce385 0xd1013e7cfdc79c70

def z940 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xfff80ff81ff81ffe 0xffff01ff03ff03ff

def z941 : W := mkw 0x26eff0023db7c0c1 0x24ddfe0047b6f818 0xaffff0067fffe005 0xf5fffe00cffffc00

def z942 : W := mkw 0x04c8100019304000 0x0099020003260800 0xaff870001ff8e004 0xf5ff0e0003ff1c00

def z943 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xf877cf9f93c7fc7f 0xff0ef9f3f278ff8f

def z944 : W := mkw 0x26eff0161db7c0d1 0x84ddfe02c3b6f81a 0xaffff0061fffe005 0xf5fffe00c3fffc00

def z945 : W := mkw 0x2385ba161c164ad1 0x8470b742c382c95a 0xd787be1e1c071fff 0x7af0f7c3c380e3ff

def z946 : W := mkw 0x03858a161d260ad1 0x8070b142c3a4c15a 0xdf878e1e1fff1fff 0x7bf0f1c3c3ffe3ff

def z947 : W := mkw 0x03859a161c164ad1 0x8070b342c382c95a 0xd78fbe1e1c3f1fff 0x7af1f7c3c387e3ff

def z948 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xfff98fe61ff81f87 0xffff31fcc3ff03f0

def z949 : W := mkw 0x0032458982c1b428 0x400648b130583685 0x78764c1993c7fc7d 0x2f0ec9833278ff8f

def z950 : W := mkw 0x27cdba363d3e4bd5 0xa4f9b746c7a7c97a 0x0789b2666c380380 0x40f1364ccd870070

def z951 : W := mkw 0x175d2f5440000000 0x02eba5ea88000000 0xf7f9ffe7e0000003 0xfeff3ffcfc000000

def z952 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x8809f3e7ee38f386 0xd1013e7cfdc71e70

def z953 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xaff803e01ff80384 0xf5ff007c03ff0070

def z954 : W := mkw 0x13858a565c060ad1 0x8270b14acb80c15a 0xd7878e7e7c071fff 0x7af0f1cfcf80e3ff

def z955 : W := mkw 0x266ff00005b7c000 0x04cdfe0000b6f800 0xaffff00003ffe001 0xf5fffe00007ffc00

def z956 : W := mkw 0x0dd80fe01b6a1f16 0x81bb01fc036d43e2 0xeff80fe01ffb1f9e 0xfdff01fc03ff63f3

def z957 : W := mkw 0x03859a161c164ad1 0x8070b342c382c95a 0xdf8ffffffe3fffff 0xfbf1ffffffc7ffff

def z958 : W := mkw 0x0032458982c1b428 0x400648b130583685 0x78764d9993c7ec79 0xaf0ec9b33278fd8f

def z959 : W := mkw 0x000090a2a61e71f5 0xa000121454c3ce3e 0x9809f3e7ee3ff3ff 0xd3013e7cfdc7fe7f

def z960 : W := mkw 0x177f6f5d40c18408 0x42efedeba8183081 0xf7ffffffe1c00003 0xfefffffffc380000

def z961 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xeff80c001ff81f84 0xfdff018003ff03f0

def z962 : W := mkw 0x003245a982c9b52c 0x400648b5305936a5 0xf87fffffffffffff 0xff0fffffffffffff

def z963 : W := mkw 0x0dd80fe0bb683f26 0x21bb01fc176d07e4 0xeff80fe1fff81f86 0xfdff01fc3fff03f0

def z964 : W := mkw 0x177f6f5d41200000 0x02efedeba8240000 0xffffffffe3f80003 0xfffffffffc7f0000

def z965 : W := mkw 0x003245a982c9b52c 0x400648b5305936a5 0xf8764ff993c7ffff 0xbf0ec9ff3278ffff

def z966 : W := mkw 0x008090a2be1c7be5 0x2010121457c38f7c 0x080000001e3cffe4 0x0100000003c79ffc

def z967 : W := mkw 0x003245a982c9b52c 0x400648b5305936a5 0xf8764d999fffffff 0xbf0ec9b333ffffff

def z968 : W := mkw 0x177f6f5d40818008 0x42efedeba8103001 0xf7ffffffe003001b 0xfefffffffc006003

def z969 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x980ff3ffee3ff3ff 0xd301fe7ffdc7fe7f

def z970 : W := mkw 0x05d80f4019200a00 0x00bb01e803240140 0xeff80fe01ff81f86 0xfdff01fc03ff03f0

def z971 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0x6ff80de01ff81f84 0xadff01bc03ff03f0

def z972 : W := mkw 0x36eff0405db7c000 0x06ddfe080bb6f800 0xaffff0607fffe005 0xf5fffe0c0ffffc00

def z973 : W := mkw 0x03058a1604060ad1 0x8060b142c080c15a 0xd7878e1e00071ffb 0x7af0f1c3c000e3ff

def z974 : W := mkw 0x13276a1d40000000 0x0264ed43a8000000 0xd78fffffe0000003 0xfaf1fffffc000000

def z975 : W := mkw 0x266f700001b1c000 0x04cdee0000363800 0x2ffe700003f8e000 0xa5ffce00007f1c00

def z976 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xeff80fe01fff1ffe 0xfdff01fc03ffe3ff

def z977 : W := mkw 0x03850a1418000a00 0x0070a14283000140 0xd7878e1e1c071fff 0x7af0f1c3c380e3ff

def z978 : W := mkw 0x000090a2a65c75ed 0x6000121454cb8ebd 0x9809f3e7ee3cffff 0xd3013e7cfdc79fff

def z979 : W := mkw 0x03850a1618020ad1 0x8070a142c300415a 0xd7860e1e10071fff 0x3af0c1c3c200e3ff

def z980 : W := mkw 0x01000a0000000000 0x0020014000000000 0xd789ffe7e0000003 0xfaf13ffcfc000000

def z981 : W := mkw 0x177f6f5d40818000 0x02efedeba8103000 0xffffffffe3c0e003 0xfffffffffc781c00

def z982 : W := mkw 0x2227f0020497c0c1 0x0444fe004092f818 0x1007f0060007e061 0x0200fe00c000fc0c

def z983 : W := mkw 0x2227f01f8497e0f9 0xc444fe03f092fc1f 0x1007f01f8007e079 0x0200fe03f000fc0f

def z984 : W := mkw 0x177f6f5d40000a10 0x82efedeba8000142 0xf7ffffffe0000c1b 0xfefffffffc000183

def z985 : W := mkw 0x06ef600019a18000 0x00ddec0003343000 0xaffff0001fffe005 0xf5fffe0003fffc00

def z986 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xeff9bfe67ff81f86 0xfdff37fccfff03f0

def z987 : W := mkw 0x26ef700019b3c000 0x04ddee0003367800 0xaffff00013fbe001 0xf5fffe00027f7c00

def z988 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x57860e1e1c071ffe 0x2af0c1c3c380e3ff

def z989 : W := mkw 0x10326589c2c1b428 0x42064cb138583685 0xf8767d99f3c7fc7f 0xbf0ecfb33e78ff8f

def z990 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xf7ffffffec001387 0xfefffffffd800270

def z991 : W := mkw 0x0dd80fe09b683f26 0x01bb01fc136d07e4 0xfffe4ff99fffffff 0xffffc9ff33ffffff

def z992 : W := mkw 0x09100fe0a2483f26 0x212201fc144907e4 0x40000fe1e0001f82 0x080001fc3c0003f0

def z993 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xfffffc181fffe007 0xffffff8303fffc00

def z994 : W := mkw 0x1385aa165c060ad1 0x8270b542cb80c15a 0xd787be1e7c071fff 0x7af0f7c3cf80e3ff

def z995 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x0809f3e7ee3cf3e4 0xc1013e7cfdc79e7c

def z996 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xaffff0001ffffc7d 0xf5fffe0003ffff8f

def z997 : W := mkw 0x266f700001b1c000 0x04cdee0000363800 0x2ff9f00003f8e000 0xc5ff3e00007f1c00

def z998 : W := mkw 0x2227f00ba497e0e9 0x6444fe017492fc1d 0x1007f01fe007e079 0x0200fe03fc00fc0f

def z999 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xeffe0fe01fff1f87 0xfdffc1fc03ffe3f0

def z1000 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0x2ffff0001ffbe000 0xe5fffe0003ff7c00

def z1001 : W := mkw 0x266ff00005b5c000 0x04cdfe0000b6b800 0xaffff0000ffce005 0xf5fffe0001ff9c00

def z1002 : W := mkw 0x008090a2bedffffd 0xe010121457dbffff 0x080000001ffffffc 0x0100000003ffffff

def z1003 : W := mkw 0x0dd80fe99b683f2e 0x41bb01fd336d07e5 0xeff80fe19ff81f86 0xfdff01fc33ff03f0

def z1004 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xeff84fe01ffcff87 0xfdff09fc03ff9ff0

def z1005 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xffffffffe204e007 0xfffffffffc409c00

def z1006 : W := mkw 0x24c890001db7c000 0x0499120003b6f800 0x2ff000001fffe004 0x25fe000003fffc00

def z1007 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xf8764ffff3c7fc7f 0xbf0ec9fffe78ff8f

def z1008 : W := mkw 0x208090a2bf3e71e5 0x2410121457e7ce3c 0x080000000e3cf3e4 0x0100000001c79e7c

def z1009 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0xd809ffe7fe3cffe7 0xfb013ffcffc79ffc

def z1010 : W := mkw 0x008090a2be1e71e5 0x2010121457c3ce3c 0x080000001e3ff3e4 0x0100000003c7fe7c

def z1011 : W := mkw 0x1dd80ffd5b681f06 0x03bb01ffab6d03e0 0xfff9fffffff81f87 0xffff3fffffff03f0

def z1012 : W := mkw 0x2227f016a497e0f1 0xa444fe02d492fc1e 0x1007f01fe007e079 0x0200fe03fc00fc0f

def z1013 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xd7860c181c071fff 0x3af0c1830380e3ff

def z1014 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xf8764f999fc7ffff 0xff0ec9f333f8ffff

def z1015 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xeff00e001ff81f86 0x7dfe01c003ff03f0

def z1016 : W := mkw 0x24ead0001db7c000 0x049d5a0003b6f800 0xaffe40001fffe005 0xf5ffc80003fffc00

def z1017 : W := mkw 0x04c8002019280104 0x0099000403250020 0xaff802601ff80384 0xf5ff004c03ff0070

def z1018 : W := mkw 0x2227f0160497c0d1 0x8444fe02c092f81a 0x0007f0060007e001 0x0000fe00c000fc00

def z1019 : W := mkw 0x083245e982c9b52e 0x410648bd305936a5 0xf8764df993c7fc7f 0xbf0ec9bf3278ff8f

def z1020 : W := mkw 0x26ef700019b3c000 0x04ddee0003367800 0x2ff8700003f8e000 0x85ff0e00007f1c00

def z1021 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xaffff2001ffff387 0xf5fffe4003fffe70

def z1022 : W := mkw 0x09100fe982483f2e 0x412201fd304907e5 0x40000fe180001f82 0x080001fc300003f0

def z1023 : W := mkw 0x0cd805e01b681506 0x019b00bc036d02a0 0xaff803e01ff81386 0xf5ff007c03ff0270

def z1024 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0x6ff00fe01ff81f86 0x2dfe01fc03ff03f0

def z1025 : W := mkw 0x22a7d0001db7c000 0x0454fa0003b6f800 0xaff7c0001fffe005 0xf5fef80003fffc00

def z1026 : W := mkw 0x19100ffdc2483f2e 0x432201ffb84907e5 0x50000fffe0001ffa 0x0a0001fffc0003ff

def z1027 : W := mkw 0x26ef700019b1c000 0x04ddee0003363800 0xaffff0001ff8e005 0xf5fffe0003ff1c00

def z1028 : W := mkw 0x0205000000000000 0x0040a00000000000 0x978ff3e7e0000003 0xf2f1fe7cfc000000

def z1029 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xf7ffffffe0041067 0xfefffffffc00820c

def z1030 : W := mkw 0x06cd90001d364000 0x00d9b20003a6c800 0xaffff0001fffe005 0xf5fffe0003fffc00

def z1031 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xdf8f8e1e1e3f1fff 0xfbf1f1c3c3c7e3ff

def z1032 : W := mkw 0x174d2a5440000000 0x02e9a54a88000000 0x1789b3e7e0000002 0x42f1367cfc000000

def z1033 : W := mkw 0x09100fe2a2483fe7 0x212201fc544907fc 0x40000fe000001fe2 0x080001fc000003fc

def z1034 : W := mkw 0x2227f0022497c0c1 0x2444fe004492f818 0x0007f0066007e001 0x0000fe00cc00fc00

def z1035 : W := mkw 0x24eaf0001db7c000 0x049d5e0003b6f800 0xaff870001fffe004 0xf5ff0e0003fffc00

def z1036 : W := mkw 0x0dd80f6019680f06 0x01bb01ec032d01e0 0xe7f80e601df81f86 0x7cff01cc03bf03f0

def z1037 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0x67f80fe01df81f82 0x6cff01fc03bf03f0

def z1038 : W := mkw 0x01808a021c060ad1 0x803011404380c15a 0xd7860e181c071fff 0x7af0c1c30380e3ff

def z1039 : W := mkw 0x0032458982c1b428 0x400648b130583685 0x78760d9993c7fc7e 0x2f0ec1b33278ff8f

def z1040 : W := mkw 0x0032450900c18408 0x400648a120183081 0xf8764c1813c7fc7f 0xbf0ec9830278ff8f

def z1041 : W := mkw 0x177f6f5d40818000 0x02efedeba8103000 0xf7fffffff1c30003 0xfefffffffe386000

def z1042 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0x6ff80fe00ff81f82 0xcdff01fc01ff03f0

def z1043 : W := mkw 0x0dc80a6019280b06 0x01b9014c03250160 0xeff80e601ff81f86 0xfdff01cc03ff03f0

def z1044 : W := mkw 0x1fff6f5d59e18e0a 0x43ffedebab3c31c1 0x67f60c1811c30c18 0x2cfec18302386183

def z1045 : W := mkw 0x02a7d0001c97c000 0x0054fa000392f800 0xaffff0001fffe005 0xf5fffe0003fffc00

def z1046 : W := mkw 0x26eff0161db7c0d1 0x84ddfe02c3b6f81a 0xfffffc1e1ffffc7f 0xffffff83c3ffff8f

def z1047 : W := mkw 0x0dd80f6019680f06 0x01bb01ec032d01e0 0x67f00c001df80f80 0x2cfe018003bf01f0

def z1048 : W := mkw 0x03850a1618020ad1 0x8070a142c300415a 0x47860c1810031ff8 0x28f0c183020063ff

def z1049 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xaff9f0000ffce005 0xd5ff3e0001ff9c00

def z1050 : W := mkw 0x103245c9c2c1b428 0x420648b938583685 0xf8764df9f3c7fc7f 0xbf0ec9bf3e78ff8f

def z1051 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x9809f3e7fe3fffff 0xd3013e7cffc7ffff

def z1052 : W := mkw 0x0dd80fe09b683f26 0x01bb01fc136d07e4 0xeff80fe01ffcffe6 0xfdff01fc03ff9ffc

def z1053 : W := mkw 0x0dc80ae01b681f06 0x01b9015c036d03e0 0xaff802601ff81f84 0xf5ff004c03ff03f0

def z1054 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0x2ffff00013ffe001 0xa5fffe00027ffc00

def z1055 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xf87e4ff993c7fc7f 0xff0fc9ff3278ff8f

def z1056 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xeffe0ff81ffb1f9e 0xfdffc1ff03ff63f3

def z1057 : W := mkw 0x0032458982c1b428 0x400648b130583685 0xf87e4d999ffffc7f 0xff0fc9b333ffff8f

def z1058 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x57878e1e10071ffb 0x2af0f1c3c200e3ff

def z1059 : W := mkw 0x0dc80a6019280b06 0x01b9014c03250160 0x27f802601df80380 0x64ff004c03bf0070

def z1060 : W := mkw 0x064d200000000000 0x00c9a40000000000 0x9789f3e7e0000003 0xd2f13e7cfc000000

def z1061 : W := mkw 0x26eff0021db7c0c1 0x04ddfe0043b6f818 0xaffff2061fffe385 0xf5fffe40c3fffc70

def z1062 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xbffff2061fffe007 0xf7fffe40c3fffc00

def z1063 : W := mkw 0x0dd80fe99b683f2e 0x41bb01fd336d07e5 0xfff84ff99ffcffff 0xffff09ff33ff9fff

def z1064 : W := mkw 0x0cd805e01b681f06 0x019b00bc036d03e0 0xaff801e01ff81f84 0xf5ff003c03ff03f0

def z1065 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0xfffe0ff81ff81f87 0xffffc1ff03ff03f0

def z1066 : W := mkw 0x0dd80fe01b681f06 0x01bb01fc036d03e0 0x6ff80fe01ff80f80 0xedff01fc03ff01f0

def z1067 : W := mkw 0x1dd80fe95b681f06 0x03bb01fd2b6d03e0 0xeff80fe1fff81f86 0xfdff01fc3fff03f0

def z1068 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0x37fff3ffe0000001 0xc6fffe7ffc000000

def z1069 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xf7fffffff0070007 0xfefffffffe00e000

def z1070 : W := mkw 0x377f6f5d40838000 0x06efedeba8107000 0xf7ffffffe0030003 0xfefffffffc006000

def z1071 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0xf7fffffff0001c07 0xfefffffffe000380

def z1072 : W := mkw 0x0032450980c1a428 0x400648a130183485 0x60760c1811c7ec78 0x2c0ec1830238fd8f

def z1073 : W := mkw 0x2227f002a497e0e1 0x2444fe005492fc1c 0x0007f0000007e061 0x0000fe000000fc0c

def z1074 : W := mkw 0x04ea400019a18000 0x009d480003343000 0xaff840001ff8e004 0xf5ff080003ff1c00

def z1075 : W := mkw 0x067f650900000000 0x00cfeca120000000 0xf7ffffffe0000003 0xfefffffffc000000

def z1076 : W := mkw 0x377f6f5d41a18000 0x06efedeba8343000 0xf7ffffffe1c00003 0xfefffffffc380000

def z1077 : W := mkw 0x13150f5d40000000 0x0262a1eba8000000 0xd78fffffe0000003 0xfaf1fffffc000000

def z1078 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x47878e1e1c071ffc 0x68f0f1c3c380e3ff

def z1079 : W := mkw 0x05c80aa01b281b04 0x00b9015403650360 0xeff80fe01ff81f86 0xfdff01fc03ff03f0

def z1080 : W := mkw 0x03859a161c164ad1 0x8070b342c382c95a 0xd787fe1e1c07ffff 0x7af0ffc3c380ffff

def z1081 : W := mkw 0x0dd80f4019600e02 0x01bb01e8032c01c0 0xeff80e001ff81f86 0xfdff01c003ff03f0

def z1082 : W := mkw 0x0032450900818000 0x000648a120103000 0xf8764d9993c7fc7f 0xbf0ec9b33278ff8f

def z1083 : W := mkw 0x0fcd9a763d3e4bd7 0xa1f9b34ec7a7c97a 0x0789b2666c380380 0x40f1364ccd870070

def z1084 : W := mkw 0x000090a2a61c71e5 0x2000121454c38e3c 0x9809f3e7ee38e383 0xd3013e7cfdc71c70

def z1085 : W := mkw 0x177f6f5d40c18408 0x42efedeba8183081 0xfffffffff3c7ec1f 0xfffffffffe78fd83

def z1086 : W := mkw 0x06eff0001d344000 0x00ddfe0003a68800 0xaffff0001ffce005 0xf5fffe0003ff9c00

def z1087 : W := mkw 0x26eff0021db7cad1 0x84ddfe0043b6f95a 0xaffff0001fffe385 0xf5fffe0003fffc70

def z1088 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0x57878e1e0c071ffb 0x4af0f1c3c180e3ff

def z1089 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xbffff1819fffe007 0xf7fffe3033fffc00

def z1090 : W := mkw 0x208090a2bffff5ed 0x6410121457fffebd 0x080000001ffffffc 0x0100000003ffffff

def z1091 : W := mkw 0x03858a161c060ad1 0x8070b142c380c15a 0xd7878ffffc071fff 0x7af0f1ffff80e3ff

def z1092 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xeffffc181fffec1d 0xfdffff8303fffd83

def z1093 : W := mkw 0x0032450980c1a428 0x400648a130183485 0xf0764c1991c7fc7f 0x3e0ec9833238ff8f

def z1094 : W := mkw 0x166f601d40000000 0x02cdec03a8000000 0xb7fff3ffe0000003 0xf6fffe7ffc000000

def z1095 : W := mkw 0x1dd80ffddb683f2e 0x43bb01ffbb6d07e5 0xfff80ffffff81ffe 0xffff01ffffff03ff

def z1096 : W := mkw 0x04ead0001db5c000 0x009d5a0003b6b800 0xaffff0001fffe005 0xf5fffe0003fffc00

def z1097 : W := mkw 0x36eff0095db7c000 0x06ddfe012bb6f800 0xaffff001ffffe005 0xf5fffe003ffffc00

def z1098 : W := mkw 0x0dd80ff41b681f06 0x01bb01fe836d03e0 0xfff80ffe1ff81f86 0xffff01ffc3ff03f0

def z1099 : W := mkw 0x11100fffe24835ed 0x622201fffc4906bd 0x50000fffe0001ffa 0x0a0001fffc0003ff

def z1100 : W := mkw 0x008090a2be1e7bf5 0xa010121457c3cf7e 0x080000000e3cf3e4 0x0100000001c79e7c

def z1101 : W := mkw 0x177f6f5d40020010 0x82efedeba8004002 0xf7ffffffe003001b 0xfefffffffc006003

def z1102 : W := mkw 0x26eff0001db7c000 0x04ddfe0003b6f800 0xaffe00001fffe004 0xf5ffc00003fffc00

def z1103 : W := mkw 0x09100feba2483fef 0x612201fd744907fd 0x50000fffe0001ffa 0x0a0001fffc0003ff

def z1104 : W := mkw 0x0032450980c1a428 0x400648a130183485 0xf0764d9991c7ec7b 0xbe0ec9b33238fd8f

def z1105 : W := mkw 0x077f6f4000000000 0x00efede800000000 0xf7ffffe7e0000003 0xfefffffcfc000000

def z1106 : W := mkw 0x176f6a5d40000000 0x02eded4ba8000000 0x978ff3ffe0000003 0xd2f1fe7ffc000000

def z1107 : W := mkw 0x177f6f5d40000000 0x02efedeba8000000 0x67ffffffe0000000 0xecfffffffc000000

def z1108 : W := mkw 0x002240098081a028 0x4004480130103405 0xf8764c1993c7fc7f 0xbf0ec9833278ff8f

def z1109 : W := mkw 0x0cd805a01b681f06 0x019b00b4036d03e0 0xeff80d801ff81f86 0xfdff01b003ff03f0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z8,z9,z3,z4]),(0,[z0,z1,z8,z3,z4,z5,z10])],[(0,[z0,z1,z8,z11,z3,z4,z5]),(0,[z12,z0,z1,z8,z3,z4,z5]),(0,[z0,z13,z1,z8,z9,z3,z4]),(0,[z0,z1,z14,z8,z3,z4,z5])],[(0,[z15,z0,z1,z8,z3,z4,z5]),(1,[z16,z1,z8,z3,z4,z17]),(0,[z0,z1,z8,z3,z4,z18,z5]),(0,[z0,z1,z8,z3,z4,z19,z5]),(1,[z0,z1,z8,z4,z20,z5])],[(0,[z21,z1,z8,z22,z3,z4,z5]),(0,[z0,z1,z8,z23,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z24,z5]),(0,[z0,z25,z1,z8,z3,z4,z5]),(0,[z0,z26,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z27,z4,z28,z5]),(0,[z0,z1,z29,z8,z3,z4,z5])],[(0,[z0,z1,z8,z30,z3,z4,z5]),(0,[z16,z0,z1,z8,z3,z4,z17]),(0,[z0,z1,z8,z3,z31,z4,z5]),(0,[z0,z32,z1,z8,z27,z4,z5]),(0,[z0,z1,z8,z3,z4,z33,z5])],[(0,[z0,z1,z34,z8,z3,z4,z5]),(1,[z35,z1,z8,z3,z36,z5]),(0,[z0,z37,z1,z8,z3,z4,z5])],[(0,[z38,z0,z39,z8,z3,z4,z5]),(0,[z0,z1,z40,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z41,z5]),(0,[z0,z42,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z43,z44,z4,z5])]],
   [[(0,[z0,z42,z8,z3,z4,z5,z45]),(0,[z0,z42,z1,z8,z46,z3,z4]),(0,[z0,z1,z8,z3,z4,z47,z5]),(0,[z0,z48,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z49,z3,z4,z50])],[(0,[z51,z52,z1,z8,z3,z4,z5]),(0,[z0,z1,z53,z8,z3,z4,z5]),(0,[z0,z1,z54,z8,z3,z4,z5]),(0,[z0,z8,z55,z3,z27,z4,z5]),(0,[z0,z1,z8,z3,z56,z4,z5]),(0,[z57,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z58,z4,z5]),(0,[z59,z0,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z60,z4,z5]),(0,[z0,z1,z61,z8,z3,z4,z5]),(0,[z0,z13,z8,z3,z4,z33,z5]),(0,[z0,z1,z8,z62,z3,z4,z5]),(0,[z0,z1,z8,z63,z3,z4,z5]),(0,[z0,z1,z8,z3,z64,z4,z5])],[(0,[z52,z0,z1,z8,z4,z28,z5]),(0,[z65,z66,z1,z8,z3,z4,z5]),(0,[z0,z67,z1,z8,z3,z4,z5])],[(0,[z68,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z69,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z70,z5])],[(0,[z71,z0,z1,z22,z3,z4,z5]),(1,[z71,z1,z2,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z72]),(0,[z0,z73,z1,z8,z3,z74,z5]),(0,[z0,z1,z8,z75,z3,z4,z5])],[(0,[z0,z1,z76,z8,z3,z4,z5]),(0,[z0,z1,z8,z43,z77,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z78]),(0,[z35,z0,z1,z8,z3,z79,z5]),(0,[z0,z1,z8,z3,z80,z4,z5]),(1,[z0,z1,z8,z49,z3,z81]),(0,[z0,z1,z8,z82,z4,z83,z5])],[(0,[z0,z1,z84,z8,z3,z4,z5]),(0,[z0,z1,z85,z8,z3,z4,z5]),(0,[z0,z1,z8,z86,z3,z4,z5]),(0,[z0,z1,z87,z8,z3,z4,z5]),(0,[z0,z1,z88,z8,z3,z4,z50])]],
   [[(0,[z0,z1,z8,z3,z89,z4,z5]),(0,[z0,z1,z8,z3,z3,z4,z5]),(0,[z0,z90,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z91,z4,z5]),(0,[z0,z1,z8,z92,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z93,z5]),(0,[z0,z1,z8,z94,z3,z4,z5])],[(0,[z0,z1,z8,z3,z95,z4,z5]),(0,[z0,z1,z8,z3,z96,z4,z5]),(0,[z0,z1,z8,z3,z4,z97,z5]),(0,[z0,z1,z8,z43,z3,z98,z5]),(0,[z0,z99,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z100,z6]),(0,[z0,z1,z101,z3,z102,z4,z5])],[(0,[z0,z1,z8,z3,z4,z103,z5]),(0,[z0,z1,z8,z3,z4,z104,z5])],[(0,[z105,z0,z1,z8,z3,z4,z5]),(0,[z0,z106,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z107,z3,z4,z5]),(0,[z0,z1,z8,z108,z3,z4,z5]),(0,[z109,z0,z1,z8,z3,z4,z5]),(0,[z110,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z111,z3,z4,z5])],[(1,[z0,z1,z8,z3,z4,z41]),(0,[z112,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z113,z3,z4,z5])],[(0,[z0,z1,z76,z8,z22,z3,z5]),(0,[z114,z0,z1,z8,z3,z4,z5]),(0,[z115,z0,z1,z8,z3,z4,z5]),(0,[z0,z42,z1,z8,z9,z3,z4]),(0,[z0,z1,z8,z9,z3,z4,z81])],[(0,[z0,z1,z116,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z117,z4,z5]),(0,[z0,z32,z1,z8,z3,z4,z5]),(1,[z0,z1,z8,z3,z118,z5]),(0,[z119,z0,z1,z8,z3,z4,z5]),(1,[z0,z8,z3,z4,z5,z120])]],
   [[(0,[z7,z0,z1,z8,z3,z4,z100]),(0,[z0,z1,z8,z121,z3,z4,z5])],[(0,[z71,z21,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z122,z4,z5]),(1,[z0,z1,z8,z3,z123,z5]),(0,[z0,z124,z125,z8,z3,z4,z5]),(0,[z0,z1,z126,z3,z27,z4,z5]),(0,[z0,z1,z127,z8,z4,z28,z5]),(1,[z0,z1,z8,z3,z4,z128]),(0,[z129,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z130,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z131,z5]),(0,[z1,z2,z8,z22,z3,z4,z5]),(0,[z132,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z133,z3,z134,z4]),(0,[z38,z0,z135,z8,z3,z4,z5])],[(0,[z35,z0,z1,z8,z3,z36,z5]),(0,[z0,z1,z8,z3,z4,z136,z5]),(0,[z0,z1,z8,z137,z3,z4,z5]),(0,[z0,z13,z1,z8,z138,z4,z5])],[(0,[z0,z1,z8,z133,z3,z4,z5]),(0,[z0,z1,z8,z3,z139,z4,z5])],[(0,[z0,z1,z140,z8,z3,z4,z5]),(0,[z0,z1,z8,z55,z134,z4,z5]),(0,[z0,z1,z8,z141,z3,z134,z5]),(0,[z38,z0,z1,z8,z3,z4,z5]),(0,[z142,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z143,z4,z5]),(1,[z0,z1,z8,z43,z44,z5]),(0,[z0,z1,z144,z8,z3,z4,z5])],[(0,[z0,z145,z8,z3,z4,z146,z5]),(1,[z0,z147,z8,z3,z4,z5]),(0,[z7,z0,z1,z8,z3,z4,z17]),(0,[z0,z1,z148,z8,z3,z4,z5])],[(0,[z0,z1,z149,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z150,z4,z5]),(0,[z0,z1,z8,z151,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z79,z5])]],
   [[(0,[z0,z1,z8,z3,z4,z5,z152]),(0,[z0,z1,z8,z3,z36,z4,z5]),(0,[z0,z1,z8,z55,z102,z4,z5]),(0,[z0,z1,z8,z3,z153,z4,z5]),(0,[z0,z1,z8,z154,z3,z4,z5]),(0,[z0,z1,z8,z155,z3,z4,z5])],[(1,[z0,z1,z8,z3,z156,z5]),(0,[z157,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z158,z3,z4,z5]),(0,[z0,z1,z8,z46,z3,z4,z81])],[(0,[z159,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z160,z3,z4,z5]),(0,[z0,z1,z161,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z82,z4,z79])],[(0,[z0,z1,z8,z3,z4,z5,z162]),(0,[z0,z1,z8,z3,z4,z163,z5])],[(0,[z0,z164,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z165,z3,z27,z4]),(1,[z0,z1,z8,z3,z166,z5]),(1,[z0,z1,z8,z3,z4,z167])],[(0,[z0,z168,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z169,z3,z4,z5]),(0,[z0,z1,z8,z170,z3,z98,z5]),(0,[z0,z1,z8,z3,z82,z4,z81])],[(0,[z145,z1,z171,z8,z3,z4,z5]),(0,[z172,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z173,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z174,z5])],[(0,[z0,z1,z8,z3,z4,z175,z5]),(0,[z0,z1,z8,z3,z4,z167,z5])]],
   [[(0,[z176,z0,z73,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z177,z4,z5]),(1,[z0,z1,z8,z170,z98,z5])],[(0,[z0,z1,z178,z8,z3,z4,z5]),(0,[z0,z124,z1,z125,z3,z4,z5]),(0,[z0,z1,z8,z46,z27,z4,z5]),(1,[z0,z1,z8,z165,z3,z4]),(0,[z0,z1,z8,z179,z82,z4,z5])],[(0,[z180,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z134,z27,z4,z5]),(0,[z0,z1,z8,z181,z3,z4,z5]),(0,[z182,z0,z1,z8,z3,z4,z5])],[(0,[z1,z171,z8,z22,z3,z4,z5]),(0,[z0,z1,z8,z183,z3,z4,z5]),(0,[z0,z1,z8,z184,z3,z5,z17]),(0,[z0,z1,z8,z3,z4,z185,z5]),(0,[z0,z1,z8,z3,z186,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z187])],[(0,[z0,z145,z1,z8,z3,z4,z5]),(0,[z188,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z189,z8,z3,z4,z5])],[(0,[z0,z1,z190,z8,z3,z4,z5])],[(1,[z191,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z192,z4,z5]),(0,[z0,z1,z127,z8,z101,z4,z5]),(0,[z0,z1,z193,z194,z3,z4,z5]),(0,[z0,z1,z195,z8,z3,z4,z50])],[(0,[z196,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z197,z4,z5]),(0,[z0,z1,z8,z3,z198,z4,z5]),(0,[z0,z1,z8,z49,z3,z4,z81])]],
   [[(0,[z0,z1,z199,z8,z3,z4,z5]),(0,[z0,z1,z8,z200,z3,z4,z5]),(0,[z0,z1,z8,z4,z98,z28,z5])],[(0,[z0,z1,z201,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z45,z6])],[(0,[z0,z1,z8,z3,z4,z202,z5]),(0,[z0,z124,z1,z8,z3,z4,z5]),(0,[z65,z0,z1,z8,z203,z4,z5]),(0,[z0,z1,z204,z8,z3,z4,z5]),(0,[z205,z0,z1,z8,z3,z4,z5])],[(1,[z0,z1,z8,z206,z4,z5]),(0,[z38,z0,z1,z8,z3,z4,z78]),(1,[z0,z1,z207,z3,z4,z5]),(0,[z0,z1,z207,z8,z3,z4,z5]),(0,[z65,z0,z1,z8,z3,z208,z5]),(0,[z0,z209,z1,z8,z3,z4,z5]),(1,[z0,z32,z8,z55,z4,z5]),(0,[z0,z1,z210,z8,z3,z4,z5]),(0,[z0,z1,z211,z8,z3,z4,z5]),(0,[z0,z1,z8,z212,z3,z4,z5])],[(0,[z0,z1,z29,z8,z101,z4,z5]),(0,[z0,z1,z193,z8,z3,z150,z5]),(0,[z0,z1,z8,z3,z4,z5,z213])],[(0,[z214,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z6])],[(0,[z0,z1,z215,z8,z3,z4,z5]),(0,[z0,z1,z8,z216,z3,z4,z5]),(0,[z0,z1,z8,z3,z217,z4,z5]),(0,[z0,z218,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z219,z3,z4,z5]),(0,[z0,z1,z8,z3,z203,z4,z5]),(0,[z65,z0,z1,z8,z3,z4,z41]),(0,[z0,z1,z8,z3,z4,z5,z220])]],
   [[(0,[z71,z196,z1,z8,z3,z4,z5]),(0,[z0,z1,z221,z8,z3,z4,z5]),(0,[z0,z1,z199,z8,z22,z3,z5]),(0,[z0,z1,z8,z3,z4,z5,z222]),(0,[z0,z1,z223,z8,z3,z4,z5])],[(0,[z21,z0,z1,z8,z3,z4,z224]),(0,[z0,z1,z8,z3,z4,z225,z5]),(0,[z0,z1,z8,z3,z138,z4,z5]),(0,[z0,z1,z8,z226,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z83,z5])],[(0,[z227,z0,z1,z8,z3,z4,z5]),(0,[z228,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z50,z17]),(0,[z0,z1,z8,z3,z229,z4,z5]),(0,[z0,z1,z8,z3,z4,z230,z5]),(0,[z0,z1,z8,z3,z231,z4,z5]),(0,[z0,z1,z8,z3,z232,z4,z5])],[(1,[z0,z1,z40,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z233,z5])],[(0,[z234,z0,z1,z8,z3,z4,z5]),(0,[z0,z235,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z236,z4,z5])],[(0,[z0,z1,z8,z3,z4,z237,z5]),(0,[z238,z0,z1,z8,z3,z4,z5]),(1,[z0,z1,z8,z141,z3,z5]),(0,[z0,z1,z8,z184,z3,z4,z5]),(0,[z0,z1,z8,z3,z239,z4,z5]),(0,[z240,z0,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z241,z4,z5]),(0,[z0,z1,z242,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z243,z5]),(0,[z0,z1,z8,z3,z4,z244,z5]),(0,[z245,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z98,z5]),(0,[z0,z1,z246,z8,z3,z4,z5])],[(1,[z0,z1,z8,z247,z4,z5]),(0,[z0,z1,z8,z3,z4,z248,z5]),(0,[z0,z66,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z249]),(0,[z0,z1,z8,z3,z82,z4,z5])]],
   [[(0,[z0,z1,z8,z3,z4,z5,z250]),(0,[z0,z251,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z252,z3,z4,z5]),(0,[z0,z1,z8,z3,z150,z146,z5]),(0,[z253,z0,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z33,z6])],[(0,[z38,z1,z8,z3,z4,z254,z5]),(0,[z0,z1,z255,z8,z3,z4,z5])],[(0,[z0,z256,z1,z8,z3,z4,z5]),(0,[z0,z1,z257,z8,z3,z4,z5]),(0,[z16,z1,z8,z3,z4,z5,z17])],[(0,[z0,z125,z8,z258,z3,z4,z5]),(0,[z0,z1,z8,z3,z259,z4,z5]),(0,[z0,z260,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z261,z5]),(0,[z0,z1,z262,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z263,z4,z5]),(0,[z0,z1,z8,z3,z4,z264,z5])],[(0,[z0,z1,z8,z3,z265,z4,z5]),(1,[z0,z1,z252,z3,z4,z5]),(0,[z0,z1,z266,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z267])],[(0,[z268,z0,z1,z8,z3,z4,z5]),(0,[z51,z0,z1,z8,z134,z4,z5])]],
   [[(0,[z269,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z270,z5]),(0,[z0,z1,z8,z3,z4,z5,z271]),(0,[z0,z1,z8,z272,z3,z4,z5])],[(0,[z273,z0,z1,z8,z3,z4,z5]),(1,[z0,z1,z8,z274,z4,z5]),(0,[z0,z1,z8,z46,z9,z4,z5])],[(0,[z0,z1,z8,z3,z4,z275,z5]),(0,[z21,z0,z1,z8,z3,z4,z5]),(0,[z0,z276,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z277,z3,z4,z5]),(0,[z0,z1,z8,z278,z3,z4,z5])],[(0,[z0,z1,z193,z8,z3,z4,z5])],[(0,[z0,z1,z8,z279,z3,z4,z5])],[(0,[z0,z1,z280,z8,z3,z4,z5]),(1,[z0,z39,z8,z3,z4,z5]),(0,[z0,z1,z8,z43,z3,z4,z5])],[],[(0,[z0,z281,z1,z8,z3,z4,z5]),(1,[z0,z1,z76,z8,z3,z5]),(0,[z65,z0,z1,z8,z3,z4,z282]),(1,[z0,z1,z277,z3,z4,z5]),(0,[z0,z1,z283,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z284])]],
   [[(0,[z65,z0,z1,z8,z3,z285,z5]),(0,[z0,z1,z8,z286,z3,z4,z5]),(0,[z0,z1,z88,z8,z3,z4,z5])],[(0,[z51,z0,z147,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z287,z4,z5]),(0,[z288,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z289,z3,z4,z5])],[(1,[z0,z1,z8,z3,z4,z224]),(0,[z0,z1,z8,z3,z4,z5,z290]),(0,[z0,z124,z1,z101,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z291]),(0,[z0,z1,z8,z3,z4,z292,z5]),(0,[z0,z1,z8,z4,z20,z5,z6])],[(0,[z0,z1,z8,z77,z4,z98,z5]),(0,[z293,z0,z1,z8,z3,z4,z5]),(1,[z0,z1,z8,z9,z4,z28])],[(1,[z0,z1,z8,z4,z294,z5]),(0,[z0,z295,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z296,z4,z5]),(0,[z0,z1,z8,z297,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z298]),(0,[z0,z1,z8,z9,z3,z4,z28]),(0,[z0,z299,z1,z8,z3,z4,z5])],[(0,[z0,z1,z300,z8,z3,z4,z5]),(0,[z0,z1,z8,z9,z3,z4,z79])],[(0,[z38,z0,z1,z8,z170,z3,z5]),(0,[z65,z0,z1,z127,z3,z4,z5]),(0,[z0,z8,z3,z4,z5,z120,z6])]],
   [[],[],[(0,[z301,z0,z1,z8,z3,z4,z5]),(0,[z65,z0,z1,z8,z302,z4,z5]),(0,[z0,z1,z8,z27,z102,z4,z5]),(0,[z0,z1,z8,z3,z303,z4,z5]),(0,[z0,z1,z8,z3,z4,z304,z5]),(0,[z0,z305,z1,z8,z3,z4,z5])],[(0,[z51,z1,z8,z3,z134,z4,z5])],[(0,[z306,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z307,z3,z4,z5]),(0,[z0,z1,z8,z101,z55,z4,z5]),(0,[z0,z1,z8,z46,z55,z4,z5]),(0,[z0,z1,z308,z8,z3,z4,z5]),(0,[z0,z309,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z310,z5]),(0,[z0,z1,z311,z8,z3,z4,z5]),(0,[z0,z1,z194,z8,z3,z150,z5]),(0,[z0,z1,z8,z312,z3,z4,z5])],[(0,[z313,z0,z1,z8,z3,z4,z5]),(0,[z21,z0,z1,z22,z3,z4,z5]),(0,[z52,z0,z1,z8,z134,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z120]),(0,[z0,z1,z8,z314,z3,z4,z5])],[(0,[z0,z1,z193,z22,z3,z4,z5]),(0,[z0,z1,z315,z8,z3,z4,z5]),(0,[z0,z1,z8,z316,z3,z4,z5])]],
   [[(0,[z0,z1,z317,z8,z3,z4,z5]),(0,[z0,z1,z8,z46,z3,z4,z28])],[(1,[z0,z1,z199,z8,z3,z5]),(0,[z0,z1,z8,z318,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z319,z5]),(0,[z0,z1,z8,z3,z123,z5,z17]),(0,[z0,z1,z8,z320,z3,z4,z5]),(0,[z0,z1,z8,z170,z3,z4,z5]),(0,[z0,z1,z8,z46,z3,z4,z79])],[(0,[z0,z147,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z321,z3,z4,z5]),(0,[z0,z1,z29,z8,z4,z28,z5])],[(1,[z0,z1,z8,z3,z4,z5]),(0,[z0,z124,z1,z258,z3,z4,z5])],[(0,[z0,z322,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z323,z3,z4,z5]),(0,[z0,z1,z324,z8,z3,z4,z5])],[(0,[z16,z0,z1,z207,z3,z4,z5]),(0,[z0,z1,z8,z3,z325,z4,z5])],[(0,[z71,z1,z171,z8,z3,z4,z5]),(0,[z38,z0,z1,z8,z181,z4,z5]),(0,[z0,z1,z8,z326,z3,z4,z5]),(1,[z0,z1,z8,z179,z4,z5])],[(0,[z0,z145,z1,z8,z3,z327,z5]),(0,[z0,z1,z22,z3,z4,z328,z5]),(0,[z0,z1,z8,z3,z4,z5,z329]),(0,[z0,z1,z8,z330,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z331,z5]),(1,[z176,z0,z8,z3,z74,z5]),(0,[z0,z1,z8,z332,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z333,z5]),(0,[z0,z1,z8,z3,z4,z334,z5]),(0,[z0,z1,z8,z3,z4,z335,z5])]],
   [[(0,[z0,z1,z8,z3,z4,z5,z17]),(0,[z0,z1,z8,z3,z4,z5,z336]),(0,[z0,z337,z1,z8,z3,z4,z5])],[(0,[z0,z1,z171,z8,z3,z4,z5]),(0,[z338,z0,z1,z8,z3,z4,z5]),(0,[z71,z1,z2,z8,z3,z4,z5]),(0,[z35,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z339]),(0,[z340,z0,z1,z8,z3,z4,z5])],[(1,[z196,z145,z8,z3,z4,z5]),(0,[z65,z0,z8,z258,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z341,z5]),(0,[z0,z1,z8,z3,z342,z4,z5]),(0,[z0,z1,z8,z3,z343,z4,z5]),(1,[z0,z1,z8,z314,z4,z5])],[(0,[z0,z1,z8,z3,z156,z4,z5]),(0,[z0,z1,z8,z3,z4,z344,z5])],[(0,[z0,z1,z2,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z345,z5]),(0,[z0,z1,z8,z216,z3,z134,z5]),(0,[z0,z1,z8,z55,z3,z4,z5]),(0,[z0,z1,z8,z101,z27,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z346]),(0,[z0,z1,z127,z29,z3,z4,z5]),(0,[z347,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z20,z5]),(0,[z348,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z349,z5])],[(0,[z0,z1,z8,z3,z4,z350,z5]),(0,[z38,z0,z1,z351,z3,z4,z5]),(1,[z38,z1,z8,z3,z254,z5]),(0,[z0,z1,z8,z352,z3,z4,z5]),(0,[z0,z353,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z9,z3,z4,z6])],[(0,[z0,z1,z8,z3,z4,z17,z81]),(0,[z65,z0,z42,z8,z3,z4,z5]),(0,[z176,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z28,z5])],[(0,[z0,z1,z8,z354,z3,z4,z5]),(0,[z355,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z127,z8,z102,z4,z5]),(0,[z0,z1,z195,z8,z3,z4,z5]),(0,[z0,z1,z8,z49,z3,z4,z79])]],
   [[(0,[z71,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z328,z5]),(0,[z0,z1,z8,z55,z77,z4,z5]),(0,[z0,z1,z356,z8,z3,z4,z5]),(0,[z0,z1,z357,z8,z3,z4,z5])],[(0,[z358,z0,z1,z8,z3,z4,z5]),(1,[z0,z1,z194,z3,z328,z5]),(0,[z0,z1,z8,z3,z359,z4,z5])],[(0,[z360,z0,z1,z8,z3,z4,z5]),(0,[z361,z0,z1,z8,z3,z4,z5]),(0,[z21,z0,z1,z8,z3,z4,z152]),(0,[z0,z1,z8,z22,z3,z4,z5])],[(0,[z362,z0,z1,z8,z3,z4,z5]),(0,[z0,z363,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z9,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z364,z5])],[(0,[z0,z365,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z366,z5]),(0,[z0,z1,z194,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z367,z5])],[(0,[z0,z368,z1,z8,z3,z4,z5]),(0,[z0,z1,z29,z8,z102,z4,z5])],[(0,[z369,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z370,z5]),(0,[z0,z1,z8,z3,z4,z5,z371]),(0,[z0,z1,z193,z8,z3,z328,z5])],[(0,[z0,z1,z8,z372,z3,z4,z5]),(0,[z0,z1,z8,z373,z3,z4,z5]),(0,[z0,z1,z8,z3,z374,z4,z5]),(0,[z0,z1,z29,z8,z3,z4,z128]),(0,[z0,z1,z8,z3,z4,z5,z375]),(0,[z0,z1,z8,z9,z3,z4,z249])]],
   [[(1,[z0,z1,z8,z133,z3,z4]),(0,[z16,z0,z1,z252,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z376,z5]),(0,[z0,z42,z1,z8,z3,z118,z5]),(0,[z0,z1,z194,z3,z4,z328,z5]),(0,[z0,z1,z8,z46,z3,z4,z6])],[(0,[z0,z1,z8,z3,z146,z328,z5]),(0,[z0,z1,z8,z377,z3,z4,z5])],[(0,[z378,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z379]),(0,[z380,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z50,z33]),(0,[z0,z381,z1,z8,z3,z4,z5]),(0,[z0,z382,z1,z8,z3,z4,z5])],[(1,[z0,z1,z195,z3,z4,z50])],[(0,[z0,z8,z3,z74,z4,z146,z5]),(0,[z0,z1,z383,z8,z3,z4,z5]),(0,[z0,z384,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z82,z4,z6])],[(0,[z0,z1,z8,z3,z4,z5,z385]),(0,[z0,z1,z8,z3,z4,z50,z45])],[(0,[z0,z1,z8,z101,z3,z4,z5]),(0,[z0,z1,z386,z8,z3,z4,z5]),(0,[z0,z1,z8,z46,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z387,z5]),(0,[z0,z1,z8,z3,z4,z5,z388]),(0,[z0,z1,z8,z3,z389,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z282]),(0,[z0,z1,z8,z3,z4,z5,z390])]],
   [[(0,[z0,z1,z8,z391,z3,z4,z5])],[(0,[z105,z1,z171,z8,z3,z4,z5]),(0,[z0,z1,z8,z392,z3,z4,z5]),(0,[z0,z1,z8,z3,z74,z4,z5]),(0,[z0,z393,z1,z8,z3,z4,z5]),(0,[z0,z394,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z102,z4,z5]),(0,[z0,z1,z8,z395,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z396,z5]),(0,[z0,z1,z8,z3,z4,z5,z397])],[(0,[z398,z0,z1,z8,z3,z4,z5]),(0,[z38,z0,z1,z8,z3,z254,z5]),(0,[z38,z0,z1,z8,z3,z146,z5]),(0,[z0,z1,z8,z399,z3,z4,z5]),(1,[z0,z73,z8,z3,z146,z5]),(0,[z0,z1,z29,z8,z3,z4,z167]),(0,[z0,z1,z8,z3,z4,z5,z400]),(0,[z0,z1,z8,z46,z3,z4,z249])],[(0,[z0,z401,z1,z8,z3,z4,z5]),(0,[z0,z1,z195,z22,z3,z4,z5]),(0,[z402,z0,z1,z8,z3,z4,z5]),(1,[z0,z1,z8,z216,z3,z5]),(0,[z0,z1,z403,z8,z3,z4,z5])],[(0,[z404,z0,z1,z8,z3,z4,z5])],[(0,[z405,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z406,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z407,z5]),(0,[z0,z42,z1,z8,z3,z166,z5]),(0,[z0,z1,z408,z8,z3,z4,z5])],[(0,[z0,z1,z8,z49,z3,z4,z6]),(0,[z0,z1,z8,z3,z4,z5,z409])],[(0,[z0,z410,z1,z8,z3,z4,z5]),(1,[z65,z0,z258,z3,z4,z5]),(0,[z411,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z412,z5]),(1,[z0,z1,z29,z101,z4,z5]),(0,[z0,z1,z8,z3,z44,z4,z5])]],
   [[(0,[z38,z0,z1,z193,z8,z3,z5]),(0,[z0,z1,z8,z3,z4,z413,z5])],[(0,[z0,z1,z8,z3,z4,z79,z100]),(0,[z0,z73,z8,z3,z4,z146,z5]),(0,[z414,z0,z1,z8,z3,z4,z5])],[(0,[z415,z0,z1,z8,z3,z4,z5]),(0,[z416,z0,z1,z8,z3,z4,z5]),(0,[z1,z8,z3,z36,z4,z254,z5]),(0,[z0,z1,z417,z8,z3,z4,z5]),(0,[z0,z418,z1,z8,z3,z4,z5])],[(1,[z0,z1,z8,z3,z4,z152]),(0,[z35,z0,z1,z8,z3,z146,z5]),(0,[z0,z1,z8,z165,z3,z4,z5]),(0,[z0,z1,z8,z46,z43,z4,z5])],[(0,[z0,z1,z419,z8,z3,z4,z5]),(0,[z0,z1,z8,z49,z3,z4,z5]),(0,[z0,z420,z1,z8,z3,z4,z5]),(0,[z0,z1,z421,z8,z3,z4,z5]),(1,[z0,z1,z8,z4,z83,z5])],[(0,[z0,z1,z8,z77,z27,z4,z5]),(0,[z35,z1,z8,z3,z36,z4,z5]),(1,[z0,z124,z125,z3,z4,z5]),(0,[z0,z422,z1,z8,z27,z4,z5]),(0,[z0,z1,z423,z8,z3,z4,z5]),(0,[z0,z1,z88,z8,z3,z4,z6]),(0,[z0,z1,z8,z3,z424,z4,z5])],[(0,[z425,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z426,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z79,z17]),(0,[z0,z1,z8,z258,z3,z4,z5]),(0,[z427,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z428,z8,z3,z4,z5]),(0,[z0,z1,z8,z429,z3,z4,z5])]],
   [[(0,[z0,z1,z8,z3,z430,z4,z5]),(0,[z0,z1,z8,z3,z4,z431,z5]),(0,[z105,z0,z171,z8,z3,z4,z5]),(0,[z176,z0,z1,z8,z3,z146,z5]),(0,[z432,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z433,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z5,z434]),(0,[z35,z0,z1,z193,z8,z3,z5]),(0,[z0,z422,z32,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z166,z4,z5]),(0,[z0,z1,z8,z3,z4,z435,z5])],[(0,[z0,z1,z8,z3,z436,z4,z5]),(0,[z0,z1,z8,z3,z437,z4,z5])],[(0,[z0,z1,z8,z438,z3,z4,z5]),(0,[z0,z32,z171,z8,z3,z4,z5]),(0,[z0,z1,z439,z8,z3,z4,z5]),(0,[z52,z1,z8,z77,z3,z4,z5]),(0,[z38,z0,z1,z8,z3,z74,z5]),(0,[z65,z191,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z440,z5]),(0,[z0,z1,z8,z441,z3,z4,z5])],[(0,[z0,z1,z442,z8,z3,z4,z5]),(0,[z0,z1,z443,z8,z3,z4,z5]),(0,[z0,z1,z8,z444,z3,z4,z5])],[(1,[z0,z1,z8,z11,z3,z4]),(0,[z0,z1,z8,z3,z445,z4,z5]),(0,[z0,z1,z8,z446,z3,z4,z5]),(0,[z16,z0,z1,z8,z3,z4,z5]),(0,[z0,z447,z1,z8,z3,z4,z5]),(0,[z448,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z150,z74,z5]),(0,[z449,z0,z1,z8,z3,z4,z5])],[(0,[z105,z196,z1,z8,z3,z4,z5]),(0,[z51,z0,z1,z8,z3,z4,z5]),(0,[z51,z0,z1,z8,z46,z4,z5]),(0,[z0,z1,z8,z3,z4,z450,z5]),(0,[z451,z0,z1,z8,z3,z4,z5]),(0,[z452,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z453,z3,z4,z5])],[(0,[z454,z0,z1,z8,z3,z4,z5]),(1,[z21,z1,z22,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z455,z5]),(1,[z52,z1,z8,z77,z4,z5]),(0,[z0,z1,z456,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z457]),(0,[z0,z73,z1,z8,z3,z4,z5])]],
   [[(0,[z0,z13,z42,z8,z3,z4,z5]),(0,[z0,z1,z195,z3,z4,z50,z5]),(0,[z0,z1,z8,z3,z458,z4,z5])],[(0,[z0,z1,z8,z459,z3,z4,z5]),(0,[z0,z1,z8,z460,z3,z4,z5]),(0,[z0,z1,z195,z88,z3,z4,z5])],[(0,[z51,z0,z1,z8,z77,z4,z5])],[(0,[z0,z1,z8,z3,z4,z5,z461]),(0,[z0,z1,z8,z462,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z463,z5])],[(0,[z0,z1,z8,z3,z464,z4,z5]),(0,[z465,z0,z1,z8,z3,z4,z5]),(0,[z35,z0,z1,z8,z3,z74,z5]),(0,[z0,z1,z8,z3,z466,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z467]),(0,[z0,z1,z8,z3,z4,z468,z5])],[(0,[z0,z1,z8,z3,z206,z4,z5]),(0,[z0,z1,z8,z469,z3,z4,z5]),(0,[z470,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z471,z4,z5]),(0,[z0,z472,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z473,z5]),(0,[z474,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z475,z5])],[(1,[z0,z1,z8,z3,z327,z5]),(0,[z0,z1,z8,z3,z4,z476,z5]),(0,[z0,z1,z8,z477,z3,z4,z5])],[(0,[z478,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z479,z5]),(0,[z0,z1,z8,z3,z4,z5,z480]),(0,[z0,z1,z194,z8,z3,z328,z5]),(0,[z0,z1,z8,z481,z3,z4,z5])]],
   [[(0,[z0,z1,z8,z3,z4,z5,z482]),(0,[z0,z1,z483,z8,z3,z4,z5]),(0,[z0,z1,z8,z484,z3,z4,z5])],[(0,[z0,z485,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z486,z5]),(0,[z0,z1,z487,z8,z3,z4,z5]),(0,[z0,z1,z8,z488,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z489])],[(0,[z196,z145,z1,z8,z3,z4,z5]),(0,[z0,z490,z1,z8,z3,z4,z5]),(0,[z0,z1,z491,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z492]),(0,[z0,z13,z1,z8,z3,z4,z33]),(0,[z0,z1,z493,z8,z3,z4,z5]),(0,[z0,z1,z494,z8,z3,z4,z5]),(0,[z0,z1,z8,z495,z3,z4,z5])],[(1,[z0,z135,z8,z3,z4,z5]),(0,[z35,z0,z1,z8,z170,z3,z5])],[(0,[z0,z1,z8,z3,z4,z496,z5]),(0,[z0,z1,z497,z8,z3,z4,z5]),(0,[z0,z498,z1,z8,z3,z4,z5]),(0,[z191,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z499]),(0,[z0,z500,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z82,z146,z5])],[(0,[z0,z501,z1,z8,z3,z4,z5]),(0,[z0,z39,z1,z8,z3,z4,z5]),(0,[z0,z13,z1,z8,z3,z4,z45]),(0,[z0,z1,z8,z3,z4,z328,z5]),(1,[z0,z502,z8,z3,z4,z5])],[(0,[z503,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z504,z8,z3,z4,z5]),(1,[z0,z1,z127,z102,z4,z5]),(0,[z0,z1,z8,z3,z505,z4,z5])],[(0,[z176,z0,z171,z8,z3,z4,z5]),(0,[z0,z145,z1,z8,z3,z156,z5]),(0,[z0,z1,z8,z3,z506,z4,z5])]],
   [[(0,[z0,z1,z507,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z508])],[(0,[z0,z1,z8,z509,z3,z4,z5]),(0,[z510,z0,z1,z8,z3,z4,z5])],[(0,[z0,z511,z1,z8,z3,z4,z5]),(1,[z0,z1,z8,z3,z4,z512]),(1,[z0,z1,z8,z46,z4,z249])],[(0,[z196,z0,z171,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z513,z5]),(0,[z0,z1,z8,z514,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z45]),(0,[z0,z1,z515,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z516]),(0,[z0,z1,z8,z43,z4,z28,z5])],[(1,[z0,z1,z8,z181,z4,z5]),(0,[z0,z1,z8,z3,z74,z328,z5]),(0,[z0,z1,z195,z8,z3,z4,z6]),(0,[z0,z1,z8,z46,z4,z98,z5])],[(0,[z517,z0,z1,z8,z3,z4,z5]),(0,[z52,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z134,z4,z98,z5]),(0,[z52,z0,z1,z8,z46,z4,z5]),(0,[z0,z1,z8,z3,z518,z4,z5]),(0,[z0,z1,z8,z46,z4,z5,z249])],[(0,[z519,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z520,z5]),(0,[z521,z0,z1,z8,z3,z4,z5]),(0,[z7,z0,z1,z8,z3,z4,z5]),(1,[z7,z1,z8,z3,z4,z100]),(0,[z0,z1,z8,z3,z4,z5,z522]),(0,[z0,z1,z8,z3,z4,z523,z5]),(0,[z0,z1,z8,z3,z4,z5,z128])],[(0,[z0,z1,z8,z3,z4,z524,z5]),(0,[z0,z1,z8,z525,z3,z4,z5])]],
   [[(1,[z105,z171,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z526,z4,z5]),(0,[z0,z1,z8,z527,z3,z4,z5]),(0,[z0,z1,z528,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z529]),(0,[z0,z422,z8,z3,z27,z4,z5]),(0,[z0,z1,z8,z3,z4,z530,z5]),(1,[z0,z1,z8,z3,z82,z79]),(0,[z0,z1,z531,z8,z3,z4,z5])],[(0,[z0,z1,z8,z532,z3,z4,z5]),(0,[z52,z0,z1,z8,z77,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z533]),(0,[z0,z1,z8,z170,z43,z4,z5])],[(0,[z0,z1,z534,z8,z3,z4,z5]),(0,[z38,z0,z1,z40,z3,z4,z5]),(0,[z0,z1,z8,z3,z146,z5,z81]),(1,[z0,z1,z8,z23,z4,z5])],[(0,[z535,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z274,z4,z5]),(0,[z0,z1,z8,z49,z3,z82,z5])],[(0,[z196,z0,z145,z8,z3,z4,z5]),(0,[z38,z0,z1,z8,z3,z4,z524]),(0,[z1,z8,z3,z4,z100,z5,z17]),(0,[z0,z502,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z536,z5]),(0,[z0,z1,z8,z537,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z327,z5]),(0,[z538,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z82,z74,z5])],[(0,[z0,z1,z8,z3,z539,z4,z5]),(0,[z0,z1,z8,z3,z285,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z540])],[(0,[z0,z1,z8,z541,z3,z4,z5]),(0,[z0,z542,z1,z8,z3,z4,z5]),(0,[z0,z42,z1,z8,z3,z4,z33]),(0,[z0,z1,z8,z3,z543,z4,z5]),(0,[z544,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z43,z3,z44,z5]),(0,[z0,z1,z8,z3,z4,z545,z5])]],
   [[(0,[z0,z1,z8,z3,z4,z5,z546]),(0,[z0,z1,z8,z3,z4,z547,z5]),(0,[z0,z1,z8,z548,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z549]),(0,[z0,z1,z8,z3,z4,z550,z5]),(0,[z0,z1,z8,z3,z551,z4,z5])],[],[(0,[z552,z0,z1,z8,z3,z4,z5]),(0,[z0,z42,z1,z8,z3,z4,z45]),(0,[z0,z1,z8,z3,z4,z553,z5]),(0,[z0,z1,z8,z3,z79,z5,z81])],[(0,[z0,z1,z8,z3,z4,z100,z81]),(0,[z0,z125,z8,z3,z4,z33,z5]),(0,[z0,z1,z8,z3,z4,z554,z5]),(0,[z0,z1,z8,z3,z27,z4,z5]),(0,[z0,z1,z127,z8,z3,z4,z5]),(0,[z0,z1,z127,z8,z46,z4,z5])],[(0,[z0,z1,z8,z11,z3,z134,z4]),(1,[z0,z1,z8,z3,z4,z78])],[(0,[z0,z1,z8,z555,z3,z4,z5]),(0,[z0,z1,z8,z556,z3,z4,z5]),(0,[z0,z557,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z558,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z294,z5]),(0,[z0,z1,z8,z3,z559,z4,z5])],[(0,[z1,z8,z77,z3,z134,z4,z5]),(0,[z65,z0,z1,z125,z3,z4,z5]),(0,[z560,z0,z1,z8,z3,z4,z5]),(0,[z176,z0,z8,z3,z74,z4,z5])]],
   [[(0,[z38,z0,z1,z8,z274,z4,z5]),(0,[z0,z1,z561,z8,z3,z4,z5]),(0,[z0,z422,z1,z8,z55,z4,z5]),(0,[z0,z1,z8,z3,z4,z562,z5]),(1,[z0,z1,z8,z3,z4,z298]),(0,[z563,z0,z1,z8,z3,z4,z5])],[(0,[z21,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z8,z3,z134,z4,z5]),(0,[z0,z124,z1,z127,z3,z4,z5]),(0,[z0,z1,z29,z8,z46,z4,z5]),(0,[z564,z0,z1,z8,z3,z4,z5])],[(0,[z0,z1,z193,z2,z3,z4,z5]),(0,[z38,z0,z1,z8,z3,z79,z5]),(0,[z0,z1,z565,z8,z3,z4,z5])],[(1,[z0,z280,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z566,z4,z5]),(0,[z0,z1,z567,z8,z3,z4,z5]),(0,[z0,z1,z8,z568,z3,z4,z5]),(0,[z0,z569,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z570,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z5,z571]),(0,[z0,z1,z8,z3,z4,z17,z6]),(0,[z0,z1,z8,z3,z4,z572,z5])],[(0,[z573,z0,z1,z8,z3,z4,z5]),(0,[z0,z574,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z314,z4,z5,z6])],[(0,[z0,z1,z8,z247,z3,z4,z5]),(0,[z0,z1,z8,z575,z3,z4,z5]),(0,[z0,z1,z8,z3,z576,z4,z5])]],
   [[(0,[z0,z1,z577,z8,z3,z4,z5]),(0,[z0,z1,z8,z578,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z579]),(0,[z65,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z580,z3,z4,z5])],[(0,[z0,z1,z277,z3,z27,z4,z5]),(0,[z581,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z193,z3,z150,z4,z5])],[(0,[z0,z1,z8,z582,z3,z4,z5]),(0,[z0,z1,z8,z3,z583,z4,z5]),(1,[z0,z1,z8,z184,z3,z5]),(0,[z7,z1,z8,z3,z4,z100,z5]),(0,[z0,z1,z8,z55,z4,z28,z5]),(0,[z0,z1,z8,z3,z4,z50,z5]),(1,[z0,z1,z88,z3,z4,z6])],[(0,[z0,z171,z8,z3,z4,z146,z5]),(0,[z38,z35,z1,z8,z3,z4,z5]),(0,[z38,z0,z1,z194,z8,z3,z5]),(0,[z0,z1,z8,z3,z4,z584,z5]),(0,[z0,z1,z8,z170,z3,z44,z5])],[],[(1,[z0,z1,z8,z203,z4,z5]),(0,[z0,z1,z585,z8,z3,z4,z5]),(0,[z0,z1,z586,z8,z3,z4,z5]),(0,[z587,z0,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z588,z5]),(0,[z35,z0,z1,z8,z3,z254,z5]),(0,[z0,z1,z8,z3,z4,z589,z5]),(1,[z0,z1,z8,z3,z208,z5]),(0,[z0,z1,z8,z3,z44,z4,z512])],[(0,[z590,z0,z1,z8,z3,z4,z5]),(0,[z38,z0,z1,z8,z3,z36,z5]),(0,[z0,z591,z1,z8,z3,z4,z5]),(1,[z0,z1,z8,z138,z4,z5]),(0,[z0,z1,z592,z8,z3,z4,z5]),(0,[z0,z1,z8,z593,z3,z4,z5])]],
   [[],[(0,[z0,z1,z8,z3,z4,z224,z5]),(0,[z0,z1,z8,z3,z4,z594,z5]),(0,[z0,z1,z8,z302,z3,z4,z5]),(0,[z0,z595,z1,z8,z3,z4,z5]),(0,[z0,z1,z596,z8,z3,z4,z5]),(0,[z597,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z9,z4,z28,z5])],[(0,[z0,z1,z8,z219,z4,z5,z17]),(0,[z0,z1,z8,z598,z3,z4,z5]),(0,[z0,z1,z8,z3,z599,z4,z5]),(0,[z0,z1,z8,z170,z4,z98,z5])],[(0,[z0,z1,z600,z8,z3,z4,z5]),(1,[z0,z422,z8,z27,z4,z5]),(0,[z0,z1,z193,z8,z3,z4,z553])],[(0,[z0,z601,z1,z8,z3,z4,z5]),(0,[z35,z0,z1,z194,z8,z3,z5]),(0,[z0,z1,z125,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z602,z4,z5])],[(0,[z0,z603,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z100,z5]),(0,[z0,z1,z604,z8,z3,z4,z5]),(0,[z0,z1,z193,z8,z3,z4,z400]),(0,[z605,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z606,z3,z4,z5])],[(0,[z607,z0,z1,z8,z3,z4,z5])],[(0,[z0,z1,z608,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z609,z4,z5]),(0,[z0,z1,z8,z3,z4,z610,z5])]],
   [[(0,[z0,z1,z8,z3,z611,z4,z5]),(0,[z0,z1,z8,z612,z3,z27,z4]),(0,[z0,z1,z8,z613,z3,z4,z5])],[(0,[z16,z0,z1,z8,z46,z3,z4]),(0,[z0,z32,z8,z55,z3,z4,z5]),(0,[z0,z614,z1,z8,z3,z4,z5]),(0,[z0,z1,z615,z8,z3,z4,z5]),(0,[z0,z616,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z617,z5]),(0,[z0,z1,z8,z618,z3,z4,z5]),(0,[z619,z0,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z620,z4,z5]),(0,[z0,z1,z621,z8,z3,z4,z5])],[(0,[z105,z0,z145,z8,z3,z4,z5]),(0,[z0,z1,z622,z8,z3,z4,z5]),(0,[z0,z1,z623,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z624])],[(0,[z625,z0,z1,z8,z3,z4,z5]),(0,[z7,z16,z1,z8,z3,z4,z5]),(0,[z0,z1,z626,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z5,z627]),(0,[z0,z1,z8,z3,z628,z4,z5]),(0,[z0,z1,z8,z629,z3,z4,z5]),(1,[z0,z1,z8,z612,z3,z4]),(0,[z0,z1,z127,z3,z102,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z81])],[(0,[z0,z32,z145,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z254,z5]),(0,[z0,z1,z8,z3,z4,z146,z5]),(0,[z0,z630,z1,z8,z3,z4,z5])]],
   [[(0,[z65,z0,z8,z3,z4,z33,z5])],[(0,[z0,z1,z8,z3,z631,z4,z5]),(0,[z0,z1,z8,z3,z632,z4,z5]),(0,[z633,z0,z1,z8,z3,z4,z5]),(1,[z0,z13,z8,z3,z4,z33]),(0,[z0,z1,z8,z3,z4,z634,z5]),(0,[z0,z635,z1,z8,z3,z4,z5]),(0,[z0,z1,z29,z101,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z636,z5]),(0,[z0,z1,z8,z3,z637,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z638])],[(0,[z0,z1,z639,z8,z3,z4,z5]),(0,[z0,z1,z8,z77,z3,z4,z5]),(0,[z38,z0,z1,z8,z49,z3,z5]),(0,[z0,z422,z1,z8,z3,z4,z5]),(0,[z640,z0,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z641,z4,z5]),(0,[z642,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z643,z4,z5])],[(0,[z105,z0,z1,z8,z206,z4,z5]),(0,[z0,z644,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z645,z4,z5]),(0,[z0,z1,z8,z3,z4,z646,z5]),(0,[z0,z1,z8,z647,z3,z4,z5]),(0,[z176,z0,z1,z8,z3,z74,z5]),(0,[z0,z1,z8,z3,z4,z648,z5]),(0,[z0,z1,z88,z3,z4,z5,z6]),(0,[z0,z1,z8,z3,z44,z4,z298]),(0,[z0,z1,z8,z4,z28,z5,z249]),(0,[z0,z1,z8,z3,z82,z79,z5])],[(0,[z0,z1,z8,z3,z4,z208,z5]),(0,[z0,z1,z8,z3,z74,z5,z81]),(0,[z0,z1,z8,z3,z649,z4,z5]),(0,[z650,z0,z1,z8,z3,z4,z5])],[(0,[z0,z1,z195,z2,z3,z4,z5])],[(0,[z0,z1,z8,z141,z3,z4,z5]),(0,[z16,z0,z1,z8,z9,z3,z4]),(0,[z0,z1,z8,z3,z4,z5,z651]),(0,[z0,z1,z8,z652,z3,z4,z5])]],
   [[(0,[z196,z1,z8,z22,z3,z4,z5]),(0,[z65,z0,z1,z101,z3,z4,z5]),(0,[z0,z1,z8,z3,z653,z4,z5])],[(0,[z0,z654,z1,z8,z3,z4,z5]),(0,[z38,z0,z1,z8,z43,z3,z5]),(1,[z66,z1,z8,z3,z4,z5]),(0,[z655,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z656,z3,z4,z5]),(0,[z0,z1,z8,z657,z3,z4,z5]),(0,[z658,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z659])],[(0,[z0,z171,z8,z3,z27,z4,z5]),(0,[z0,z1,z135,z8,z3,z4,z5]),(1,[z0,z1,z8,z3,z4,z282]),(0,[z0,z1,z8,z3,z4,z5,z660])],[(0,[z0,z1,z8,z3,z661,z4,z5]),(0,[z35,z0,z1,z8,z49,z3,z5]),(1,[z0,z1,z8,z3,z285,z5]),(0,[z0,z1,z8,z3,z4,z118,z5]),(1,[z0,z1,z8,z3,z4,z553]),(0,[z0,z1,z8,z3,z4,z662,z5])],[(0,[z0,z1,z663,z8,z3,z4,z5]),(1,[z0,z1,z193,z3,z150,z5])],[(0,[z0,z1,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z664,z5]),(0,[z0,z1,z8,z4,z294,z5,z17]),(0,[z0,z1,z8,z3,z4,z123,z5]),(0,[z0,z1,z8,z3,z665,z4,z5]),(1,[z0,z1,z8,z3,z4,z400]),(0,[z0,z1,z8,z666,z3,z4,z5])],[(0,[z0,z42,z125,z8,z3,z4,z5]),(0,[z0,z1,z8,z667,z3,z4,z5]),(0,[z0,z8,z3,z4,z33,z5,z45]),(0,[z0,z668,z1,z8,z3,z4,z5]),(0,[z0,z1,z669,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z5,z670]),(0,[z0,z1,z8,z3,z671,z4,z5]),(0,[z672,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z9,z3,z4,z50]),(0,[z0,z1,z8,z3,z4,z5,z673])]],
   [[(0,[z674,z0,z1,z8,z3,z4,z5]),(0,[z105,z0,z1,z8,z247,z4,z5]),(0,[z0,z1,z8,z675,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z676,z5]),(0,[z0,z1,z8,z49,z3,z5,z81])],[(0,[z0,z1,z8,z3,z677,z4,z5]),(0,[z0,z1,z8,z351,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z50,z100]),(0,[z0,z1,z8,z3,z4,z5,z678])],[(0,[z35,z0,z1,z8,z43,z3,z5]),(0,[z7,z0,z1,z8,z46,z3,z4]),(0,[z0,z1,z679,z8,z3,z4,z5]),(0,[z0,z13,z1,z8,z3,z4,z5]),(0,[z0,z1,z680,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z681,z4,z5])],[(0,[z176,z0,z145,z8,z3,z4,z5]),(0,[z0,z1,z8,z682,z3,z4,z5]),(0,[z0,z1,z8,z3,z683,z4,z5]),(0,[z0,z13,z1,z8,z46,z3,z4]),(0,[z0,z1,z3,z150,z4,z328,z5]),(0,[z0,z684,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z512,z5]),(0,[z0,z1,z8,z685,z3,z4,z5])],[(1,[z51,z1,z8,z134,z4,z5]),(0,[z51,z0,z1,z8,z4,z28,z5])],[(1,[z0,z1,z8,z302,z4,z5]),(0,[z0,z32,z1,z8,z55,z4,z5]),(0,[z0,z1,z8,z3,z686,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z687]),(0,[z0,z1,z3,z4,z50,z5,z6])],[(0,[z51,z0,z280,z8,z3,z4,z5]),(0,[z688,z0,z1,z8,z3,z4,z5]),(1,[z0,z1,z351,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z689,z5])],[(0,[z0,z1,z22,z3,z4,z5,z6]),(0,[z0,z1,z690,z8,z3,z4,z5])]],
   [[(0,[z0,z1,z8,z3,z4,z5,z5])],[(0,[z71,z0,z1,z8,z3,z4,z5]),(0,[z65,z0,z1,z258,z3,z4,z5]),(0,[z0,z691,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z692,z3,z4,z5]),(0,[z0,z1,z8,z693,z3,z4,z5])],[(0,[z0,z145,z8,z3,z27,z4,z5]),(1,[z0,z1,z8,z3,z4,z524]),(0,[z0,z1,z8,z46,z3,z4,z50]),(0,[z0,z1,z8,z179,z3,z4,z5])],[(0,[z65,z0,z124,z8,z3,z4,z5]),(0,[z0,z1,z8,z44,z4,z98,z5])],[(0,[z0,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z694,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z695,z5]),(0,[z696,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z612,z3,z4,z5]),(0,[z0,z73,z1,z8,z3,z146,z5]),(0,[z0,z1,z8,z3,z4,z5,z697]),(0,[z0,z502,z8,z3,z4,z5,z6]),(0,[z0,z1,z698,z8,z3,z4,z5]),(0,[z699,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z700,z4,z5])],[(0,[z0,z1,z8,z3,z4,z701,z5])],[(0,[z0,z1,z8,z43,z134,z4,z5]),(0,[z0,z13,z1,z8,z23,z4,z5]),(0,[z0,z1,z8,z3,z82,z4,z50])],[(0,[z702,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z703,z3,z4,z5]),(0,[z16,z0,z1,z8,z3,z4,z100]),(1,[z0,z1,z8,z219,z4,z5]),(1,[z0,z1,z126,z3,z4,z5]),(0,[z0,z1,z126,z8,z3,z4,z5]),(0,[z0,z1,z8,z704,z3,z4,z5]),(1,[z0,z42,z8,z3,z4,z45]),(0,[z0,z1,z8,z3,z4,z705,z5]),(0,[z0,z1,z8,z3,z706,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[],[(0,[z0,z1,z8,z3,z707,z5]),(0,[z51,z1,z8,z216,z134,z5]),(0,[z0,z1,z708,z3,z4,z5]),(0,[z65,z0,z169,z3,z4,z5]),(0,[z709,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z43,z44,z5])],[(0,[z0,z147,z8,z3,z4,z5])],[(0,[z0,z1,z8,z3,z710,z5]),(0,[z0,z1,z8,z3,z711,z5]),(0,[z38,z1,z8,z3,z712,z5]),(0,[z0,z1,z8,z3,z4,z713])],[(1,[z0,z1,z8,z714,z5])],[(0,[z0,z1,z8,z3,z156,z5]),(0,[z0,z1,z715,z3,z4,z5]),(0,[z71,z1,z716,z3,z4,z5]),(0,[z0,z1,z8,z3,z146,z78]),(0,[z0,z1,z8,z612,z3,z4]),(0,[z0,z32,z8,z717,z4,z5]),(0,[z0,z8,z3,z4,z33,z718])],[(0,[z0,z1,z8,z43,z576,z5])],[(0,[z0,z1,z8,z3,z719,z5]),(0,[z0,z1,z8,z184,z3,z78]),(0,[z16,z1,z8,z657,z3,z4]),(0,[z0,z1,z116,z3,z4,z6]),(0,[z65,z0,z14,z3,z4,z5])]],
   [[(0,[z0,z1,z720,z3,z4,z5]),(0,[z1,z8,z3,z36,z712,z5]),(0,[z0,z1,z8,z721,z4,z5]),(0,[z0,z1,z8,z3,z166,z5]),(0,[z0,z1,z8,z3,z4,z167]),(0,[z0,z1,z8,z3,z722,z5])],[(0,[z0,z39,z40,z3,z4,z5]),(0,[z0,z1,z8,z219,z4,z79]),(0,[z0,z1,z8,z179,z4,z50])],[],[(0,[z0,z1,z723,z3,z4,z5]),(0,[z0,z1,z724,z3,z4,z5]),(0,[z0,z1,z8,z3,z725,z5]),(0,[z0,z1,z8,z726,z4,z5])],[(0,[z196,z145,z8,z3,z156,z5]),(0,[z0,z1,z8,z219,z4,z81]),(0,[z0,z502,z8,z3,z727,z5]),(0,[z0,z1,z8,z170,z98,z5])],[(0,[z0,z1,z8,z728,z4,z5]),(0,[z0,z1,z8,z3,z5,z729]),(0,[z0,z1,z8,z165,z3,z4]),(0,[z0,z1,z8,z3,z4,z730])],[(0,[z696,z1,z8,z134,z4,z5]),(0,[z0,z1,z8,z3,z4,z731])],[(0,[z0,z1,z8,z732,z4,z5]),(0,[z0,z1,z733,z3,z4,z5])]],
   [[(0,[z1,z8,z3,z734,z4,z5]),(0,[z7,z0,z1,z8,z219,z4]),(0,[z0,z8,z3,z4,z5,z735])],[(0,[z0,z1,z8,z3,z4,z736]),(0,[z0,z1,z8,z141,z11,z3]),(0,[z737,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z4,z738,z5]),(0,[z0,z1,z8,z46,z4,z390]),(0,[z0,z1,z8,z3,z4,z739]),(0,[z0,z1,z8,z4,z28,z740])],[(0,[z191,z1,z8,z3,z4,z5]),(0,[z66,z1,z8,z3,z285,z5])],[(0,[z51,z1,z8,z11,z134,z4]),(0,[z0,z1,z8,z717,z4,z5])],[(0,[z0,z1,z8,z3,z4,z741]),(0,[z0,z1,z101,z203,z4,z5]),(0,[z0,z8,z3,z742,z146,z5]),(0,[z0,z13,z8,z23,z4,z33]),(0,[z0,z1,z8,z3,z4,z400]),(0,[z0,z1,z8,z4,z743,z5])],[(0,[z0,z1,z8,z4,z5,z744]),(0,[z0,z1,z8,z745,z4,z5])],[(0,[z0,z1,z8,z3,z74,z78])],[(0,[z0,z644,z8,z27,z4,z5]),(0,[z0,z39,z8,z274,z4,z5]),(0,[z619,z1,z8,z3,z4,z17]),(0,[z0,z32,z8,z55,z4,z5])]],
   [[(0,[z0,z1,z8,z3,z746,z5]),(0,[z747,z1,z8,z3,z4,z5]),(0,[z0,z8,z4,z20,z5,z120]),(0,[z0,z1,z8,z49,z3,z748])],[(0,[z0,z1,z3,z4,z749,z5]),(0,[z0,z750,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z751]),(0,[z0,z1,z8,z3,z4,z752]),(0,[z0,z1,z3,z753,z328,z5])],[(0,[z238,z171,z8,z3,z4,z5]),(0,[z0,z1,z8,z754,z4,z5]),(0,[z0,z1,z8,z3,z748,z81])],[(0,[z51,z1,z8,z134,z4,z5]),(0,[z0,z1,z193,z351,z3,z5]),(0,[z16,z0,z1,z8,z219,z4]),(0,[z0,z1,z8,z3,z4,z755]),(0,[z756,z1,z8,z3,z4,z5]),(0,[z0,z1,z615,z3,z4,z6]),(1,[z0,z1,z8,z3,z748])],[(0,[z451,z145,z8,z3,z4,z5]),(0,[z0,z1,z8,z203,z208,z5]),(0,[z0,z1,z8,z3,z4,z757]),(0,[z0,z1,z3,z150,z753,z5]),(0,[z0,z1,z8,z758,z4,z5]),(0,[z0,z1,z759,z8,z3,z5])],[(0,[z65,z0,z258,z3,z4,z41]),(0,[z0,z1,z663,z3,z4,z6])],[(0,[z0,z1,z8,z3,z4,z760]),(0,[z0,z1,z8,z3,z4,z761]),(0,[z0,z135,z8,z3,z4,z524]),(0,[z0,z1,z8,z170,z274,z5]),(0,[z0,z1,z8,z762,z3,z4]),(0,[z0,z1,z8,z3,z82,z70])],[(0,[z0,z1,z8,z3,z4,z763]),(0,[z0,z1,z40,z3,z4,z5]),(0,[z764,z1,z8,z3,z4,z5]),(0,[z0,z73,z8,z3,z742,z5]),(0,[z0,z1,z29,z765,z4,z5]),(0,[z0,z1,z8,z766,z4,z5])]],
   [[(0,[z0,z1,z8,z3,z229,z79])],[(0,[z0,z1,z8,z767,z3,z4]),(0,[z0,z1,z8,z141,z3,z5]),(0,[z0,z1,z8,z3,z4,z524]),(0,[z0,z1,z8,z3,z4,z768]),(0,[z0,z1,z8,z769,z4,z5]),(0,[z293,z0,z8,z3,z74,z5]),(0,[z0,z1,z29,z101,z4,z128])],[(0,[z0,z1,z8,z3,z742,z5]),(0,[z0,z1,z8,z46,z4,z20]),(0,[z0,z1,z8,z4,z714,z5])],[(0,[z0,z1,z8,z247,z4,z5]),(0,[z0,z1,z8,z770,z4,z5]),(0,[z0,z1,z351,z181,z4,z5]),(0,[z0,z1,z8,z771,z3,z4])],[(0,[z0,z1,z772,z3,z4,z5])],[(0,[z0,z1,z8,z773,z4,z5]),(0,[z0,z1,z8,z774,z4,z5]),(0,[z1,z8,z77,z734,z4,z5]),(0,[z35,z1,z8,z3,z331,z5])],[(0,[z0,z1,z8,z3,z775,z5]),(0,[z0,z776,z8,z3,z4,z5]),(0,[z0,z1,z8,z219,z4,z5]),(0,[z0,z1,z126,z3,z4,z5]),(0,[z0,z26,z8,z27,z4,z5]),(0,[z0,z1,z126,z46,z4,z5])],[(0,[z0,z1,z8,z777,z4,z5]),(0,[z0,z422,z8,z165,z27,z4]),(0,[z0,z502,z8,z3,z778,z5])]],
   [[(0,[z0,z1,z8,z779,z4,z5])],[(0,[z0,z1,z8,z3,z4,z780]),(0,[z0,z1,z2,z3,z4,z152]),(0,[z38,z1,z40,z3,z254,z5]),(0,[z16,z1,z8,z3,z4,z17]),(0,[z0,z8,z3,z4,z33,z282]),(0,[z0,z1,z781,z3,z4,z5])],[(0,[z0,z1,z252,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z782]),(0,[z0,z1,z8,z783,z3,z5]),(0,[z0,z784,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z785]),(0,[z0,z1,z8,z786,z4,z400]),(0,[z0,z1,z8,z46,z4,z624])],[(0,[z0,z1,z8,z9,z518,z4]),(0,[z0,z1,z29,z101,z4,z167])],[(1,[z1,z716,z3,z4,z5]),(0,[z0,z1,z8,z787,z4,z5]),(0,[z0,z1,z8,z274,z4,z5]),(0,[z35,z0,z1,z8,z3,z553])],[(0,[z0,z1,z8,z3,z4,z788]),(0,[z538,z0,z1,z8,z46,z4]),(0,[z0,z1,z8,z46,z4,z467])],[]],
   [[(0,[z0,z1,z8,z789,z4,z5]),(0,[z0,z790,z8,z3,z4,z5]),(0,[z0,z1,z8,z9,z4,z20]),(0,[z0,z1,z8,z681,z98,z5]),(0,[z0,z1,z8,z179,z4,z81])],[(0,[z0,z1,z8,z3,z791,z5]),(0,[z0,z1,z8,z123,z294,z5]),(0,[z0,z13,z8,z138,z4,z33])],[(0,[z0,z1,z8,z792,z4,z5]),(0,[z0,z1,z793,z3,z4,z5]),(0,[z0,z1,z794,z3,z4,z5])],[],[(0,[z0,z1,z8,z3,z795,z5]),(0,[z0,z1,z8,z796,z4,z5]),(0,[z0,z1,z383,z3,z328,z5])],[(0,[z0,z1,z193,z199,z3,z5]),(0,[z0,z1,z40,z3,z4,z78]),(0,[z0,z1,z8,z3,z797,z5]),(0,[z0,z1,z8,z3,z4,z798]),(0,[z0,z1,z8,z3,z799,z5]),(0,[z0,z1,z8,z49,z3,z81])],[(0,[z0,z800,z8,z3,z4,z5]),(0,[z1,z8,z3,z4,z768,z5]),(0,[z0,z8,z3,z717,z4,z5])],[(0,[z0,z1,z8,z801,z3,z5]),(0,[z0,z1,z8,z133,z27,z4]),(0,[z66,z1,z8,z203,z4,z5]),(0,[z0,z1,z3,z4,z802,z5])]],
   [[(0,[z0,z1,z3,z803,z4,z5]),(0,[z0,z1,z8,z804,z4,z5]),(0,[z0,z1,z8,z3,z4,z805]),(0,[z0,z1,z8,z3,z4,z806]),(0,[z57,z1,z22,z3,z4,z5]),(0,[z0,z1,z8,z4,z294,z5]),(0,[z66,z1,z8,z3,z208,z5]),(0,[z0,z1,z8,z203,z4,z282]),(0,[z807,z1,z8,z3,z4,z5])],[(0,[z0,z808,z8,z3,z4,z5]),(0,[z0,z1,z8,z203,z285,z5]),(0,[z0,z1,z8,z3,z208,z282]),(0,[z0,z1,z8,z809,z3,z4])],[(0,[z0,z1,z8,z3,z4,z810]),(0,[z0,z1,z8,z811,z4,z5]),(0,[z0,z1,z8,z3,z812,z5]),(0,[z0,z1,z8,z813,z4,z5])],[(0,[z38,z39,z8,z3,z254,z5])],[(0,[z0,z1,z814,z3,z4,z5]),(0,[z0,z1,z8,z815,z4,z5]),(0,[z66,z1,z8,z3,z4,z41]),(0,[z0,z1,z483,z3,z4,z50]),(0,[z816,z1,z8,z3,z4,z5])],[(0,[z1,z8,z3,z4,z100,z768]),(0,[z0,z1,z8,z3,z4,z817]),(0,[z0,z1,z585,z3,z150,z5])],[(0,[z0,z1,z818,z8,z4,z5]),(0,[z0,z1,z8,z3,z4,z819]),(0,[z0,z1,z8,z3,z4,z820]),(0,[z0,z1,z194,z3,z753,z5])],[(0,[z0,z1,z8,z821,z4,z5]),(0,[z0,z1,z351,z3,z146,z5]),(0,[z0,z1,z8,z3,z4,z822])]],
   [[(0,[z0,z1,z8,z823,z4,z5]),(0,[z824,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z128]),(0,[z0,z1,z8,z46,z4,z128]),(1,[z0,z1,z3,z4,z825])],[(0,[z0,z1,z8,z826,z206,z4]),(0,[z0,z1,z8,z3,z4,z827]),(0,[z0,z8,z3,z4,z5,z828])],[(0,[z1,z2,z716,z3,z4,z5])],[(0,[z0,z1,z829,z3,z4,z5]),(0,[z0,z1,z8,z274,z4,z78]),(0,[z0,z337,z8,z3,z146,z5])],[(0,[z0,z1,z8,z302,z208,z5])],[(0,[z0,z1,z8,z3,z830,z5]),(0,[z0,z1,z831,z3,z4,z5]),(0,[z7,z1,z8,z3,z4,z768]),(0,[z0,z1,z8,z3,z82,z486]),(0,[z1,z8,z3,z4,z5,z832])],[(0,[z0,z1,z833,z3,z4,z5]),(0,[z0,z125,z3,z4,z5,z371])],[(0,[z834,z1,z8,z3,z4,z5])]],
   [[(0,[z0,z1,z835,z8,z3,z5]),(0,[z0,z1,z2,z3,z4,z400]),(0,[z0,z280,z8,z4,z28,z5]),(0,[z0,z1,z8,z133,z55,z4]),(0,[z0,z1,z8,z46,z4,z540]),(0,[z0,z1,z8,z43,z44,z512])],[(0,[z109,z1,z8,z77,z4,z5]),(0,[z0,z1,z8,z836,z4,z5])],[(0,[z0,z1,z8,z3,z837,z5]),(0,[z0,z1,z8,z46,z4,z546]),(0,[z0,z1,z8,z179,z4,z5]),(0,[z0,z1,z8,z714,z98,z5])],[(0,[z0,z1,z8,z3,z838,z5]),(0,[z0,z1,z8,z839,z4,z5])],[(0,[z0,z1,z840,z3,z4,z5]),(0,[z841,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z842])],[(0,[z0,z1,z8,z3,z843,z5]),(0,[z16,z1,z8,z184,z3,z17]),(0,[z844,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z845]),(0,[z0,z1,z88,z4,z20,z6])],[(0,[z196,z145,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z846]),(0,[z0,z1,z8,z314,z4,z5])],[(0,[z0,z1,z8,z3,z4,z847]),(0,[z0,z1,z8,z46,z4,z10])]],
   [[(0,[z0,z1,z8,z3,z4,z848]),(0,[z0,z1,z351,z3,z74,z5]),(0,[z16,z1,z8,z3,z4,z768])],[(0,[z38,z1,z8,z3,z254,z5]),(0,[z0,z8,z3,z4,z718,z45])],[(0,[z0,z1,z8,z3,z4,z849]),(0,[z0,z420,z8,z3,z74,z5])],[(0,[z414,z1,z8,z134,z4,z5]),(0,[z0,z502,z8,z3,z4,z282]),(0,[z0,z422,z126,z27,z4,z5]),(0,[z0,z1,z850,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z748])],[(0,[z66,z1,z8,z3,z4,z282]),(0,[z0,z42,z8,z3,z118,z45])],[(0,[z0,z1,z8,z3,z4,z851]),(0,[z0,z1,z3,z4,z5,z852]),(0,[z0,z1,z194,z3,z328,z5])],[(0,[z0,z1,z8,z3,z4,z853]),(0,[z0,z1,z8,z3,z285,z282]),(0,[z0,z125,z854,z3,z4,z5]),(0,[z0,z1,z126,z101,z4,z5])],[(1,[z1,z8,z734,z4,z5]),(0,[z0,z1,z8,z216,z11,z3]),(0,[z0,z1,z8,z855,z4,z5])]],
   [[(0,[z0,z1,z8,z3,z4,z856]),(0,[z0,z1,z8,z3,z857,z5]),(0,[z0,z8,z3,z4,z33,z522]),(0,[z0,z1,z8,z3,z858,z5]),(0,[z0,z859,z8,z3,z4,z5]),(1,[z0,z1,z3,z753,z5]),(0,[z0,z1,z193,z3,z150,z553])],[(0,[z0,z1,z860,z3,z4,z5]),(0,[z0,z1,z8,z3,z861,z5])],[(0,[z0,z1,z8,z206,z4,z5]),(0,[z0,z1,z207,z3,z4,z5]),(0,[z0,z862,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z863]),(0,[z0,z1,z193,z3,z150,z400])],[(0,[z0,z1,z8,z3,z864,z5]),(0,[z0,z1,z8,z3,z4,z865]),(0,[z0,z418,z8,z55,z4,z5]),(0,[z0,z1,z8,z82,z83,z79])],[(0,[z105,z866,z8,z3,z4,z5]),(0,[z0,z1,z8,z133,z3,z4]),(0,[z0,z1,z3,z4,z867,z5]),(0,[z0,z1,z8,z868,z3,z5])],[(0,[z0,z1,z869,z3,z4,z5]),(0,[z0,z1,z8,z3,z870,z5]),(0,[z0,z1,z871,z3,z4,z5])],[(0,[z0,z1,z872,z3,z4,z5]),(0,[z0,z1,z194,z351,z3,z5]),(0,[z0,z1,z8,z3,z4,z873]),(0,[z0,z1,z126,z612,z3,z4]),(0,[z0,z1,z8,z43,z44,z298])],[(0,[z0,z1,z8,z874,z4,z5]),(0,[z0,z135,z40,z3,z4,z5]),(0,[z38,z1,z8,z121,z3,z5]),(0,[z66,z1,z8,z302,z4,z5]),(0,[z0,z1,z195,z3,z4,z50])]],
   [[(0,[z0,z1,z8,z3,z4,z875]),(0,[z0,z1,z8,z302,z4,z282]),(0,[z0,z1,z8,z876,z3,z5])],[(0,[z0,z1,z8,z302,z285,z5]),(0,[z0,z854,z258,z3,z4,z5]),(0,[z0,z42,z8,z3,z166,z45])],[(0,[z0,z1,z8,z877,z4,z5]),(0,[z0,z1,z8,z3,z4,z878]),(0,[z1,z8,z3,z4,z712,z5]),(0,[z0,z1,z8,z4,z879,z5]),(0,[z65,z0,z854,z3,z4,z5])],[(0,[z0,z1,z8,z219,z4,z6]),(0,[z0,z1,z8,z203,z4,z41])],[(0,[z0,z1,z8,z3,z208,z41])],[(0,[z866,z171,z8,z3,z4,z5]),(0,[z0,z1,z8,z49,z3,z78])],[(0,[z0,z880,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z881])],[(0,[z0,z1,z8,z3,z4,z882]),(0,[z38,z1,z8,z3,z254,z78]),(0,[z0,z1,z8,z3,z883,z5]),(0,[z0,z1,z8,z4,z884,z5]),(0,[z0,z1,z8,z885,z3,z4])]],
   [[(0,[z0,z1,z40,z181,z4,z5]),(0,[z0,z1,z8,z3,z4,z886])],[(0,[z0,z1,z8,z887,z3,z4]),(0,[z0,z888,z8,z3,z4,z5])],[(0,[z0,z1,z889,z3,z4,z5]),(0,[z21,z1,z22,z3,z4,z224]),(0,[z0,z1,z8,z181,z4,z524]),(0,[z0,z1,z8,z3,z4,z890])],[(0,[z65,z0,z258,z3,z4,z5]),(0,[z0,z1,z29,z101,z4,z5]),(1,[z0,z1,z765,z4,z5]),(0,[z0,z1,z8,z3,z4,z891]),(0,[z0,z502,z8,z4,z20,z5]),(0,[z0,z1,z8,z3,z232,z81])],[(0,[z35,z1,z8,z495,z3,z5]),(0,[z0,z1,z165,z277,z3,z4])],[(0,[z0,z8,z3,z156,z146,z5]),(0,[z0,z135,z8,z274,z4,z5]),(0,[z0,z1,z8,z43,z274,z5]),(0,[z0,z1,z8,z184,z3,z50]),(0,[z0,z1,z8,z892,z3,z5]),(0,[z0,z1,z8,z46,z3,z118]),(0,[z0,z1,z8,z3,z893,z5]),(0,[z0,z88,z3,z4,z120,z6]),(0,[z0,z1,z88,z3,z4,z825])],[(0,[z0,z1,z8,z3,z894,z5]),(0,[z0,z1,z8,z3,z4,z895]),(0,[z0,z1,z8,z3,z4,z896]),(0,[z0,z1,z252,z46,z3,z4]),(0,[z0,z1,z8,z765,z4,z5])],[(0,[z0,z1,z8,z897,z3,z5]),(0,[z52,z1,z8,z734,z4,z5]),(0,[z0,z1,z898,z3,z4,z5]),(0,[z449,z1,z8,z3,z4,z17]),(0,[z0,z1,z854,z3,z4,z5])]],
   [[(0,[z105,z171,z8,z247,z4,z5]),(0,[z0,z1,z8,z899,z4,z5]),(0,[z0,z1,z195,z3,z4,z520]),(0,[z900,z1,z8,z3,z4,z5]),(1,[z0,z8,z3,z4,z718]),(0,[z0,z1,z8,z46,z138,z4]),(0,[z0,z1,z8,z179,z4,z79])],[(0,[z0,z1,z8,z901,z3,z5]),(0,[z0,z1,z351,z3,z4,z524]),(0,[z902,z1,z8,z3,z4,z5])],[(0,[z0,z1,z903,z3,z4,z5]),(0,[z0,z106,z8,z27,z4,z5]),(0,[z0,z1,z8,z44,z714,z5])],[(0,[z0,z904,z8,z3,z4,z5]),(0,[z0,z1,z8,z43,z620,z5])],[(0,[z0,z39,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z905,z5]),(0,[z0,z1,z8,z906,z4,z5]),(0,[z0,z42,z8,z3,z4,z282]),(0,[z1,z8,z3,z4,z5,z907])],[],[(0,[z0,z1,z908,z8,z3,z4]),(0,[z0,z1,z76,z8,z3,z5]),(0,[z0,z1,z8,z184,z294,z5]),(0,[z0,z1,z8,z3,z909,z5]),(0,[z0,z1,z277,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z910]),(0,[z0,z1,z8,z170,z714,z5])],[(0,[z0,z1,z8,z3,z4,z911]),(0,[z0,z1,z912,z8,z3,z5])]],
   [[(0,[z0,z1,z8,z913,z4,z5]),(0,[z0,z914,z8,z3,z4,z5]),(0,[z0,z1,z8,z4,z5,z915])],[(0,[z0,z1,z8,z3,z4,z224]),(0,[z0,z1,z8,z3,z916,z5]),(0,[z0,z1,z8,z3,z917,z5]),(0,[z0,z1,z8,z11,z3,z4]),(0,[z0,z1,z8,z3,z4,z918]),(0,[z0,z1,z8,z3,z4,z919])],[(0,[z0,z1,z8,z3,z920,z5]),(0,[z0,z1,z8,z49,z3,z162]),(0,[z0,z1,z8,z9,z4,z28]),(0,[z0,z1,z8,z3,z82,z748])],[(0,[z21,z1,z22,z3,z4,z5]),(0,[z51,z280,z8,z134,z4,z5]),(0,[z921,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z9,z3,z118])],[(0,[z1,z866,z8,z3,z4,z5]),(0,[z0,z1,z252,z9,z3,z4]),(1,[z1,z8,z3,z4,z768]),(0,[z191,z1,z8,z203,z4,z5]),(0,[z0,z502,z8,z3,z4,z33])],[(0,[z0,z1,z351,z274,z4,z5]),(0,[z0,z1,z8,z922,z4,z5]),(0,[z191,z1,z8,z3,z208,z5]),(0,[z0,z1,z421,z3,z4,z6])],[(0,[z0,z32,z8,z537,z4,z5]),(0,[z0,z1,z639,z3,z4,z6]),(0,[z0,z1,z8,z9,z138,z4])],[(0,[z0,z1,z8,z3,z923,z5]),(0,[z0,z502,z8,z3,z4,z45])]],
   [[],[(0,[z0,z1,z924,z8,z4,z5]),(0,[z0,z1,z8,z3,z285,z41]),(0,[z0,z1,z8,z46,z437,z4])],[(0,[z0,z1,z8,z925,z3,z4])],[(0,[z0,z1,z8,z926,z4,z5]),(0,[z0,z1,z22,z3,z4,z152]),(0,[z0,z1,z127,z203,z4,z5]),(0,[z0,z1,z8,z46,z4,z678]),(0,[z0,z13,z8,z484,z3,z4])],[(0,[z0,z1,z8,z927,z4,z5]),(0,[z0,z1,z8,z928,z3,z4]),(0,[z0,z929,z8,z3,z4,z5]),(0,[z0,z930,z8,z3,z4,z5]),(0,[z0,z1,z126,z4,z28,z5]),(0,[z0,z1,z3,z4,z825,z5])],[(0,[z0,z931,z8,z3,z4,z5]),(0,[z0,z1,z8,z932,z4,z5])],[(0,[z587,z1,z2,z3,z4,z5]),(0,[z0,z1,z8,z3,z933,z5]),(0,[z0,z1,z8,z3,z4,z825])],[(0,[z0,z135,z8,z3,z4,z5]),(0,[z0,z934,z8,z3,z4,z5]),(0,[z0,z1,z8,z935,z3,z5]),(0,[z0,z1,z8,z179,z4,z6])]],
   [[(0,[z0,z1,z8,z936,z4,z5]),(0,[z0,z1,z199,z8,z3,z5]),(0,[z0,z1,z8,z3,z79,z78]),(0,[z0,z1,z937,z3,z4,z5])],[(0,[z196,z145,z8,z3,z327,z5]),(0,[z0,z1,z8,z938,z4,z5]),(0,[z52,z0,z1,z8,z133,z4]),(0,[z0,z1,z8,z3,z79,z290])],[(0,[z0,z1,z8,z3,z4,z5]),(0,[z0,z39,z8,z3,z4,z78]),(0,[z0,z365,z8,z3,z146,z5])],[(0,[z0,z866,z8,z3,z4,z5]),(0,[z0,z1,z8,z302,z4,z41]),(0,[z939,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z940,z4,z5])],[(0,[z0,z1,z8,z3,z4,z941]),(0,[z0,z1,z8,z942,z3,z4]),(0,[z0,z1,z765,z102,z4,z5]),(0,[z0,z8,z314,z4,z5,z120])],[(0,[z0,z943,z8,z3,z4,z5]),(0,[z1,z716,z22,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z944]),(0,[z0,z1,z3,z4,z945,z5])],[(0,[z176,z0,z8,z3,z74,z5]),(0,[z0,z1,z101,z765,z4,z5])],[(0,[z0,z1,z626,z3,z4,z50]),(0,[z0,z1,z946,z3,z4,z5])]],
   [[(0,[z0,z1,z947,z3,z4,z5]),(0,[z0,z1,z8,z948,z4,z5]),(0,[z0,z949,z8,z3,z4,z5]),(0,[z0,z1,z126,z203,z4,z5]),(0,[z0,z502,z8,z314,z4,z5])],[(0,[z0,z1,z406,z3,z4,z6]),(0,[z0,z8,z3,z4,z5,z950]),(0,[z38,z135,z8,z3,z254,z5]),(0,[z0,z1,z127,z593,z4,z5])],[(0,[z0,z1,z8,z3,z951,z5]),(0,[z35,z1,z8,z3,z712,z5]),(0,[z952,z1,z8,z3,z4,z5])],[(0,[z176,z0,z8,z3,z156,z5]),(0,[z51,z147,z8,z134,z4,z5]),(0,[z0,z1,z8,z953,z4,z5]),(0,[z0,z1,z3,z954,z4,z5]),(0,[z0,z42,z8,z3,z4,z718]),(0,[z0,z1,z8,z3,z4,z955])],[(0,[z0,z1,z8,z956,z4,z5]),(0,[z0,z1,z252,z3,z4,z100]),(0,[z0,z1,z8,z184,z3,z81]),(0,[z0,z1,z8,z3,z82,z79])],[(0,[z0,z422,z8,z717,z4,z5]),(0,[z0,z1,z957,z3,z4,z5])],[(0,[z0,z958,z8,z3,z4,z5]),(0,[z0,z39,z8,z3,z146,z5]),(1,[z0,z8,z717,z4,z5])],[(0,[z0,z1,z8,z133,z216,z3]),(0,[z959,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z179,z82,z79])]],
   [[(0,[z0,z1,z8,z3,z960,z5]),(0,[z0,z1,z8,z4,z28,z508]),(0,[z0,z1,z8,z961,z4,z5])],[(0,[z0,z1,z8,z219,z123,z5]),(0,[z191,z1,z8,z3,z4,z282]),(0,[z0,z962,z8,z3,z4,z5])],[(0,[z0,z1,z8,z963,z4,z5]),(0,[z38,z1,z8,z181,z254,z5]),(0,[z0,z1,z252,z3,z4,z17]),(0,[z191,z1,z8,z3,z285,z5]),(0,[z0,z1,z8,z3,z964,z5])],[(0,[z0,z280,z8,z134,z4,z5]),(0,[z0,z965,z8,z3,z4,z5]),(0,[z0,z1,z8,z133,z4,z98]),(0,[z0,z1,z966,z8,z3,z5])],[(0,[z0,z967,z8,z3,z4,z5]),(0,[z16,z1,z8,z3,z123,z17]),(0,[z0,z1,z8,z4,z20,z128]),(0,[z0,z1,z195,z3,z4,z825])],[],[(0,[z672,z171,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z968,z5]),(0,[z38,z0,z1,z8,z3,z553]),(0,[z253,z1,z8,z3,z4,z100]),(0,[z969,z1,z8,z3,z4,z5]),(0,[z0,z8,z3,z4,z718,z5]),(0,[z0,z1,z8,z4,z28,z128]),(0,[z0,z1,z8,z3,z753,z5]),(0,[z0,z1,z8,z970,z4,z5]),(0,[z0,z1,z8,z4,z743,z400])],[(0,[z0,z1,z8,z971,z4,z5]),(0,[z0,z490,z8,z55,z4,z5]),(0,[z0,z1,z8,z3,z4,z972]),(0,[z0,z1,z973,z3,z4,z5])]],
   [[(0,[z0,z1,z8,z3,z974,z5]),(0,[z0,z1,z8,z3,z4,z78]),(0,[z0,z1,z8,z3,z4,z975]),(0,[z0,z1,z8,z976,z4,z5]),(0,[z0,z1,z977,z3,z4,z5]),(0,[z978,z1,z8,z3,z4,z5])],[(0,[z0,z1,z979,z3,z4,z5]),(0,[z38,z1,z351,z3,z254,z5]),(0,[z0,z1,z8,z3,z712,z5]),(0,[z0,z1,z980,z8,z3,z5]),(0,[z0,z1,z8,z786,z4,z5])],[(0,[z21,z1,z199,z22,z3,z5]),(0,[z0,z1,z8,z3,z981,z5]),(0,[z0,z124,z854,z3,z4,z5])],[(0,[z21,z1,z22,z3,z4,z152]),(0,[z0,z422,z277,z27,z4,z5]),(0,[z0,z1,z8,z46,z612,z4]),(0,[z0,z1,z8,z612,z4,z28])],[(0,[z0,z1,z8,z4,z982,z5]),(0,[z52,z1,z8,z4,z545,z5]),(0,[z191,z1,z8,z302,z4,z5]),(0,[z0,z1,z8,z4,z983,z5]),(0,[z0,z1,z357,z3,z4,z6])],[(0,[z0,z1,z199,z3,z328,z5]),(0,[z0,z1,z8,z3,z984,z5]),(1,[z0,z8,z3,z742,z5])],[(0,[z0,z485,z8,z3,z146,z5]),(0,[z38,z1,z8,z151,z3,z5]),(0,[z1,z8,z3,z4,z768,z17]),(0,[z0,z1,z8,z985,z3,z4])],[(0,[z105,z171,z8,z206,z4,z5]),(0,[z0,z280,z8,z46,z4,z5]),(0,[z0,z1,z8,z612,z138,z4])]],
   [[(0,[z0,z1,z8,z986,z4,z5]),(0,[z0,z1,z8,z3,z4,z987]),(0,[z0,z1,z988,z3,z4,z5]),(0,[z0,z8,z3,z989,z4,z5])],[(0,[z0,z1,z8,z3,z990,z5]),(0,[z0,z1,z8,z991,z4,z5]),(0,[z0,z1,z8,z992,z3,z4]),(0,[z1,z8,z3,z712,z254,z5]),(0,[z0,z1,z126,z165,z3,z4]),(0,[z0,z73,z8,z3,z146,z5])],[(0,[z0,z1,z8,z216,z3,z5]),(0,[z0,z603,z8,z27,z4,z5]),(0,[z0,z1,z423,z101,z4,z5])],[(0,[z0,z280,z8,z77,z4,z5]),(0,[z0,z1,z8,z3,z4,z993]),(0,[z0,z1,z3,z994,z4,z5])],[],[(0,[z995,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z996]),(0,[z0,z1,z8,z3,z4,z997])],[(0,[z0,z1,z199,z351,z3,z5]),(0,[z0,z1,z8,z184,z3,z5]),(0,[z0,z1,z88,z3,z4,z6])],[(0,[z71,z1,z622,z3,z4,z5]),(0,[z0,z1,z8,z216,z98,z5]),(1,[z0,z854,z3,z4,z5]),(0,[z0,z1,z3,z4,z50,z825])]],
   [[(0,[z0,z1,z8,z4,z998,z5]),(0,[z0,z1,z8,z999,z4,z5])],[(0,[z0,z1,z8,z3,z4,z1000]),(0,[z0,z1,z8,z938,z4,z152]),(0,[z0,z1,z8,z3,z4,z1001]),(0,[z0,z384,z8,z3,z146,z5])],[(0,[z0,z1,z1002,z8,z3,z5]),(0,[z0,z1,z8,z3,z4,z152]),(0,[z0,z1,z8,z1003,z4,z5])],[(0,[z0,z1,z8,z138,z4,z5]),(0,[z0,z1,z8,z4,z83,z5]),(0,[z0,z1,z8,z46,z4,z740]),(0,[z0,z1,z8,z3,z4,z740])],[(0,[z0,z1,z8,z1004,z4,z5]),(0,[z348,z1,z8,z3,z4,z100]),(0,[z0,z124,z125,z3,z4,z5])],[(0,[z0,z1,z8,z826,z3,z4]),(0,[z0,z1,z8,z3,z1005,z5]),(0,[z0,z1,z8,z3,z4,z1006]),(0,[z0,z1,z88,z314,z4,z6])],[(0,[z0,z1,z40,z3,z4,z524]),(0,[z16,z1,z207,z3,z4,z17]),(0,[z0,z8,z3,z74,z742,z5])],[(0,[z51,z1,z8,z657,z4,z5]),(0,[z0,z1007,z8,z3,z4,z5]),(0,[z0,z422,z8,z27,z4,z5]),(0,[z0,z1,z8,z3,z1008,z5])]],
   [[(0,[z0,z1,z8,z3,z714,z5])],[(0,[z1009,z1,z8,z3,z4,z5])],[(0,[z0,z1,z1010,z8,z3,z5])],[(0,[z619,z1,z22,z3,z4,z5]),(0,[z51,z1,z8,z141,z134,z5]),(0,[z0,z13,z8,z3,z4,z718])],[(0,[z1,z716,z8,z3,z4,z5]),(0,[z0,z1,z8,z4,z1011,z5]),(0,[z0,z1,z8,z4,z740,z249])],[(0,[z0,z1,z8,z4,z1012,z5]),(0,[z0,z39,z8,z181,z4,z5])],[(0,[z362,z1,z22,z3,z4,z5]),(0,[z0,z1,z1013,z3,z4,z5]),(0,[z196,z498,z8,z3,z4,z5]),(0,[z0,z1014,z8,z3,z4,z5]),(0,[z0,z1,z8,z1015,z4,z5]),(0,[z52,z1,z8,z77,z4,z5]),(0,[z0,z1,z8,z3,z4,z1016])],[(0,[z0,z1,z8,z1017,z4,z5]),(0,[z0,z1,z8,z4,z1018,z5])]],
   [[(0,[z0,z8,z1019,z3,z4,z5]),(0,[z597,z0,z1,z8,z46,z4])],[(0,[z0,z1,z8,z3,z4,z1020]),(0,[z0,z1,z8,z3,z4,z1021]),(0,[z0,z1,z8,z216,z274,z5]),(0,[z0,z1,z8,z1022,z3,z4]),(0,[z0,z1,z3,z4,z825,z6]),(0,[z0,z1,z8,z9,z4,z740])],[(0,[z0,z1,z40,z274,z4,z5])],[],[(0,[z0,z39,z351,z3,z4,z5]),(0,[z0,z1,z8,z274,z4,z524]),(0,[z191,z1,z8,z3,z4,z41])],[(0,[z0,z1,z8,z3,z327,z5]),(0,[z0,z1,z8,z1023,z4,z5]),(0,[z0,z1,z8,z1024,z4,z5]),(0,[z16,z1,z8,z219,z4,z17]),(0,[z0,z1,z8,z3,z4,z1025]),(0,[z0,z13,z8,z3,z4,z33]),(0,[z0,z1,z8,z43,z714,z5])],[(0,[z0,z1,z8,z133,z43,z4]),(0,[z0,z1,z8,z3,z4,z1026]),(0,[z0,z1,z8,z3,z4,z1027])],[(0,[z0,z1,z29,z4,z468,z5]),(0,[z0,z1,z1028,z8,z3,z5])]],
   [[(0,[z0,z1,z8,z3,z1029,z5]),(0,[z0,z1,z8,z1030,z3,z4]),(0,[z0,z1,z1031,z3,z4,z5]),(0,[z0,z39,z8,z3,z4,z524]),(0,[z0,z1,z8,z3,z1032,z5]),(0,[z65,z66,z258,z3,z4,z5]),(0,[z0,z1,z8,z4,z349,z28])],[(0,[z0,z1,z193,z160,z3,z5]),(0,[z0,z1,z8,z1033,z3,z4]),(0,[z16,z1,z252,z3,z4,z17])],[(0,[z196,z866,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z727,z5])],[(0,[z0,z1,z8,z925,z206,z4]),(0,[z0,z1,z8,z4,z1034,z5]),(0,[z0,z1,z8,z133,z141,z3])],[(0,[z0,z1,z8,z4,z982,z152]),(0,[z38,z1,z8,z3,z559,z5]),(0,[z38,z1,z596,z8,z3,z5]),(0,[z0,z502,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z1035])],[(0,[z0,z1,z8,z1036,z4,z5]),(0,[z0,z1,z8,z1037,z4,z5]),(0,[z66,z1,z8,z3,z4,z5]),(0,[z0,z299,z8,z27,z4,z5]),(0,[z0,z1,z1038,z3,z4,z5]),(0,[z0,z1,z127,z102,z4,z5]),(0,[z0,z502,z8,z46,z3,z4])],[(0,[z0,z1039,z8,z3,z4,z5]),(0,[z7,z1,z8,z111,z3,z4]),(0,[z0,z1,z8,z3,z4,z282])],[(0,[z0,z1040,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z285,z5]),(0,[z0,z1,z8,z3,z4,z553])]],
   [[(0,[z0,z1,z8,z3,z1041,z5]),(0,[z544,z1,z2,z3,z4,z5]),(0,[z0,z135,z8,z181,z4,z5]),(0,[z0,z1,z8,z1042,z4,z5]),(0,[z0,z1,z8,z1043,z4,z5]),(0,[z0,z8,z717,z27,z4,z5]),(0,[z1,z8,z3,z4,z1044,z5]),(0,[z0,z42,z8,z158,z3,z4]),(0,[z0,z1,z193,z3,z150,z5])],[(0,[z0,z1,z1045,z8,z3,z4]),(0,[z0,z1,z8,z216,z43,z5]),(0,[z0,z1,z8,z3,z4,z1046]),(0,[z0,z1,z8,z1047,z4,z5]),(0,[z0,z1,z8,z3,z4,z512]),(0,[z0,z1,z8,z46,z4,z249]),(0,[z0,z1,z8,z3,z5,z748]),(0,[z0,z1,z1048,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z1049]),(0,[z0,z1,z716,z3,z4,z5])],[(0,[z21,z1,z76,z22,z3,z5]),(0,[z0,z1,z8,z181,z4,z5]),(0,[z1,z8,z734,z134,z4,z5]),(0,[z0,z8,z3,z1050,z4,z5])],[(0,[z0,z1,z8,z184,z3,z79]),(0,[z1051,z1,z8,z3,z4,z5])],[(0,[z0,z1,z8,z1052,z4,z5]),(0,[z7,z1,z8,z3,z4,z100]),(0,[z65,z0,z258,z203,z4,z5]),(0,[z0,z8,z55,z717,z4,z5]),(0,[z0,z1,z8,z1053,z4,z5]),(0,[z0,z1,z8,z46,z4,z409])],[(0,[z0,z171,z8,z206,z4,z5]),(0,[z0,z1,z193,z3,z89,z5]),(0,[z65,z0,z258,z3,z208,z5])],[(0,[z105,z171,z8,z3,z4,z5]),(0,[z0,z135,z351,z3,z4,z5]),(0,[z16,z1,z8,z4,z294,z17]),(0,[z0,z1,z8,z9,z4,z220])]],
   [[(0,[z0,z1,z8,z3,z4,z1054]),(0,[z0,z1055,z8,z3,z4,z5]),(0,[z432,z1,z8,z77,z4,z5])],[(0,[z696,z171,z8,z3,z4,z5]),(0,[z0,z1,z8,z1056,z4,z5]),(0,[z182,z145,z8,z3,z4,z5]),(0,[z0,z1057,z8,z3,z4,z5]),(0,[z0,z1,z1058,z3,z4,z5]),(0,[z0,z1,z8,z1059,z4,z5]),(0,[z0,z1,z8,z302,z4,z5]),(0,[z0,z1,z8,z23,z4,z5]),(0,[z0,z1,z8,z1060,z3,z5])],[(0,[z0,z1,z8,z3,z4,z1061]),(0,[z0,z1,z351,z3,z4,z5]),(0,[z0,z1,z126,z102,z4,z5]),(0,[z0,z1,z680,z3,z4,z50])],[(0,[z0,z502,z8,z9,z3,z4])],[(0,[z0,z1,z8,z3,z4,z1062]),(0,[z51,z1,z8,z734,z4,z5]),(0,[z0,z422,z8,z612,z27,z4]),(0,[z0,z1,z8,z3,z576,z79])],[(0,[z0,z1,z8,z1063,z4,z5]),(0,[z0,z1,z612,z277,z3,z4]),(0,[z0,z1,z3,z765,z4,z5]),(0,[z0,z1,z8,z1064,z4,z5])],[(0,[z0,z1,z8,z1065,z4,z5]),(0,[z0,z1,z8,z43,z4,z512]),(0,[z0,z1,z8,z4,z5,z740])],[(0,[z0,z145,z8,z206,z4,z5]),(0,[z35,z1,z324,z8,z3,z5])]],
   [[(0,[z0,z1,z8,z1066,z4,z5]),(0,[z0,z135,z8,z3,z4,z78]),(0,[z0,z8,z854,z3,z4,z5])],[(0,[z0,z1,z8,z4,z1067,z5])],[],[(0,[z0,z1,z8,z219,z184,z5]),(0,[z0,z1,z8,z3,z1068,z5]),(0,[z0,z1,z8,z3,z1069,z5]),(0,[z0,z574,z8,z55,z4,z5]),(0,[z0,z42,z8,z3,z4,z45])],[(0,[z0,z1,z8,z3,z5,z1070]),(0,[z0,z1,z8,z3,z1071,z5])],[(0,[z0,z1,z22,z3,z4,z400]),(0,[z0,z1,z8,z219,z4,z50]),(0,[z0,z1,z8,z3,z778,z5])],[(1,[z866,z8,z3,z4,z5]),(0,[z0,z1,z8,z4,z20,z5]),(0,[z0,z1072,z8,z3,z4,z5])],[(0,[z0,z1,z8,z4,z1073,z5]),(0,[z0,z1,z8,z1074,z3,z4]),(0,[z0,z1,z8,z3,z4,z298])]],
   [[(0,[z0,z1,z8,z1075,z3,z5]),(0,[z0,z1,z8,z3,z5,z1076]),(0,[z38,z1,z8,z3,z254,z524])],[(0,[z0,z1,z8,z181,z4,z78])],[(0,[z0,z280,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z1077,z5]),(0,[z35,z1,z8,z3,z36,z5]),(0,[z0,z39,z8,z3,z74,z5])],[(0,[z0,z1,z1078,z3,z4,z5]),(0,[z0,z1,z8,z1079,z4,z5]),(0,[z0,z1,z8,z184,z3,z6]),(0,[z0,z1,z101,z287,z4,z5])],[(0,[z0,z1,z1080,z3,z4,z5])],[(0,[z0,z1,z8,z1081,z4,z5]),(0,[z0,z1,z8,z3,z4,z718]),(0,[z0,z1082,z8,z3,z4,z5])],[(0,[z0,z8,z3,z1083,z4,z5]),(0,[z0,z1,z3,z753,z4,z5])],[(0,[z0,z39,z8,z3,z156,z5]),(0,[z1084,z1,z8,z3,z4,z5])]],
   [[(0,[z0,z1,z351,z3,z4,z78]),(0,[z0,z1,z8,z3,z1085,z5]),(0,[z0,z502,z88,z3,z4,z6]),(0,[z0,z1,z144,z3,z4,z50])],[(0,[z71,z1,z2,z3,z4,z5]),(0,[z0,z1,z8,z1086,z3,z4]),(0,[z0,z1,z8,z3,z4,z1087]),(0,[z0,z1,z1088,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z1089]),(0,[z0,z1,z8,z3,z1090,z5]),(0,[z21,z1,z716,z3,z4,z5]),(0,[z65,z0,z258,z3,z4,z282]),(0,[z0,z8,z3,z742,z4,z5])],[(0,[z65,z0,z258,z3,z285,z5]),(0,[z176,z0,z8,z3,z742,z5])],[(0,[z38,z1,z8,z274,z254,z5]),(0,[z0,z1,z8,z203,z4,z5])],[(0,[z0,z1,z8,z43,z241,z5]),(0,[z0,z1,z1091,z3,z4,z5]),(0,[z0,z1,z8,z46,z632,z4]),(0,[z0,z1,z8,z3,z208,z5]),(0,[z0,z124,z453,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z1092]),(0,[z0,z1093,z8,z3,z4,z5]),(0,[z51,z1,z8,z133,z134,z4]),(0,[z51,z0,z1,z8,z133,z4]),(0,[z0,z1,z8,z3,z1094,z5]),(0,[z0,z1,z8,z4,z1095,z5]),(0,[z0,z557,z8,z3,z4,z33])],[(0,[z0,z1,z8,z1096,z3,z4])]],
   [[(0,[z0,z1,z8,z3,z4,z1097]),(0,[z0,z1,z8,z1098,z4,z5]),(0,[z0,z1,z8,z3,z79,z748])],[(0,[z0,z1,z8,z3,z1099,z4]),(0,[z35,z1,z8,z3,z233,z5]),(0,[z0,z1,z8,z3,z4,z41]),(0,[z0,z1,z1100,z8,z3,z5])],[(0,[z0,z1,z8,z3,z1101,z5]),(0,[z0,z1,z8,z3,z4,z1102])],[(0,[z65,z191,z258,z3,z4,z5]),(0,[z0,z8,z3,z4,z5,z120]),(0,[z0,z668,z8,z27,z4,z5]),(0,[z0,z1,z8,z3,z118,z5]),(0,[z0,z1,z193,z3,z753,z5])],[(0,[z0,z1,z8,z1103,z3,z4]),(0,[z0,z1104,z8,z3,z4,z5]),(0,[z0,z1,z8,z734,z4,z5]),(0,[z0,z1,z8,z1105,z3,z5]),(1,[z1,z8,z3,z712,z5]),(0,[z0,z1,z8,z692,z3,z81])],[(0,[z0,z1,z8,z3,z1106,z5]),(0,[z0,z1,z8,z3,z123,z5]),(0,[z65,z0,z258,z302,z4,z5]),(0,[z0,z1,z127,z765,z4,z5])],[(0,[z0,z1,z8,z3,z1107,z5]),(0,[z145,z866,z8,z3,z4,z5]),(0,[z0,z1108,z8,z3,z4,z5])],[(0,[z0,z1,z8,z1109,z4,z5]),(0,[z0,z1,z8,z4,z98,z512]),(1,[z0,z1,z8,z4,z740])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 547) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 547).take 535) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1082)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [547, 535] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 159).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 159).take 97).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [159, 97] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_38751

theorem PEqualNP.Outside.L_meta_38751 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4006142144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4006142144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38751.solve