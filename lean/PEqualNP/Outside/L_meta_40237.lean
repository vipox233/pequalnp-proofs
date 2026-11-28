import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40237

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4274579648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0002411580e31bc8#64 ++ 0x20002411580e31bc#64 ++ 0xf027cf3f81e73fc7#64 ++ 0xdf027cf3f81e73fc#64 : BitVec 256),
   (0x00c9144c060d4552#64 ++ 0x400c9144c060d455#64 ++ 0x71d934cc0e3fc7ff#64 ++ 0xb71d934cc0e3fc7f#64 : BitVec 256),
   (0x061628b0b030a8a0#64 ++ 0x8061628b0b030a8a#64 ++ 0xde1e38f0f038f8ff#64 ++ 0x7de1e38f0f038f8f#64 : BitVec 256),
   (0x1b603f005b40f603#64 ++ 0x01b603f005b40f60#64 ++ 0xbfe03f00ffc0ff0e#64 ++ 0xfbfe03f00ffc0ff0#64 : BitVec 256),
   (0x2dbfc000edbe000c#64 ++ 0x02dbfc000edbe000#64 ++ 0xafffc000ffff000d#64 ++ 0xfafffc000ffff000#64 : BitVec 256),
   (0x4ffdbeea00000000#64 ++ 0x04ffdbeea0000000#64 ++ 0x4fffffff00000003#64 ++ 0xf4fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [12, 3]⟩, ⟨.and, [13, 8]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x2001000000270005 0x9200100000027000

def z1 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf027cf3f81e73fc7 0xdf027cf3f81e73fc

def z2 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x71d934cc0e3fc7ff 0xb71d934cc0e3fc7f

def z3 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde1e38f0f038f8ff 0x7de1e38f0f038f8f

def z4 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfe03f00ffc0ff0e 0xfbfe03f00ffc0ff0

def z5 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafffc000ffff000d 0xfafffc000ffff000

def z6 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4fffffff00000003 0xf4fffffff0000000

def z7 : W := mkw 0x0002400080a20008 0x00002400080a2000 0x0007c00000270001 0x00007c0000027000

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000000002000c7 0x150000000002000c

def z9 : W := mkw 0x0002001080200880 0x0000200108020088 0x8006083080003800 0x4800608308000380

def z10 : W := mkw 0x00000004060d4552 0x400000004060d455 0x300000000e3fc7fc 0x0300000000e3fc7f

def z11 : W := mkw 0x00c91448060c4412 0x400c91448060c441 0x01d830c00e18c038 0x201d830c00e18c03

def z12 : W := mkw 0x041641b5a0f31be8 0xa041641b5a0f31be 0xf03fcfff81ff3ff7 0xdf03fcfff81ff3ff

def z13 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xb000000081e73fc4 0x0b000000081e73fc

def z14 : W := mkw 0x1b603e005b00e403 0x01b603e005b00e40 0x0fe03f007e00c00a 0xf0fe03f007e00c00

def z15 : W := mkw 0x0000000400010140 0x0000000040001014 0x7001040c002707c7 0x97001040c002707c

def z16 : W := mkw 0x0002411180e21a88 0x20002411180e21a8 0x8026cb3381c03800 0x48026cb3381c0380

def z17 : W := mkw 0x020028b01000a8a0 0x8020028b01000a8a 0x500038f00000f8f2 0x0500038f00000f8f

def z18 : W := mkw 0x061428a03010a020 0x8061428a03010a02 0x0e1830c07018c038 0x20e1830c07018c03

def z19 : W := mkw 0x2dbd80006d1c0004 0x02dbd80006d1c000 0x0fd800007e180008 0x20fd800007e18000

def z20 : W := mkw 0x196017004b405603 0x0196017004b40560 0x21e007000fc00700 0x821e007000fc0070

def z21 : W := mkw 0x1f763fb0fb70fea3 0x81f763fb0fb70fea 0xfffe3ff0fff8ffff 0xffffe3ff0fff8fff

def z22 : W := mkw 0x4ffdbefa1000a8a0 0x84ffdbefa1000a8a 0x5fffffff0000f8f3 0xf5fffffff0000f8f

def z23 : W := mkw 0x4f36aab2b030a8a0 0x84f36aab2b030a8a 0x8e26cb33f0003800 0x48e26cb33f000380

def z24 : W := mkw 0x2dbfc010fdbea8ac 0x82dbfc010fdbea8a 0xbfffc000fffff8fd 0xfbfffc000fffff8f

def z25 : W := mkw 0x12403f001240f603 0x012403f001240f60 0x10003f000000ff02 0x010003f000000ff0

def z26 : W := mkw 0x20024000edbe000c 0x020024000edbe000 0xa0000000ffff000c 0x0a0000000ffff000

def z27 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf007c03f81e73fc5 0x0f007c03f81e73fc

def z28 : W := mkw 0x249fc0b0a4be08ac 0x8249fc0b0a4be08a 0x401fc0f0003f00f1 0x0401fc0f0003f00f

def z29 : W := mkw 0x4ffffeea80a20008 0x04ffffeea80a2000 0xefffffff81e70007 0xfefffffff81e7000

def z30 : W := mkw 0x1f362bb0f970baa1 0x81f362bb0f970baa 0xde3e3bf0f1f8f8ff 0x7de3e3bf0f1f8f8f

def z31 : W := mkw 0x00890000040c0000 0x000890000040c000 0x21d900000e3f000d 0xb21d900000e3f000

def z32 : W := mkw 0x020028b01000a8a0 0x8020028b01000a8a 0x501838f00038f8ff 0x3501838f00038f8f

def z33 : W := mkw 0x1b603f045f4df753 0x41b603f045f4df75 0xbfe03f00fffffffe 0xfbfe03f00fffffff

def z34 : W := mkw 0x061428a000000000 0x0061428a00000000 0x4e3fffff00000003 0xf4e3fffff0000000

def z35 : W := mkw 0x29a9c0004d8e000c 0x029a9c0004d8e000 0xafe1c000ffc7000c 0xfafe1c000ffc7000

def z36 : W := mkw 0x00020000a0300000 0x000020000a030000 0x80000000f038000c 0x080000000f038000

def z37 : W := mkw 0x02403e0000000000 0x002403e000000000 0x00003f0000000002 0x000003f000000000

def z38 : W := mkw 0x100001005b40f603 0x0100001005b40f60 0xb0000000ffc0ff0c 0x0b0000000ffc0ff0

def z39 : W := mkw 0x1b627f15dbe3ffcb 0x21b627f15dbe3ffc 0xffe7ff3fffe7ffcf 0xfffe7ff3fffe7ffc

def z40 : W := mkw 0x0000011500411bc0 0x20000011500411bc 0x50000f3f00003fc2 0x050000f3f00003fc

def z41 : W := mkw 0x0002400080a20008 0x00002400080a2000 0xa027c00081e70005 0xda027c00081e7000

def z42 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x0fe7cf3f00000000 0xc0fe7cf3f0000000

def z43 : W := mkw 0x0920000049000000 0x0092000004900000 0xafe00000ffc0000c 0xfafe00000ffc0000

def z44 : W := mkw 0x249fc000a4be000c 0x0249fc000a4be000 0x001fc000003f0001 0x0001fc000003f000

def z45 : W := mkw 0x4ffdbeee060d4552 0x44ffdbeee060d455 0x7fd934cc0e3fc7ff 0xb7fd934cc0e3fc7f

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x4027cf3f00000003 0xd4027cf3f0000000

def z47 : W := mkw 0x4ffdbeee060d4552 0x44ffdbeee060d455 0x7fffffff0e3fc7ff 0xf7fffffff0e3fc7f

def z48 : W := mkw 0x0000000000000000 0x0000000000000000 0x401800c0003800f1 0x0401800c0003800f

def z49 : W := mkw 0x12403f4c1241f753 0x412403f4c1241f75 0x50003fcc0000fff2 0x050003fcc0000fff

def z50 : W := mkw 0x29224000edbe000c 0x029224000edbe000 0xafe00000ffff000c 0xfafe00000ffff000

def z51 : W := mkw 0x449d80ea00000000 0x0449d80ea0000000 0x401fc0ff00000001 0x0401fc0ff0000000

def z52 : W := mkw 0x0b603e0000000000 0x00b603e000000000 0x4fe7ff3f00000003 0xf4fe7ff3f0000000

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0x501830c00038c0ff 0x3501830c00038c0f

def z54 : W := mkw 0x06df3cfcb63dedf2 0xc06df3cfcb63dedf 0xffdf3cfcfe3fffff 0xfffdf3cfcfe3ffff

def z55 : W := mkw 0x2dbdc0004d8e000c 0x02dbdc0004d8e000 0x2fffc0000fc70001 0xf2fffc0000fc7000

def z56 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0x8fe03b00ffc0f808 0x68fe03b00ffc0f80

def z57 : W := mkw 0x1beb7f5ddfefffdb 0x61beb7f5ddfefffd 0xffffffffffffffff 0xffffffffffffffff

def z58 : W := mkw 0x061428a03010a020 0x8061428a03010a02 0x4e1e38f07018c03b 0x74e1e38f07018c03

def z59 : W := mkw 0x4f74bea200000000 0x04f74bea20000000 0x0fe6ff3300000002 0xf0fe6ff330000000

def z60 : W := mkw 0x52403fea1240f603 0x052403fea1240f60 0x50003fff0000ff02 0x050003fff0000ff0

def z61 : W := mkw 0x061669b5b0f3bbe8 0xa061669b5b0f3bbe 0xfe3ffffff1ffffff 0xffe3ffffff1fffff

def z62 : W := mkw 0x008b415d84ef1bd8 0x6008b415d84ef1bd 0xf03fcfff81ff3ff7 0xdf03fcfff81ff3ff

def z63 : W := mkw 0x0089004c040d0150 0x40089004c040d015 0x401900cc003f00f1 0x0401900cc003f00f

def z64 : W := mkw 0x1b202b005940b201 0x01b202b005940b20 0x8e200b00f1c03800 0x48e200b00f1c0380

def z65 : W := mkw 0x06dd3cec060d4552 0x406dd3cec060d455 0x7fdf3cfc0e3fc7ff 0xf7fdf3cfc0e3fc7f

def z66 : W := mkw 0x42403eea00000000 0x042403eea0000000 0x40003fff00000002 0x040003fff0000000

def z67 : W := mkw 0x249fc015a4bf09cc 0x2249fc015a4bf09c 0x401fc03f003f00c1 0x0401fc03f003f00c

def z68 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x21c1040c0e070700 0x821c1040c0e07070

def z69 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0x8e060830f0003800 0x48e060830f000380

def z70 : W := mkw 0x06563cfcb231edf2 0xc06563cfcb231edf 0xde1e3cfcf038ffff 0x7de1e3cfcf038fff

def z71 : W := mkw 0x4f34aaa200000000 0x04f34aaa20000000 0x0e26cb3300000000 0x40e26cb330000000

def z72 : W := mkw 0x00c91448060c4412 0x400c91448060c441 0x31d834c00e18c73e 0xb31d834c00e18c73

def z73 : W := mkw 0x0002401580a309c8 0x20002401580a309c 0x4007c03f002700c1 0x04007c03f002700c

def z74 : W := mkw 0x061668b0b0b2a8a8 0x8061668b0b0b2a8a 0xfe3ff8f0f1fff8ff 0xffe3ff8f0f1fff8f

def z75 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0x9e1830c0f038f8fc 0x29e1830c0f038f8f

def z76 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xefffcf3fffff000f 0xfefffcf3fffff000

def z77 : W := mkw 0x200000006d1c0004 0x0200000006d1c000 0x000000007e180008 0x0000000007e18000

def z78 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xb021c70f81e73fc4 0x8b021c70f81e73fc

def z79 : W := mkw 0x5b603fea5b40f603 0x05b603fea5b40f60 0xffe03fffffc0ff0e 0xfffe03fffffc0ff0

def z80 : W := mkw 0x008b400084ae0008 0x0008b400084ae000 0xa1ffc0008fff000d 0xfa1ffc0008fff000

def z81 : W := mkw 0x42403fff00411bc0 0x242403fff00411bc 0x50003fff00003fc2 0x050003fff00003fc

def z82 : W := mkw 0x19625715cbe35fcb 0x219625715cbe35fc 0xf1e7cf3f8fe73fc7 0xdf1e7cf3f8fe73fc

def z83 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000080080003806 0x5900008008000380

def z84 : W := mkw 0x2fbfe9b5fdffbbec 0xa2fbfe9b5fdffbbe 0xffffffffffffffff 0xffffffffffffffff

def z85 : W := mkw 0x2dbfc115edff1bcc 0x22dbfc115edff1bc 0xffffcf3fffff3fcf 0xfffffcf3fffff3fc

def z86 : W := mkw 0x0002001080200880 0x0000200108020088 0xd0060830802038c7 0x5d0060830802038c

def z87 : W := mkw 0x2dbdc0006d9e000c 0x02dbdc0006d9e000 0x2ff9c0007fdf0008 0xa2ff9c0007fdf000

def z88 : W := mkw 0x0000010000401200 0x0000001000040120 0xb0200f0081c03f06 0xdb0200f0081c03f0

def z89 : W := mkw 0x00c9144800000000 0x000c914480000000 0x01c1040c00000000 0x801c1040c0000000

def z90 : W := mkw 0x196017004b405603 0x0196017004b40560 0xb1e00f008fc03f06 0xdb1e00f008fc03f0

def z91 : W := mkw 0x12403f151241ffc3 0x212403f151241ffc 0x50003f3f0000ffc2 0x050003f3f0000ffc

def z92 : W := mkw 0x00020010b030a8a0 0x800020010b030a8a 0xd0060830f038f8ff 0x5d0060830f038f8f

def z93 : W := mkw 0x0040144c02014552 0x40040144c0201455 0x0000040c00000700 0x00000040c0000070

def z94 : W := mkw 0x20024000e9b2000c 0x020024000e9b2000 0x80000000f1c00000 0x080000000f1c0000

def z95 : W := mkw 0x5ffdbfea5b40f603 0x05ffdbfea5b40f60 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z96 : W := mkw 0x4f36ebb780e31bc8 0x24f36ebb780e31bc 0xfe27cf3f81e73fc7 0xdfe27cf3f81e73fc

def z97 : W := mkw 0x104015005b40f603 0x0104015005b40f60 0xb1c03400ffc0ff0e 0xbb1c03400ffc0ff0

def z98 : W := mkw 0x4ffdbeea1000a000 0x04ffdbeea1000a00 0xdffffffff000f80f 0xfdffffffff000f80

def z99 : W := mkw 0x4fffbefab030a8a0 0x84fffbefab030a8a 0xdffffffff038f8ff 0xfdffffffff038f8f

def z100 : W := mkw 0x3ffdbf007f5cf607 0x03ffdbf007f5cf60 0xbff83f00ffd8ff0e 0xfbff83f00ffd8ff0

def z101 : W := mkw 0x2dbfc115edff1bcc 0x22dbfc115edff1bc 0xbfffc000ffff3fcd 0xfbfffc000ffff3fc

def z102 : W := mkw 0x29a9c0004d8e000c 0x029a9c0004d8e000 0x21f9c0000fff000d 0xb21f9c0000fff000

def z103 : W := mkw 0x0000410500c31348 0x20000410500c3134 0x2021c70f01c70700 0x82021c70f01c7070

def z104 : W := mkw 0x161629b0fb70fea3 0x8161629b0fb70fea 0xfe1e38f0fff8ffff 0x7fe1e38f0fff8fff

def z105 : W := mkw 0x449fc1ff80e31bc8 0x2449fc1ff80e31bc 0xf03fcfff81e73fc7 0xdf03fcfff81e73fc

def z106 : W := mkw 0x0000000400010140 0x0000000040001014 0x701934cc003fc7ff 0xb701934cc003fc7f

def z107 : W := mkw 0x29a980004d0c0004 0x029a980004d0c000 0x01c000000e000000 0x001c000000e00000

def z108 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0x9e060830f038f8fc 0x49e060830f038f8f

def z109 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0x6027c73f01e707c1 0x86027c73f01e707c

def z110 : W := mkw 0x00020010b030a8a0 0x800020010b030a8a 0x90000000f038f8fc 0x090000000f038f8f

def z111 : W := mkw 0x49e9964a00000000 0x049e9964a0000000 0x01e1c70f00000000 0x801e1c70f0000000

def z112 : W := mkw 0x041600b0a03008a0 0x8041600b0a03008a 0xce1e00f0f03800fd 0x7ce1e00f0f03800f

def z113 : W := mkw 0x00024115b0f3bbe8 0xa00024115b0f3bbe 0xb0000000f1fffffc 0x0b0000000f1fffff

def z114 : W := mkw 0x0b603e0000000000 0x00b603e000000000 0x0fc0300000000000 0x20fc030000000000

def z115 : W := mkw 0x00cb555d86ef5fda 0x600cb555d86ef5fd 0xf1d934cc8fffffff 0xbf1d934cc8ffffff

def z116 : W := mkw 0x5ffdbfea5b40f603 0x05ffdbfea5b40f60 0xbff83fc0ffc0ff0e 0xfbff83fc0ffc0ff0

def z117 : W := mkw 0x04160000a0300000 0x004160000a030000 0xde1e30c0f038c0ff 0x7de1e30c0f038c0f

def z118 : W := mkw 0x6ffffeeaedbe000c 0x06ffffeeaedbe000 0xefffffffffff000f 0xfefffffffffff000

def z119 : W := mkw 0x1b603f005940b201 0x01b603f005940b20 0x8fe03f00f1c03802 0xf8fe03f00f1c0380

def z120 : W := mkw 0x0002410580e31348 0x20002410580e3134 0xa027c70f81e70705 0xda027c70f81e7070

def z121 : W := mkw 0x39e9d7004fce560f 0x039e9d7004fce560 0x21e1c7000fc70700 0x821e1c7000fc7070

def z122 : W := mkw 0x69e9d64a4d8e000c 0x069e9d64a4d8e000 0x21e1c70f0fc70000 0x821e1c70f0fc7000

def z123 : W := mkw 0x0000000000000000 0x0000000000000000 0x4006083000000003 0x5400608300000000

def z124 : W := mkw 0x00c9144800000000 0x000c914480000000 0x41d934cc00000003 0xb41d934cc0000000

def z125 : W := mkw 0x0960160000000000 0x0096016000000000 0x01e0070000000000 0x801e007000000000

def z126 : W := mkw 0x061428a000000000 0x0061428a00000000 0x4e1e38f000000003 0x74e1e38f00000000

def z127 : W := mkw 0x4ffdbeea040c0000 0x04ffdbeea040c000 0x6fffffff0e3f000f 0xf6fffffff0e3f000

def z128 : W := mkw 0x02c93c4c160de552 0x402c93c4c160de55 0xffd93cccfe3fffff 0xfffd93cccfe3ffff

def z129 : W := mkw 0x041600b0a03008a0 0x8041600b0a03008a 0x401e00f0003800f1 0x0401e00f0003800f

def z130 : W := mkw 0x00c91448060c4412 0x400c91448060c441 0x01c000000e000000 0x001c000000e00000

def z131 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x0ffff0c000000001 0xf0ffff0c00000000

def z132 : W := mkw 0x4ffdbeee040d0150 0x44ffdbeee040d015 0x4fffffff003f00f3 0xf4fffffff003f00f

def z133 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde0638f0f000f8f2 0x4de0638f0f000f8f

def z134 : W := mkw 0x04160000a0300000 0x004160000a030000 0x8e1e0000f038000d 0x78e1e0000f038000

def z135 : W := mkw 0x061428a03010a020 0x8061428a03010a02 0x5e1830c07038c0ff 0x35e1830c07038c0f

def z136 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xfffff0c0ffffc0ff 0xffffff0c0ffffc0f

def z137 : W := mkw 0x2ffffcfcffbfedfe 0xc2ffffcfcffbfedf 0xfffffcfcffffffff 0xffffffcfcfffffff

def z138 : W := mkw 0x2d36c115e9f31bcc 0x22d36c115e9f31bc 0xfe27cf3ff1e73fc7 0xdfe27cf3ff1e73fc

def z139 : W := mkw 0x0002411586ef5fda 0x60002411586ef5fd 0xb00000008ffffffc 0x0b00000008ffffff

def z140 : W := mkw 0x2d36c000e9b2000c 0x02d36c000e9b2000 0xae27c000f1e70005 0xdae27c000f1e7000

def z141 : W := mkw 0x00cb545d86af4dda 0x600cb545d86af4dd 0x71dff4ff0e3fc7ff 0xb71dff4ff0e3fc7f

def z142 : W := mkw 0x0b603e001000a000 0x00b603e001000a00 0x9fe03f00f000f80e 0xf9fe03f00f000f80

def z143 : W := mkw 0x061428a000000000 0x0061428a00000000 0x0e1830c000000000 0x20e1830c00000000

def z144 : W := mkw 0x441480a200000000 0x0441480a20000000 0x0006c03300000000 0x00006c0330000000

def z145 : W := mkw 0x0b603e0000000000 0x00b603e000000000 0x0fe03f0000000002 0xf0fe03f000000000

def z146 : W := mkw 0x649fc0eaa4be000c 0x0649fc0eaa4be000 0x401fc0ff003f0001 0x0401fc0ff003f000

def z147 : W := mkw 0x0040140002004402 0x0004014000200440 0x31c034000e00c70e 0xb31c034000e00c70

def z148 : W := mkw 0x1be93f4c5f4df753 0x41be93f4c5f4df75 0xfff93fccffffffff 0xffff93fccfffffff

def z149 : W := mkw 0x0000000000000000 0x0000000000000000 0xa020000081c00004 0xda020000081c0000

def z150 : W := mkw 0x1b603e005b00e403 0x01b603e005b00e40 0x0fc030007e00c008 0x20fc030007e00c00

def z151 : W := mkw 0x1ffdbf005b40f603 0x01ffdbf005b40f60 0xbfffff00ffc0ff0f 0xfbfffff00ffc0ff0

def z152 : W := mkw 0x02c93cfc160dedf2 0xc02c93cfc160dedf 0x71d93cfc0e3fffff 0xb71d93cfc0e3ffff

def z153 : W := mkw 0x3fffff00fffef60f 0x03fffff00fffef60 0xbfffff00ffffff0f 0xfbfffff00ffffff0

def z154 : W := mkw 0x12002b001040b201 0x012002b001040b20 0x00000b0000003800 0x000000b000000380

def z155 : W := mkw 0x400000ea00000000 0x0400000ea0000000 0x400000ff00000000 0x0400000ff0000000

def z156 : W := mkw 0x1f743ea07b10e423 0x81f743ea07b10e42 0x0fd830c07e18c038 0x20fd830c07e18c03

def z157 : W := mkw 0x0000000000000000 0x0000000000000000 0x00200f0000000002 0xd00200f000000000

def z158 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde3ffffff038f8ff 0xfde3ffffff038f8f

def z159 : W := mkw 0x0002410080e21208 0x00002410080e2120 0xb027cf0081e73f07 0xdb027cf0081e73f0

def z160 : W := mkw 0x12403f005b40f603 0x012403f005b40f60 0xb0003f00ffc0ff0e 0x0b0003f00ffc0ff0

def z161 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafe7c000ffc70000 0xcafe7c000ffc7000

def z162 : W := mkw 0x0002001080200880 0x0000200108020088 0xd027cf3f802038c7 0xdd027cf3f802038c

def z163 : W := mkw 0x42403eea00000000 0x042403eea0000000 0x4027ffff00000003 0xd4027ffff0000000

def z164 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafd80000ffff000c 0x2afd80000ffff000

def z165 : W := mkw 0x0000000000000000 0x0000000000000000 0x100030000000c00e 0x3100030000000c00

def z166 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x5fffffff0038c0ff 0xf5fffffff0038c0f

def z167 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x61d934cc0e070703 0xb61d934cc0e07070

def z168 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0x4e1e30f07038c0f9 0x24e1e30f07038c0f

def z169 : W := mkw 0x020228109020a880 0x0020228109020a88 0xde063830f020f8cf 0x7de063830f020f8c

def z170 : W := mkw 0x10024115dbe3ffcb 0x210024115dbe3ffc 0xb0000000ffe7ffcc 0x0b0000000ffe7ffc

def z171 : W := mkw 0x0dbd800000000000 0x00dbd80000000000 0x0fd8000000000000 0x20fd800000000000

def z172 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xd026cf3f81c03fc2 0x4d026cf3f81c03fc

def z173 : W := mkw 0x061628b4b63dedf2 0xc061628b4b63dedf 0xfe1e38f0fe3fffff 0x7fe1e38f0fe3ffff

def z174 : W := mkw 0x19e9174c4f4d5753 0x419e9174c4f4d575 0x21e1070c0fc70700 0x821e1070c0fc7070

def z175 : W := mkw 0x5f74bfa25b40f603 0x05f74bfa25b40f60 0xbfe6ff33ffc0ff0e 0xfbfe6ff33ffc0ff0

def z176 : W := mkw 0x29a9c0004d8e000c 0x029a9c0004d8e000 0x21e1c0000fc70000 0x821e1c0000fc7000

def z177 : W := mkw 0x0dbd800000000000 0x00dbd80000000000 0x0fffc00000000001 0xf0fffc0000000000

def z178 : W := mkw 0x4ffdbeea02004402 0x04ffdbeea0200440 0x7fffffff0e00c70f 0xf7fffffff0e00c70

def z179 : W := mkw 0x49e9964a00000000 0x049e9964a0000000 0x41e7cf3f00000003 0xd41e7cf3f0000000

def z180 : W := mkw 0x06dd3ce8361ce432 0xc06dd3ce8361ce43 0x0fd830c07e18c038 0x20fd830c07e18c03

def z181 : W := mkw 0x2dbfc0b0edbe08ac 0x82dbfc0b0edbe08a 0xefffc0f0ffff00fd 0xfefffc0f0ffff00f

def z182 : W := mkw 0x4ffffffb80e21a88 0x24ffffffb80e21a8 0xcfffffff81c03803 0xfcfffffff81c0380

def z183 : W := mkw 0x0002411180e21a88 0x20002411180e21a8 0x8000000081c03800 0x08000000081c0380

def z184 : W := mkw 0x196017004b405603 0x0196017004b40560 0x31e037000fc0c70e 0xb31e037000fc0c70

def z185 : W := mkw 0x0042551582e35fca 0x20042551582e35fc 0xf1e7ff3f8fe7ffcf 0xff1e7ff3f8fe7ffc

def z186 : W := mkw 0x0000000400010140 0x0000000040001014 0x7027cf3f002707c7 0xd7027cf3f002707c

def z187 : W := mkw 0x00c9144802004402 0x000c914480200440 0x71d934cc0e00c70f 0xb71d934cc0e00c70

def z188 : W := mkw 0x000000001000a000 0x0000000001000a00 0x90000000f000f80c 0x090000000f000f80

def z189 : W := mkw 0x4ffdbeee00010140 0x04ffdbeee0001014 0x7fffffff002707c7 0xf7fffffff002707c

def z190 : W := mkw 0x008b405d84af09d8 0x6008b405d84af09d 0x401fc0ff003f00f1 0x0401fc0ff003f00f

def z191 : W := mkw 0x6fffffffedff1bcc 0x26fffffffedff1bc 0xffffffffffff3fcf 0xfffffffffffff3fc

def z192 : W := mkw 0x0dbf8000a0300000 0x00dbf8000a030000 0x8fffc000f038000d 0xf8fffc000f038000

def z193 : W := mkw 0x020028001000a000 0x0020028001000a00 0xde1838c0f038f8ff 0x7de1838c0f038f8f

def z194 : W := mkw 0x4ffdbeea060c4412 0x44ffdbeea060c441 0x0fd830c00e18c038 0x20fd830c00e18c03

def z195 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x71ffffff0e3fc7ff 0xf71ffffff0e3fc7f

def z196 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xffe7ff3fffc0ff0f 0xfffe7ff3fffc0ff0

def z197 : W := mkw 0x0d34800000000000 0x00d3480000000000 0x0e26c00000000000 0x40e26c0000000000

def z198 : W := mkw 0x2fbfe8b0fdbea8ac 0x82fbfe8b0fdbea8a 0xfffff8f0fffff8ff 0xffffff8f0fffff8f

def z199 : W := mkw 0x041600b0a03008a0 0x8041600b0a03008a 0xd01e08f0803838f7 0x5d01e08f0803838f

def z200 : W := mkw 0x4ffdbeea3010a020 0x84ffdbeea3010a02 0x0fd830c07018c038 0x20fd830c07018c03

def z201 : W := mkw 0x0fbfa8b0b030a8a0 0x80fbfa8b0b030a8a 0xdffff8f0f038f8ff 0xfdffff8f0f038f8f

def z202 : W := mkw 0x20024004efbf455e 0x420024004efbf455 0xb0000000ffffc7fc 0x0b0000000ffffc7f

def z203 : W := mkw 0x3f76ff00fbf2f60f 0x03f76ff00fbf2f60 0xbfe6ff00ffc0ff0e 0xfbfe6ff00ffc0ff0

def z204 : W := mkw 0x0f3628b0f930a8a0 0x80f3628b0f930a8a 0xfffe38f0fff8f8ff 0xffffe38f0fff8f8f

def z205 : W := mkw 0x1b202b005940b201 0x01b202b005940b20 0xafe00b00ffc0380c 0xfafe00b00ffc0380

def z206 : W := mkw 0x261668b0fdbea8ac 0x8261668b0fdbea8a 0xfe1e38f0fffff8ff 0x7fe1e38f0fffff8f

def z207 : W := mkw 0x46563efab030a8a0 0x846563efab030a8a 0xde1e3ffff038f8ff 0x7de1e3ffff038f8f

def z208 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x41d930cc0e3fc0f9 0x241d930cc0e3fc0f

def z209 : W := mkw 0x0040144c02014552 0x40040144c0201455 0x500034cc0000c7f2 0x0500034cc0000c7f

def z210 : W := mkw 0x00c9154c064d5752 0x400c9154c064d575 0xf1f93fcc8fffffff 0xff1f93fcc8ffffff

def z211 : W := mkw 0x249fc04ca4bf015c 0x4249fc04ca4bf015 0x401fc0cc003f00f1 0x0401fc0cc003f00f

def z212 : W := mkw 0x5fffbffafb70fea3 0x85fffbffafb70fea 0xfffffffffff8ffff 0xffffffffffff8fff

def z213 : W := mkw 0x00c9554d06cf575a 0x600c9554d06cf575 0x71f9f7cf0fffc7ff 0xb71f9f7cf0fffc7f

def z214 : W := mkw 0x0040150002405602 0x0004015000240560 0xb1e03f008fc0ff0e 0xfb1e03f008fc0ff0

def z215 : W := mkw 0x6ffdbeea6d1c0004 0x06ffdbeea6d1c000 0x4fffffff7e18000b 0xf4fffffff7e18000

def z216 : W := mkw 0x4f36aab2b030a8a0 0x84f36aab2b030a8a 0xde3efbf3f038f8ff 0x7de3efbf3f038f8f

def z217 : W := mkw 0x1b627f00dbe2f60b 0x01b627f00dbe2f60 0xbfe7ff00ffe7ff0f 0xfbfe7ff00ffe7ff0

def z218 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfc03000ffc0ff0c 0x2bfc03000ffc0ff0

def z219 : W := mkw 0x06dd3ce800000000 0x006dd3ce80000000 0x4fdf3cfc00000003 0xf4fdf3cfc0000000

def z220 : W := mkw 0x0002401580a309c8 0x20002401580a309c 0x7007c43f002707c7 0x97007c43f002707c

def z221 : W := mkw 0x00890048040c0010 0x400890048040c001 0x001800c000180030 0x0001800c00018003

def z222 : W := mkw 0x0089004c040d0150 0x40089004c040d015 0x61d900cc0e3f00fd 0xb61d900cc0e3f00f

def z223 : W := mkw 0x0040144c02014552 0x40040144c0201455 0x700134cc0027c7f7 0x9700134cc0027c7f

def z224 : W := mkw 0x061669b5b0f3bbe8 0xa061669b5b0f3bbe 0xfe1e38f0f1ffffff 0x7fe1e38f0f1fffff

def z225 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000f3f00000002 0x040000f3f0000000

def z226 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x31d830c00e3fc7fc 0x231d830c00e3fc7f

def z227 : W := mkw 0x069f28fcb43da9f0 0xc069f28fcb43da9f 0xde1f38fcf03ff8ff 0x7de1f38fcf03ff8f

def z228 : W := mkw 0x0089004c060d4552 0x40089004c060d455 0x701900cc0e3fc7fd 0x0701900cc0e3fc7f

def z229 : W := mkw 0x2dbfc010edbe088c 0x02dbfc010edbe088 0xffffc830ffff38cf 0xfffffc830ffff38c

def z230 : W := mkw 0x0000000000000000 0x0000000000000000 0x500030c00000c0f2 0x0500030c00000c0f

def z231 : W := mkw 0x0920000000000000 0x0092000000000000 0x0fe0000000000000 0xf0fe000000000000

def z232 : W := mkw 0x2dffd55defff5fde 0x62dffd55defff5fd 0xffffffffffffffff 0xffffffffffffffff

def z233 : W := mkw 0x4ffdbeea060c4412 0x44ffdbeea060c441 0x4fffffff0e18c03b 0xf4fffffff0e18c03

def z234 : W := mkw 0x1f362bb0f970baa1 0x81f362bb0f970baa 0x8e260b30f1c03800 0x48e260b30f1c0380

def z235 : W := mkw 0x46543eea00000000 0x046543eea0000000 0x4e1e3fff00000003 0x74e1e3fff0000000

def z236 : W := mkw 0x02022810b030a8a0 0x802022810b030a8a 0x9e003800f038f8fe 0x79e003800f038f8f

def z237 : W := mkw 0x096014004b004402 0x0096014004b00440 0xbfe03400ffc0c70e 0xfbfe03400ffc0c70

def z238 : W := mkw 0x2f36e8b0f9b2a8ac 0x82f36e8b0f9b2a8a 0xde3ef8f0f1f8f8ff 0x7de3ef8f0f1f8f8f

def z239 : W := mkw 0x00cb555d86ef5fda 0x600cb555d86ef5fd 0xf1ffffff8fffffff 0xff1ffffff8ffffff

def z240 : W := mkw 0x196016004b004403 0x0196016004b00440 0x01c000000e000000 0x001c000000e00000

def z241 : W := mkw 0x2dbd80006d1c0004 0x02dbd80006d1c000 0xaff80000ffd8000c 0xfaff80000ffd8000

def z242 : W := mkw 0x1b627f15dbe3ffcb 0x21b627f15dbe3ffc 0xbfe03f00ffe7ffce 0xfbfe03f00ffe7ffc

def z243 : W := mkw 0x4fbdaaea00000000 0x04fbdaaea0000000 0x4e3fcbff00000001 0x44e3fcbff0000000

def z244 : W := mkw 0x0000000402014552 0x4000000040201455 0x100000000000c7f0 0x0100000000000c7f

def z245 : W := mkw 0x00c91448040c0000 0x000c91448040c000 0x61d934cc0e3f000f 0xb61d934cc0e3f000

def z246 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x0ffefbf300000000 0x60ffefbf30000000

def z247 : W := mkw 0x2dbfc105edff134c 0x22dbfc105edff134 0xafffc70fffff070d 0xfafffc70fffff070

def z248 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0x501e38f00038f8f3 0x0501e38f00038f8f

def z249 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0x8e3fc000f1ff0001 0x48e3fc000f1ff000

def z250 : W := mkw 0x2dffd44cefbf455e 0x42dffd44cefbf455 0xfffff4ccffffc7ff 0xffffff4ccffffc7f

def z251 : W := mkw 0x00c9144800000000 0x000c914480000000 0x41ffffff00000003 0xf41ffffff0000000

def z252 : W := mkw 0x0000000000000000 0x0000000000000000 0x0026cb3300000000 0x40026cb330000000

def z253 : W := mkw 0x0414000020100000 0x0041400002010000 0x0e18000070180008 0x20e1800007018000

def z254 : W := mkw 0x0000410500c31348 0x20000410500c3134 0x2000000001c70700 0x02000000001c7070

def z255 : W := mkw 0x2fbfe800fdbea00c 0x02fbfe800fdbea00 0xbffff800fffff80f 0xfbffff800fffff80

def z256 : W := mkw 0x100001004b405603 0x0100001004b40560 0x200000000fc00700 0x0200000000fc0070

def z257 : W := mkw 0x1b603e005b00e403 0x01b603e005b00e40 0x9fc03800fe00f80e 0x79fc03800fe00f80

def z258 : W := mkw 0x00000015000109c0 0x200000015000109c 0x4000003f000000c0 0x04000003f000000c

def z259 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0x8e1e38f0f018f838 0x68e1e38f0f018f83

def z260 : W := mkw 0x1b603e005b00e403 0x01b603e005b00e40 0x3fc034007e00c70e 0xb3fc034007e00c70

def z261 : W := mkw 0x00c91448060c4412 0x400c91448060c441 0x41d934cc0e18c03b 0xb41d934cc0e18c03

def z262 : W := mkw 0x3fffff4cfffff75f 0x43fffff4cfffff75 0xffffffccffffffff 0xfffffffccfffffff

def z263 : W := mkw 0x10024115dbe3ffcb 0x210024115dbe3ffc 0xf027cf3fffe7ffcf 0xdf027cf3fffe7ffc

def z264 : W := mkw 0x0002400080a20008 0x00002400080a2000 0xa000000081e70004 0x0a000000081e7000

def z265 : W := mkw 0x0040140002004402 0x0004014000200440 0x71d834c00e38c7ff 0xb71d834c00e38c7f

def z266 : W := mkw 0x6dbfc0eaedbe000c 0x06dbfc0eaedbe000 0xefffc0ffffff000d 0xfefffc0ffffff000

def z267 : W := mkw 0x1be93e4c5f0de553 0x41be93e4c5f0de55 0x7fd934cc7e3fc7ff 0xb7fd934cc7e3fc7f

def z268 : W := mkw 0x449d80ea00000000 0x0449d80ea0000000 0x403fcfff00000003 0xd403fcfff0000000

def z269 : W := mkw 0x0dbd8000040c0000 0x00dbd8000040c000 0x2fffc0000e3f000d 0xf2fffc0000e3f000

def z270 : W := mkw 0x020269b590e3bbe8 0xa020269b590e3bbe 0xf027ffff81e7fff7 0xdf027ffff81e7fff

def z271 : W := mkw 0x29e9d44c4f8f455e 0x429e9d44c4f8f455 0x71f9f4cc0fffc7ff 0xb71f9f4cc0fffc7f

def z272 : W := mkw 0x061428b01000a8a0 0x8061428b01000a8a 0x5e1e38f00000f8f3 0x75e1e38f00000f8f

def z273 : W := mkw 0x0000011500411bc0 0x20000011500411bc 0x70010f3f00273fc7 0x970010f3f00273fc

def z274 : W := mkw 0x120029005b40f603 0x0120029005b40f60 0xbe003800ffc0ff0e 0x7be003800ffc0ff0

def z275 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0x5007cf3f00273fc3 0x05007cf3f00273fc

def z276 : W := mkw 0x30024100fffef60f 0x030024100fffef60 0xb0000000ffffff0c 0x0b0000000ffffff0

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z278 : W := mkw 0x020029b51041bbe0 0xa020029b51041bbe 0x50003fff0000fff2 0x050003fff0000fff

def z279 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x71c1040c0e2707c7 0x971c1040c0e2707c

def z280 : W := mkw 0x100001005b40f603 0x0100001005b40f60 0xb0200f00ffc0ff0e 0xdb0200f00ffc0ff0

def z281 : W := mkw 0x249fc000a4be000c 0x0249fc000a4be000 0x21dfc0000e3f000d 0xb21dfc0000e3f000

def z282 : W := mkw 0x4f34aaa200000000 0x04f34aaa20000000 0x4e27cf3f00000003 0xd4e27cf3f0000000

def z283 : W := mkw 0x4f36ebb380e21a88 0x24f36ebb380e21a8 0x8e26cb3381c03800 0x48e26cb3381c0380

def z284 : W := mkw 0x12c93f4c164df753 0x412c93f4c164df75 0x71d93fcc0e3fffff 0xb71d93fcc0e3ffff

def z285 : W := mkw 0x00890004060d4552 0x400890004060d455 0x31d900000e3fc7fd 0xb31d900000e3fc7f

def z286 : W := mkw 0x00c91448060c4412 0x400c91448060c441 0x21d930c00e3fc03d 0xb21d930c00e3fc03

def z287 : W := mkw 0x2dffd44cefbf455e 0x42dffd44cefbf455 0xafffc40cffff070d 0xfafffc40cffff070

def z288 : W := mkw 0x469fa8fab030a8a0 0x8469fa8fab030a8a 0xde1ff8fff038f8ff 0x7de1ff8fff038f8f

def z289 : W := mkw 0x3dffd700effe560f 0x03dffd700effe560 0xafffc700ffff070d 0xfafffc700ffff070

def z290 : W := mkw 0x4fffbefab030a8a0 0x84fffbefab030a8a 0xcffffffff0003803 0xfcffffffff000380

def z291 : W := mkw 0x0b202a0000000000 0x00b202a000000000 0x0e200b0000000000 0x40e200b000000000

def z292 : W := mkw 0x2fbfa8b0fd3ca8a4 0x82fbfa8b0fd3ca8a 0xdfde38f0fe38f8ff 0x7dfde38f0fe38f8f

def z293 : W := mkw 0x1f763eb0fb30eca3 0x81f763eb0fb30eca 0xdfde38f0fe38f8ff 0x7dfde38f0fe38f8f

def z294 : W := mkw 0x0002401180a20888 0x20002401180a2088 0x0006c03300000000 0x00006c0330000000

def z295 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e000000f000000c 0x78e000000f000000

def z296 : W := mkw 0x00c91400060c4402 0x000c91400060c440 0x31d934000e3fc70f 0xb31d934000e3fc70

def z297 : W := mkw 0x0000001000000880 0x0000000100000088 0x50000830000038c2 0x050000830000038c

def z298 : W := mkw 0x20024115edff1bcc 0x220024115edff1bc 0xb0000000ffff3fcc 0x0b0000000ffff3fc

def z299 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xfff83fc0fff8ffff 0xffff83fc0fff8fff

def z300 : W := mkw 0x49e9964e060d4552 0x449e9964e060d455 0x21e1c70f0e070700 0x821e1c70f0e07070

def z301 : W := mkw 0x3fffff15ffffffcf 0x23fffff15ffffffc 0xffffff3fffffffcf 0xfffffff3fffffffc

def z302 : W := mkw 0x200040004d8e000c 0x0200040004d8e000 0x200000000fc70000 0x0200000000fc7000

def z303 : W := mkw 0x0000400500830148 0x2000040050083014 0x0001c00f00070000 0x00001c00f0007000

def z304 : W := mkw 0x0002401580a309c8 0x20002401580a309c 0x00000000002700c0 0x000000000002700c

def z305 : W := mkw 0x4ffdbfff00411bc0 0x24ffdbfff00411bc 0x5fffffff00003fc3 0xf5fffffff00003fc

def z306 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0x31e03f000fc0ff02 0x831e03f000fc0ff0

def z307 : W := mkw 0x6fbfeaa2edbe000c 0x06fbfeaa2edbe000 0xafffcb33ffff000d 0xfafffcb33ffff000

def z308 : W := mkw 0x4ffdbeea3010a020 0x84ffdbeea3010a02 0x4fffffff7018c03b 0xf4fffffff7018c03

def z309 : W := mkw 0x46ddbeea00000000 0x046ddbeea0000000 0x401fffff00000003 0x0401fffff0000000

def z310 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde060830f02038c7 0x5de060830f02038c

def z311 : W := mkw 0x2dbf8000ed3c0004 0x02dbf8000ed3c000 0x8fde0000fe38000d 0x78fde0000fe38000

def z312 : W := mkw 0x061669b5b0f3bbe8 0xa061669b5b0f3bbe 0xfe27cf3ff1e73fc7 0xdfe27cf3ff1e73fc

def z313 : W := mkw 0x020028001000a000 0x0020028001000a00 0x9e003800f000f80e 0x79e003800f000f80

def z314 : W := mkw 0x0dfd944c060d4552 0x40dfd944c060d455 0x7ffff4cc0e3fc7ff 0xf7ffff4cc0e3fc7f

def z315 : W := mkw 0x2d34800069100004 0x02d3480006910000 0x0e00000070000000 0x00e0000007000000

def z316 : W := mkw 0x020028001000a000 0x0020028001000a00 0x8e000800f0003800 0x48e000800f000380

def z317 : W := mkw 0x0000000002004402 0x0000000000200440 0x300000000e00c70c 0x0300000000e00c70

def z318 : W := mkw 0x0089004c040d0150 0x40089004c040d015 0x501930cc003fc0ff 0x3501930cc003fc0f

def z319 : W := mkw 0x0040140002004402 0x0004014000200440 0x01c030000e00c008 0x201c030000e00c00

def z320 : W := mkw 0x2fbfe8a0edbe000c 0x02fbfe8a0edbe000 0xeffff8f0ffff000f 0xfeffff8f0ffff000

def z321 : W := mkw 0x1b226b11d9e2ba89 0x21b226b11d9e2ba8 0x8e26cb33f1c03800 0x48e26cb33f1c0380

def z322 : W := mkw 0x00890000040c0000 0x000890000040c000 0x21c100000e070000 0x821c100000e07000

def z323 : W := mkw 0x4f74beea00000000 0x04f74beea0000000 0x4e26ffff00000002 0x44e26ffff0000000

def z324 : W := mkw 0x49ebd75f80e31bc8 0x249ebd75f80e31bc 0xf1e7cf3f81e73fc7 0xdf1e7cf3f81e73fc

def z325 : W := mkw 0x061428a000000000 0x0061428a00000000 0x5e1e38f00038c0ff 0x75e1e38f00038c0f

def z326 : W := mkw 0x2d36c111e9f21a8c 0x22d36c111e9f21a8 0x8e26cb33f1c03800 0x48e26cb33f1c0380

def z327 : W := mkw 0x2fbfe8b0fdbea8ac 0x82fbfe8b0fdbea8a 0xafffc830ffff380d 0xfafffc830ffff380

def z328 : W := mkw 0x00cb145c862d4dd2 0x400cb145c862d4dd 0xf1df3cfc8e3fffff 0xff1df3cfc8e3ffff

def z329 : W := mkw 0x09a9800000000000 0x009a980000000000 0x01e1c00000000000 0x801e1c0000000000

def z330 : W := mkw 0x4ffdbeea49000000 0x04ffdbeea4900000 0xefffffffffc0000f 0xfefffffffffc0000

def z331 : W := mkw 0x269fe8b0b4bea8ac 0x8269fe8b0b4bea8a 0xde1ff8f0f03ff8ff 0x7de1ff8f0f03ff8f

def z332 : W := mkw 0x4fffffff80e31bc8 0x24fffffff80e31bc 0xffffffff81e73fc7 0xfffffffff81e73fc

def z333 : W := mkw 0x2d36c000e9b2000c 0x02d36c000e9b2000 0x8e26c000f1c00000 0x48e26c000f1c0000

def z334 : W := mkw 0x1be93f485b40f603 0x01be93f485b40f60 0xfff93fccffc0ff0f 0xffff93fccffc0ff0

def z335 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x0ff9f7cf00000000 0xa0ff9f7cf0000000

def z336 : W := mkw 0x6ffffeeaedbe000c 0x06ffffeeaedbe000 0xaffff0c0ffff000d 0xfaffff0c0ffff000

def z337 : W := mkw 0x020028b01000a8a0 0x8020028b01000a8a 0x0000083000003800 0x0000008300000380

def z338 : W := mkw 0x42002aa200000000 0x042002aa20000000 0x00000b3300000000 0x000000b330000000

def z339 : W := mkw 0x4dfd96ea00000000 0x04dfd96ea0000000 0x41ffc7ff00000001 0x841ffc7ff0000000

def z340 : W := mkw 0x0920000049000000 0x0092000004900000 0x21e000000fc00000 0x821e000000fc0000

def z341 : W := mkw 0x196017005b40f603 0x0196017005b40f60 0xb1e00700ffc0ff0c 0x8b1e00700ffc0ff0

def z342 : W := mkw 0x1b607f055bc3f74b 0x21b607f055bc3f74 0xbfe1ff0fffc7ff0e 0xfbfe1ff0fffc7ff0

def z343 : W := mkw 0x041600b0a03008a0 0x8041600b0a03008a 0x501e30f00038c0ff 0x3501e30f00038c0f

def z344 : W := mkw 0x00020010a03008a0 0x800020010a03008a 0x00000000003800f0 0x000000000003800f

def z345 : W := mkw 0x192001005b40f603 0x0192001005b40f60 0xbfe00000ffc0ff0c 0xfbfe00000ffc0ff0

def z346 : W := mkw 0x069f28b0b43ca8a0 0x8069f28b0b43ca8a 0xffdf38f0fe3ff8ff 0xfffdf38f0fe3ff8f

def z347 : W := mkw 0x061629b5b071bbe0 0xa061629b5b071bbe 0xde1e3ffff038ffff 0x7de1e3ffff038fff

def z348 : W := mkw 0x0089000000000000 0x0008900000000000 0x01d9000000000001 0xb01d900000000000

def z349 : W := mkw 0x061428a01000a000 0x0061428a01000a00 0xde1e38f0f000f80f 0x7de1e38f0f000f80

def z350 : W := mkw 0x000000b0000008a0 0x8000000b0000008a 0x400000f0000000f0 0x0400000f0000000f

def z351 : W := mkw 0x1b603f045b41f743 0x01b603f045b41f74 0xffe13f0cffe7ffcf 0xfffe13f0cffe7ffc

def z352 : W := mkw 0x0dbfc00080a20008 0x00dbfc00080a2000 0xafffc00081e70005 0xfafffc00081e7000

def z353 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xa027cf3f81c73f00 0xca027cf3f81c73f0

def z354 : W := mkw 0x0000410500c31348 0x20000410500c3134 0x7021c70f01e707c7 0x97021c70f01e707c

def z355 : W := mkw 0x2dffd448edbe000c 0x02dffd448edbe000 0xeffff4ccffff000f 0xfeffff4ccffff000

def z356 : W := mkw 0x0000000000000000 0x0000000000000000 0x21c000000e00000c 0xb21c000000e00000

def z357 : W := mkw 0x0000011500411bc0 0x20000011500411bc 0xf0200f3f81c03fc6 0xdf0200f3f81c03fc

def z358 : W := mkw 0x4fffffffb0f3bbe8 0xa4fffffffb0f3bbe 0xfffffffff1ffffff 0xffffffffff1fffff

def z359 : W := mkw 0x5fffffffdbe3ffcb 0x25fffffffdbe3ffc 0xffffffffffe7ffcf 0xfffffffffffe7ffc

def z360 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x0fd830c000000000 0x20fd830c00000000

def z361 : W := mkw 0x02403c001200e402 0x002403c001200e40 0xbfc03c00fe00ff0e 0xfbfc03c00fe00ff0

def z362 : W := mkw 0x049f00fca43d09f0 0xc049f00fca43d09f 0x401f00fc003f00f1 0x0401f00fc003f00f

def z363 : W := mkw 0x00401404060d4552 0x400401404060d455 0x31c034000e3fc7fe 0xb31c034000e3fc7f

def z364 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0x1fc03f007e00ff0a 0x21fc03f007e00ff0

def z365 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf006083081e73fc7 0x5f006083081e73fc

def z366 : W := mkw 0x5ffdbfea5940b201 0x05ffdbfea5940b20 0xcffffffff1c03803 0xfcffffffff1c0380

def z367 : W := mkw 0x2d36c000edbe000c 0x02d36c000edbe000 0xae26c000ffff000c 0x4ae26c000ffff000

def z368 : W := mkw 0x061428b03010a8a0 0x8061428b03010a8a 0x5e1838f07018f8fa 0x25e1838f07018f8f

def z369 : W := mkw 0x00c91448060c4412 0x400c91448060c441 0x51d830c00e38c0ff 0x351d830c00e38c0f

def z370 : W := mkw 0x100001045f4df753 0x4100001045f4df75 0xb0000000fffffffc 0x0b0000000fffffff

def z371 : W := mkw 0x4040164a00000000 0x04040164a0000000 0x0000070f00000000 0x00000070f0000000

def z372 : W := mkw 0x0000000000000000 0x0000000000000000 0x001830c00018c038 0x2001830c00018c03

def z373 : W := mkw 0x0000400000820008 0x0000040000082000 0x2021c00001c70000 0x82021c00001c7000

def z374 : W := mkw 0x196057054bc3574b 0x2196057054bc3574 0x21e1c70f0fc70700 0x821e1c70f0fc7070

def z375 : W := mkw 0x0d360000e9300000 0x00d360000e930000 0xaffe0000fff8000d 0xfaffe0000fff8000

def z376 : W := mkw 0x4fffbeeaa0300000 0x04fffbeeaa030000 0xcffffffff038000f 0xfcffffffff038000

def z377 : W := mkw 0x00cb555d86ef5fda 0x600cb555d86ef5fd 0xf1e7cf3f8fe73fc7 0xdf1e7cf3f8fe73fc

def z378 : W := mkw 0x1b623f10fb70fea3 0x81b623f10fb70fea 0xbfe03f00fff8fffe 0xfbfe03f00fff8fff

def z379 : W := mkw 0x1f763f00fb70f603 0x01f763f00fb70f60 0xbffe3f00fff8ff0f 0xfbffe3f00fff8ff0

def z380 : W := mkw 0x44dd94ee060d4552 0x444dd94ee060d455 0x71dff4ff0e3fc7ff 0xb71dff4ff0e3fc7f

def z381 : W := mkw 0x09224000c9a20008 0x009224000c9a2000 0xafe7c000ffe7000d 0xfafe7c000ffe7000

def z382 : W := mkw 0x4920820200000000 0x0492082020000000 0x0020c30300000000 0x00020c3030000000

def z383 : W := mkw 0x449d80ee040d0150 0x4449d80ee040d015 0x401fc0ff003f00f1 0x0401fc0ff003f00f

def z384 : W := mkw 0x4be9be4a00000000 0x04be9be4a0000000 0x0fe1ff0f00000002 0xf0fe1ff0f0000000

def z385 : W := mkw 0x100001001240f603 0x0100001001240f60 0x100000000000ff00 0x0100000000000ff0

def z386 : W := mkw 0x0002411180e21a88 0x20002411180e21a8 0xb026cf3381c03f06 0xdb026cf3381c03f0

def z387 : W := mkw 0x100000005b00e403 0x0100000005b00e40 0x000000007e00c008 0x0000000007e00c00

def z388 : W := mkw 0x06563cb0b230eca2 0x806563cb0b230eca 0xffde3cf0fe38ffff 0xfffde3cf0fe38fff

def z389 : W := mkw 0x04df144ca63d4552 0x404df144ca63d455 0xffdf34ccfe3fc7ff 0xfffdf34ccfe3fc7f

def z390 : W := mkw 0x0be93e4c060d4552 0x40be93e4c060d455 0x7ff93fcc0e3fc7ff 0xf7ff93fcc0e3fc7f

def z391 : W := mkw 0x020228b09020a8a0 0x8020228b09020a8a 0xd00638f08020f8f7 0x5d00638f08020f8f

def z392 : W := mkw 0x061428a03010a020 0x8061428a03010a02 0x0e00000070000000 0x00e0000007000000

def z393 : W := mkw 0x0000004c00010150 0x40000004c0001015 0x400000cc000000f0 0x0400000cc000000f

def z394 : W := mkw 0x0000410500c31348 0x20000410500c3134 0xb021cf0f81c73f06 0xdb021cf0f81c73f0

def z395 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xb0200f0081e73fc6 0xdb0200f0081e73fc

def z396 : W := mkw 0x0920010049401200 0x0092001004940120 0xbfe00f00ffc03f0e 0xfbfe00f00ffc03f0

def z397 : W := mkw 0x42403eea00000000 0x042403eea0000000 0x000030c000000000 0x0000030c00000000

def z398 : W := mkw 0x1b603f004b405603 0x01b603f004b40560 0x2fe03f000fc00702 0xf2fe03f000fc0070

def z399 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0x9e203f00f1c0ff02 0x49e203f00f1c0ff0

def z400 : W := mkw 0x0002411180e21a88 0x20002411180e21a8 0xc027cf3f81c03803 0xdc027cf3f81c0380

def z401 : W := mkw 0x0000000400010140 0x0000000040001014 0x2001040c00070700 0x82001040c0007070

def z402 : W := mkw 0x2fbfe8a0fdbea02c 0x82fbfe8a0fdbea02 0xaffff0c0ffffc03d 0xfaffff0c0ffffc03

def z403 : W := mkw 0x2920c0004982000c 0x02920c0004982000 0x0020c00001c00000 0x00020c00001c0000

def z404 : W := mkw 0x00000004040d0150 0x400000004040d015 0x00000000003f00f0 0x000000000003f00f

def z405 : W := mkw 0x0000000400010140 0x0000000040001014 0x5000040c000007c2 0x05000040c000007c

def z406 : W := mkw 0x09a900004d0c0000 0x009a900004d0c000 0xaff90000ffff000d 0xfaff90000ffff000

def z407 : W := mkw 0x041400a000000000 0x0041400a00000000 0x401e00f000000001 0x0401e00f00000000

def z408 : W := mkw 0x249fc115a4ff1bcc 0x2249fc115a4ff1bc 0xf03fcf3f81ff3fc7 0xdf03fcf3f81ff3fc

def z409 : W := mkw 0x061428a03010a020 0x8061428a03010a02 0x9e1838c0f018f83e 0x79e1838c0f018f83

def z410 : W := mkw 0x00890000040c0000 0x000890000040c000 0x00190000003f0001 0x000190000003f000

def z411 : W := mkw 0x24dfd44ca6bf455e 0x424dfd44ca6bf455 0x71dff4cc0e3fc7ff 0xb71dff4cc0e3fc7f

def z412 : W := mkw 0x061628b0a03008a0 0x8061628b0a03008a 0x4e1e38f0003800f3 0x74e1e38f0003800f

def z413 : W := mkw 0x00cb544c86af455a 0x400cb544c86af455 0xf1fff4cc8fffc7ff 0xff1fff4cc8fffc7f

def z414 : W := mkw 0x04df14fca63d4df2 0xc04df14fca63d4df 0x71df34fc0e3fc7ff 0xb71df34fc0e3fc7f

def z415 : W := mkw 0x4dbd80ea00000000 0x04dbd80ea0000000 0x4fffc0ff00000001 0xf4fffc0ff0000000

def z416 : W := mkw 0x0b603e0002004402 0x00b603e000200440 0x3fe03f000e00c70e 0xf3fe03f000e00c70

def z417 : W := mkw 0x00020010b030a8a0 0x800020010b030a8a 0xd01830c0f038f8ff 0x3d01830c0f038f8f

def z418 : W := mkw 0x0000410100c21208 0x20000410100c2120 0x0020c30301c00000 0x00020c30301c0000

def z419 : W := mkw 0x00c9144800000000 0x000c914480000000 0x01d830c000000000 0x201d830c00000000

def z420 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x0ff83fc000000002 0xf0ff83fc00000000

def z421 : W := mkw 0x0000410500c31348 0x20000410500c3134 0x6027cf3f01c70703 0xd6027cf3f01c7070

def z422 : W := mkw 0x29e9d44c4f8f455e 0x429e9d44c4f8f455 0x21e1c40c0fc70700 0x821e1c40c0fc7070

def z423 : W := mkw 0x6ffffeeae9b2000c 0x06ffffeeae9b2000 0xcffffffff1c00003 0xfcffffffff1c0000

def z424 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0x8e1e0830f038380d 0x78e1e0830f038380

def z425 : W := mkw 0x0dbd800000000000 0x00dbd80000000000 0x4fffcf3f00000003 0xf4fffcf3f0000000

def z426 : W := mkw 0x4fffbefab030a8a0 0x84fffbefab030a8a 0xdfde38f0f038f8ff 0x7dfde38f0f038f8f

def z427 : W := mkw 0x2dbfc04cedbf015c 0x42dbfc04cedbf015 0xefffc0ccffff00fd 0xfefffc0ccffff00f

def z428 : W := mkw 0x1be93f005f4cf603 0x01be93f005f4cf60 0xbff93f00ffffff0f 0xfbff93f00ffffff0

def z429 : W := mkw 0x5ffdbfea4b405603 0x05ffdbfea4b40560 0x6fffffff0fc00703 0xf6fffffff0fc0070

def z430 : W := mkw 0x29abc000edbe000c 0x029abc000edbe000 0xa1e1c000ffff000c 0x8a1e1c000ffff000

def z431 : W := mkw 0x06162800b030a000 0x006162800b030a00 0x9e1e3800f038f80f 0x79e1e3800f038f80

def z432 : W := mkw 0x0002400080a20008 0x00002400080a2000 0xe027cf3f81e70007 0xde027cf3f81e7000

def z433 : W := mkw 0x061668b5b0b3a9e8 0xa061668b5b0b3a9e 0xde1ff8fff03ff8ff 0x7de1ff8fff03ff8f

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0x401830c000000003 0x3401830c00000000

def z435 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x71c134cc0e07c7f2 0x871c134cc0e07c7f

def z436 : W := mkw 0x2dfd944c6f1d4556 0x42dfd944c6f1d455 0x7fd934cc7e3fc7ff 0xb7fd934cc7e3fc7f

def z437 : W := mkw 0x1be93f4c5f4df753 0x41be93f4c5f4df75 0xbfe13f0cffc7ff0e 0xfbfe13f0cffc7ff0

def z438 : W := mkw 0x4f34aaa200000000 0x04f34aaa20000000 0x4e3efbf300000003 0x74e3efbf30000000

def z439 : W := mkw 0x1f763fb0fb70fea3 0x81f763fb0fb70fea 0xbfe63f30ffc0ff0e 0xfbfe63f30ffc0ff0

def z440 : W := mkw 0x0dfd944800000000 0x00dfd94480000000 0x4ffff4cc00000003 0xf4ffff4cc0000000

def z441 : W := mkw 0x061669b1b0f2baa8 0xa061669b1b0f2baa 0xde3efbf3f1f8f8ff 0x7de3efbf3f1f8f8f

def z442 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xce1e38f0f0003803 0x7ce1e38f0f000380

def z443 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x61d904cc0e3f07f1 0x861d904cc0e3f07f

def z444 : W := mkw 0x4089804a00000000 0x04089804a0000000 0x0001c00f00000000 0x00001c00f0000000

def z445 : W := mkw 0x16563fb0b270fea3 0x816563fb0b270fea 0xde1e3ff0f038ffff 0x7de1e3ff0f038fff

def z446 : W := mkw 0x0040144c02014552 0x40040144c0201455 0x71c034cc0e00c7fe 0xb71c034cc0e00c7f

def z447 : W := mkw 0x0040140402014542 0x0004014040201454 0x71c1340c0e27c7cf 0xb71c1340c0e27c7c

def z448 : W := mkw 0x0040140002004402 0x0004014000200440 0x100034000000c702 0x0100034000000c70

def z449 : W := mkw 0x1be93e485f0ce413 0x41be93e485f0ce41 0x0fd830c07e18c038 0x20fd830c07e18c03

def z450 : W := mkw 0x000000101000a8a0 0x8000000101000a8a 0x100000000000f8f0 0x0100000000000f8f

def z451 : W := mkw 0x020028001000a000 0x0020028001000a00 0x0e0030007000c008 0x20e0030007000c00

def z452 : W := mkw 0x09224115c9e31bc8 0x209224115c9e31bc 0xffe7cf3fffe73fcf 0xfffe7cf3fffe73fc

def z453 : W := mkw 0x7fffffeafffef60f 0x07fffffeafffef60 0xffffffffffffff0f 0xfffffffffffffff0

def z454 : W := mkw 0x0000010500411340 0x2000001050041134 0x0000070f00000700 0x00000070f0000070

def z455 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xafe00f00ffc03f00 0xcafe00f00ffc03f0

def z456 : W := mkw 0x06df3cf8b030a8a0 0x806df3cf8b030a8a 0xdfdf3cfcf038f8ff 0xfdfdf3cfcf038f8f

def z457 : W := mkw 0x0002401580a309c8 0x20002401580a309c 0xe027c03f81e700c5 0xde027c03f81e700c

def z458 : W := mkw 0x0000000000000000 0x0000000000000000 0x4001040c00000003 0x94001040c0000000

def z459 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf03fffff81ffffff 0xff03fffff81fffff

def z460 : W := mkw 0x20024115edff1bcc 0x220024115edff1bc 0xf027cf3fffff3fcf 0xdf027cf3fffff3fc

def z461 : W := mkw 0x12403e001200e403 0x012403e001200e40 0x000030000000c000 0x0000030000000c00

def z462 : W := mkw 0x2dbfc100edfe120c 0x02dbfc100edfe120 0xbfffcf00ffff3f0f 0xfbfffcf00ffff3f0

def z463 : W := mkw 0x2dbfc015edbf09cc 0x22dbfc015edbf09c 0xefffc03fffff00cd 0xfefffc03fffff00c

def z464 : W := mkw 0x2fbda8a07d1ca024 0x82fbda8a07d1ca02 0x0fd830c07e18c038 0x20fd830c07e18c03

def z465 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf0000f3f81e73fc6 0x0f0000f3f81e73fc

def z466 : W := mkw 0x00c9144c02014552 0x400c9144c0201455 0x51d934cc0000c7f3 0xb51d934cc0000c7f

def z467 : W := mkw 0x4f34aaa200000000 0x04f34aaa20000000 0x0e00000000000000 0x00e0000000000000

def z468 : W := mkw 0x5ffdbeea5b00e403 0x05ffdbeea5b00e40 0x4fffffff7e00c00b 0xf4fffffff7e00c00

def z469 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x31c1340c0e07c70e 0xb31c1340c0e07c70

def z470 : W := mkw 0x00c9554d06cf575a 0x600c9554d06cf575 0x21e1c70f0fc70700 0x821e1c70f0fc7070

def z471 : W := mkw 0x1f743fa07b50f623 0x81f743fa07b50f62 0xbff83fc0ffd8ff3e 0xfbff83fc0ffd8ff3

def z472 : W := mkw 0x041400a020100020 0x8041400a02010002 0x001800c000180030 0x0001800c00018003

def z473 : W := mkw 0x049d800000000000 0x0049d80000000000 0x001fc00000000001 0x0001fc0000000000

def z474 : W := mkw 0x0000010000401200 0x0000001000040120 0xb000000081c03f04 0x0b000000081c03f0

def z475 : W := mkw 0x449d80ea00000000 0x0449d80ea0000000 0x001800c000000000 0x0001800c00000000

def z476 : W := mkw 0x0000000000000000 0x0000000000000000 0x0027c00000000001 0xd0027c0000000000

def z477 : W := mkw 0x00000000040c0000 0x000000000040c000 0x200000000e3f000c 0x0200000000e3f000

def z478 : W := mkw 0x24164000edbe000c 0x024164000edbe000 0xae1e0000ffff000d 0x7ae1e0000ffff000

def z479 : W := mkw 0x0dbd800049000000 0x00dbd80004900000 0xafffc000ffc0000d 0xfafffc000ffc0000

def z480 : W := mkw 0x0f743ea000000000 0x00f743ea00000000 0x4ffe3ff000000003 0xf4ffe3ff00000000

def z481 : W := mkw 0x29abc115cdef1bcc 0x229abc115cdef1bc 0xf1e7cf3f8fe73fc7 0xdf1e7cf3f8fe73fc

def z482 : W := mkw 0x4ffffeff80a309c8 0x24ffffeff80a309c 0x4fffffff002700c3 0xf4fffffff002700c

def z483 : W := mkw 0x44dd94ea00000000 0x044dd94ea0000000 0x41dff4ff00000003 0xb41dff4ff0000000

def z484 : W := mkw 0x12403f001240f603 0x012403f001240f60 0x31c03f000e00ff0e 0xb31c03f000e00ff0

def z485 : W := mkw 0x42c93eea00000000 0x042c93eea0000000 0x41d93fff00000003 0xb41d93fff0000000

def z486 : W := mkw 0x1b202b005b40f603 0x01b202b005b40f60 0xbe200b00ffc0ff0c 0x4be200b00ffc0ff0

def z487 : W := mkw 0x10020110fb70fea3 0x810020110fb70fea 0xb0000000fff8fffc 0x0b0000000fff8fff

def z488 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x21d9040c0e3f070d 0xb21d9040c0e3f070

def z489 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xb026cb3381e73fc4 0x4b026cb3381e73fc

def z490 : W := mkw 0x00024115b0f3bbe8 0xa00024115b0f3bbe 0xf027cf3ff1ffffff 0xdf027cf3ff1fffff

def z491 : W := mkw 0x0040155d02415fd2 0x60040155d02415fd 0x50003fff0000fff2 0x050003fff0000fff

def z492 : W := mkw 0x0000010000401200 0x0000001000040120 0x10000f0000003f02 0x010000f0000003f0

def z493 : W := mkw 0x0042555d82e35fda 0x60042555d82e35fd 0xf027ffff81e7fff7 0xdf027ffff81e7fff

def z494 : W := mkw 0x0002001080200880 0x0000200108020088 0xd01e38f08038f8ff 0x7d01e38f08038f8f

def z495 : W := mkw 0x469da8ea00000000 0x0469da8ea0000000 0x4e1ff8ff00000003 0x74e1ff8ff0000000

def z496 : W := mkw 0x0002401080a20888 0x00002401080a2088 0xf027c83081e738c7 0xdf027c83081e738c

def z497 : W := mkw 0x0fbda8a000000000 0x00fbda8a00000000 0x4ffff8f000000003 0xf4ffff8f00000000

def z498 : W := mkw 0x0089004800000000 0x0008900480000000 0x401900cc00000001 0x0401900cc0000000

def z499 : W := mkw 0x20cb544cefbf455e 0x420cb544cefbf455 0xf1d934ccffffc7ff 0xbf1d934ccffffc7f

def z500 : W := mkw 0x49e9d74f00c31348 0x249e9d74f00c3134 0x21e1c70f01c70700 0x821e1c70f01c7070

def z501 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xc027cb3f81e738c1 0x4c027cb3f81e738c

def z502 : W := mkw 0x008b411584ef1bc8 0x2008b411584ef1bc 0xf1ffcf3f8fff3fcf 0xff1ffcf3f8fff3fc

def z503 : W := mkw 0x061628a0a0300000 0x0061628a0a030000 0xce1e38f0f038000f 0x7ce1e38f0f038000

def z504 : W := mkw 0x041640b5a0b309e8 0xa041640b5a0b309e 0x401fc0ff003f00f1 0x0401fc0ff003f00f

def z505 : W := mkw 0x100001005940b201 0x0100001005940b20 0x80000000f1c03800 0x080000000f1c0380

def z506 : W := mkw 0x1b603e005b00e403 0x01b603e005b00e40 0xafe03000ffc0c00c 0xfafe03000ffc0c00

def z507 : W := mkw 0x1b226b15d9e3bbc9 0x21b226b15d9e3bbc 0xfe27cf3ff1e73fc7 0xdfe27cf3ff1e73fc

def z508 : W := mkw 0x0040144c060d4552 0x40040144c060d455 0x700034cc0e3fc7fe 0x0700034cc0e3fc7f

def z509 : W := mkw 0x2dbfc004edbf014c 0x02dbfc004edbf014 0xffffc40cffff07cf 0xfffffc40cffff07c

def z510 : W := mkw 0x12427f1592e3ffcb 0x212427f1592e3ffc 0xf027ff3f81e7ffc7 0xdf027ff3f81e7ffc

def z511 : W := mkw 0x0000011500411bc0 0x20000011500411bc 0x1000000000003fc0 0x01000000000003fc

def z512 : W := mkw 0x1f767fb5fbf3ffeb 0xa1f767fb5fbf3ffe 0xffffffffffffffff 0xffffffffffffffff

def z513 : W := mkw 0x0000011100401a80 0x20000011100401a8 0x00000b3300003800 0x000000b330000380

def z514 : W := mkw 0x1b202b005940b201 0x01b202b005940b20 0xbe200f00f1c03f06 0xdbe200f00f1c03f0

def z515 : W := mkw 0x4fffbefaa03008a0 0x84fffbefaa03008a 0x4fffffff003800f3 0xf4fffffff003800f

def z516 : W := mkw 0x12403f001240f603 0x012403f001240f60 0xb0203f0081c0ff06 0xdb0203f0081c0ff0

def z517 : W := mkw 0x0be93e4800000000 0x00be93e480000000 0x4ff93fcc00000003 0xf4ff93fcc0000000

def z518 : W := mkw 0x020028001000a000 0x0020028001000a00 0x100038000000f802 0x0100038000000f80

def z519 : W := mkw 0x00c9144c040d0150 0x400c9144c040d015 0x41d934cc003f00f3 0xb41d934cc003f00f

def z520 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x501934cc003fc7f3 0x0501934cc003fc7f

def z521 : W := mkw 0x2ffffe00edbe000c 0x02ffffe00edbe000 0xafffff00ffff000f 0xfafffff00ffff000

def z522 : W := mkw 0x2dffd448efbe441e 0x42dffd448efbe441 0xaffff0c0ffffc03d 0xfaffff0c0ffffc03

def z523 : W := mkw 0x0000010000401200 0x0000001000040120 0x2020070001c00700 0x82020070001c0070

def z524 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4fde38f000000003 0x74fde38f00000000

def z525 : W := mkw 0x0000000000000000 0x0000000000000000 0x100000000038c0fc 0x0100000000038c0f

def z526 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0x9e063830f000f80e 0x79e063830f000f80

def z527 : W := mkw 0x0b2028005900a000 0x00b2028005900a00 0xbfe03800ffc0f80e 0xfbfe03800ffc0f80

def z528 : W := mkw 0x061629b0b070baa0 0x8061629b0b070baa 0xfe3e3ff0f1f8ffff 0xffe3e3ff0f1f8fff

def z529 : W := mkw 0x0002411180e21a88 0x20002411180e21a8 0xd026cb3381e038c7 0x5d026cb3381e038c

def z530 : W := mkw 0x49e9964a00000000 0x049e9964a0000000 0x41f9f7cf00000003 0xb41f9f7cf0000000

def z531 : W := mkw 0x208b4000edbe000c 0x0208b4000edbe000 0xa1d90000ffff000d 0xba1d90000ffff000

def z532 : W := mkw 0x00c9144800000000 0x000c914480000000 0x51d934cc0038c0ff 0xb51d934cc0038c0f

def z533 : W := mkw 0x4fffffff86ef5fda 0x64fffffff86ef5fd 0xffffffff8fffffff 0xfffffffff8ffffff

def z534 : W := mkw 0x29a9c1054dcf134c 0x229a9c1054dcf134 0x21e1c70f0fc70700 0x821e1c70f0fc7070

def z535 : W := mkw 0x5ffdbfee5f4df753 0x45ffdbfee5f4df75 0xffffffffffffffff 0xffffffffffffffff

def z536 : W := mkw 0x0040144c02014552 0x40040144c0201455 0x501834cc0038c7ff 0x3501834cc0038c7f

def z537 : W := mkw 0x0000000000000000 0x0000000000000000 0x4007c03f00000001 0x04007c03f0000000

def z538 : W := mkw 0x0089004c040d0150 0x40089004c040d015 0x701904cc003f07f7 0x9701904cc003f07f

def z539 : W := mkw 0x0002000080200000 0x0000200008020000 0x8006000080200005 0x5800600008020000

def z540 : W := mkw 0x0040140002004402 0x0004014000200440 0x21c004000e000700 0x821c004000e00070

def z541 : W := mkw 0x04164115a0f31bc8 0x204164115a0f31bc 0xfe3fcf3ff1ff3fcf 0xffe3fcf3ff1ff3fc

def z542 : W := mkw 0x0000000400010140 0x0000000040001014 0x4001000c002700c1 0x04001000c002700c

def z543 : W := mkw 0x06dd3cec361de572 0xc06dd3cec361de57 0x7fd934cc7e3fc7ff 0xb7fd934cc7e3fc7f

def z544 : W := mkw 0x2416c000a0b2000c 0x02416c000a0b2000 0x0006c00000000000 0x00006c0000000000

def z545 : W := mkw 0x59e9974a4b405603 0x059e9974a4b40560 0x21e1c70f0fc00700 0x821e1c70f0fc0070

def z546 : W := mkw 0x1b603f155b41ffc3 0x21b603f155b41ffc 0xffe03f3fffc0ffce 0xfffe03f3fffc0ffc

def z547 : W := mkw 0x1920030049401201 0x0192003004940120 0x0020030001c00000 0x00020030001c0000

def z548 : W := mkw 0x04160000a0300000 0x004160000a030000 0x8e060000f0000000 0x48e060000f000000

def z549 : W := mkw 0x42c93eee060d4552 0x442c93eee060d455 0x71d93fff0e3fc7ff 0xb71d93fff0e3fc7f

def z550 : W := mkw 0x1040170002405603 0x0104017000240560 0x0000070000000700 0x0000007000000070

def z551 : W := mkw 0x0000000000000000 0x0000000000000000 0x0021c70f00000000 0x80021c70f0000000

def z552 : W := mkw 0x4ffdffef00c31348 0x24ffdffef00c3134 0x6fffffff01c70703 0xf6fffffff01c7070

def z553 : W := mkw 0x061628b080200880 0x0061628b08020088 0xde1e38f0802038c7 0x7de1e38f0802038c

def z554 : W := mkw 0x061628a0b030a020 0x8061628a0b030a02 0x8e1e30c0f038c03d 0x78e1e30c0f038c03

def z555 : W := mkw 0x1b202b005940b201 0x01b202b005940b20 0x9e203b00f1c0f80e 0x79e203b00f1c0f80

def z556 : W := mkw 0x12403fb01240fea3 0x812403fb01240fea 0x50003ff00000fff2 0x050003ff00000fff

def z557 : W := mkw 0x0000411500c31bc8 0x20000411500c31bc 0x7021cf3f01c73fc2 0x87021cf3f01c73fc

def z558 : W := mkw 0x0920000049000000 0x0092000004900000 0x0fc000007e000008 0x20fc000007e00000

def z559 : W := mkw 0x0040144800000000 0x0004014480000000 0x400034cc00000002 0x0400034cc0000000

def z560 : W := mkw 0x12403f001240f603 0x012403f001240f60 0x9e003f00f000ff0e 0x79e003f00f000ff0

def z561 : W := mkw 0x3ffffe00ffbee40f 0x03ffffe00ffbee40 0xaffff000ffffc00d 0xfaffff000ffffc00

def z562 : W := mkw 0x2d36c000e9b2000c 0x02d36c000e9b2000 0x8e3ec000f1f8000d 0x78e3ec000f1f8000

def z563 : W := mkw 0x2dfd94486f1c4416 0x42dfd94486f1c441 0x0fd830c07e18c038 0x20fd830c07e18c03

def z564 : W := mkw 0x4fbdaaa200000000 0x04fbdaaa20000000 0x0fffcb3300000001 0xf0fffcb330000000

def z565 : W := mkw 0x020028a000000000 0x0020028a00000000 0x400038f000000002 0x0400038f00000000

def z566 : W := mkw 0x041600b0a03008a0 0x8041600b0a03008a 0x0006003000000000 0x0000600300000000

def z567 : W := mkw 0x0089004c040d0150 0x40089004c040d015 0x0001000c00070000 0x00001000c0007000

def z568 : W := mkw 0x6ffffeeeefbf455e 0x46ffffeeeefbf455 0xffffffffffffc7ff 0xfffffffffffffc7f

def z569 : W := mkw 0x0002401580a309c8 0x20002401580a309c 0xd007c83f802738c7 0x5d007c83f802738c

def z570 : W := mkw 0x249fc000edbe000c 0x0249fc000edbe000 0xa01fc000ffff000d 0x0a01fc000ffff000

def z571 : W := mkw 0x4ffdbfea00401200 0x04ffdbfea0040120 0xffffffff81c03f07 0xfffffffff81c03f0

def z572 : W := mkw 0x249fc000a4be000c 0x0249fc000a4be000 0xa03fc00081ff0005 0xda03fc00081ff000

def z573 : W := mkw 0x249fc000a4be000c 0x0249fc000a4be000 0x8e1fc000f03f000d 0x78e1fc000f03f000

def z574 : W := mkw 0x2089c000048e000c 0x02089c000048e000 0x0001c00000070000 0x00001c0000007000

def z575 : W := mkw 0x5f34aba25940b201 0x05f34aba25940b20 0x8e26cb33f1c03800 0x48e26cb33f1c0380

def z576 : W := mkw 0x2dbfc111edfe1a8c 0x22dbfc111edfe1a8 0xafffcb33ffff380d 0xfafffcb33ffff380

def z577 : W := mkw 0x6dffd64aedbe000c 0x06dffd64aedbe000 0xafffc70fffff000d 0xfafffc70fffff000

def z578 : W := mkw 0x2dbd80006d1c0004 0x02dbd80006d1c000 0x0fffc0007e180009 0xf0fffc0007e18000

def z579 : W := mkw 0x0002400480a30148 0x00002400480a3014 0xf027c40c81e707c7 0xdf027c40c81e707c

def z580 : W := mkw 0x2dffd400efbe440e 0x02dffd400efbe440 0xbffff400ffffc70f 0xfbffff400ffffc70

def z581 : W := mkw 0x2f36e8b0f9b2a8ac 0x82f36e8b0f9b2a8a 0x8e26c830f1c03800 0x48e26c830f1c0380

def z582 : W := mkw 0x00000004060d4552 0x400000004060d455 0x701830c00e3fc7ff 0x3701830c00e3fc7f

def z583 : W := mkw 0x1fff3ffcff7dfff3 0xc1fff3ffcff7dfff 0xffff3ffcffffffff 0xfffff3ffcfffffff

def z584 : W := mkw 0x10c9154c5f4df753 0x410c9154c5f4df75 0xf1d934ccffffffff 0xbf1d934ccfffffff

def z585 : W := mkw 0x06df3cf8b63cecb2 0xc06df3cf8b63cecb 0xdfde38f0fe38f8ff 0x7dfde38f0fe38f8f

def z586 : W := mkw 0x0040144802004412 0x4004014480200441 0x000030c00000c030 0x0000030c00000c03

def z587 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0x2fe037007fc0c708 0xa2fe037007fc0c70

def z588 : W := mkw 0x1b627f11dbe2fe8b 0x21b627f11dbe2fe8 0xbfe6ff33ffc0ff0e 0xfbfe6ff33ffc0ff0

def z589 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4fd934cc00000003 0xb4fd934cc0000000

def z590 : W := mkw 0x2dbfc000e9b2000c 0x02dbfc000e9b2000 0x8fffc000f1c00001 0xf8fffc000f1c0000

def z591 : W := mkw 0x196017004b405603 0x0196017004b40560 0xafe00700ffc0070c 0xfafe00700ffc0070

def z592 : W := mkw 0x449f80faa03008a0 0x8449f80faa03008a 0x401fc0ff003800f1 0x0401fc0ff003800f

def z593 : W := mkw 0x0920000049000000 0x0092000004900000 0x8e200000f1c00000 0x48e200000f1c0000

def z594 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0x0fdfc0007e3f0009 0x20fdfc0007e3f000

def z595 : W := mkw 0x0040140000000000 0x0004014000000000 0x01c0340000000002 0xb01c034000000000

def z596 : W := mkw 0x3fbfeb00fdfeb20d 0x03fbfeb00fdfeb20 0xafffcb00ffff380d 0xfafffcb00ffff380

def z597 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0x21ffc0000fff0001 0x821ffc0000fff000

def z598 : W := mkw 0x49e9964e060d4552 0x449e9964e060d455 0x71f9f7cf0e3fc7ff 0xb71f9f7cf0e3fc7f

def z599 : W := mkw 0x4b603eea00000000 0x04b603eea0000000 0x4fe03fff00000002 0xf4fe03fff0000000

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000040000000706 0x9300004000000070

def z601 : W := mkw 0x00890000040c0000 0x000890000040c000 0x01d800000e180008 0x201d800000e18000

def z602 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4fdff0ff00000001 0x24fdff0ff0000000

def z603 : W := mkw 0x2dbfc000a4be000c 0x02dbfc000a4be000 0x0fffc000003f0001 0xf0fffc000003f000

def z604 : W := mkw 0x4dfd964a00000000 0x04dfd964a0000000 0x0fffc70f00000001 0xf0fffc70f0000000

def z605 : W := mkw 0x20024010fdbea8ac 0x820024010fdbea8a 0xb0000000fffff8fc 0x0b0000000fffff8f

def z606 : W := mkw 0x00000004060d4552 0x400000004060d455 0x7001040c0e3fc7ff 0x97001040c0e3fc7f

def z607 : W := mkw 0x4fffbefeb63dedf2 0xc4fffbefeb63dedf 0xfffffffffe3fffff 0xffffffffffe3ffff

def z608 : W := mkw 0x1b623f10db60fe83 0x01b623f10db60fe8 0xffe63f30ffe0ffcf 0xfffe63f30ffe0ffc

def z609 : W := mkw 0x061669b1b0f2baa8 0xa061669b1b0f2baa 0x8e26cb33f1c03800 0x48e26cb33f1c0380

def z610 : W := mkw 0x00cb555d80e31bc8 0x200cb555d80e31bc 0xf1ffffff81e73fc7 0xff1ffffff81e73fc

def z611 : W := mkw 0x1b202a005900a001 0x01b202a005900a00 0x0e00000070000000 0x00e0000007000000

def z612 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x21d934cc0e1fc738 0xa21d934cc0e1fc73

def z613 : W := mkw 0x20024000edbe000c 0x020024000edbe000 0xa027c000ffff000d 0xda027c000ffff000

def z614 : W := mkw 0x0002011080601a80 0x00002011080601a8 0xf0260f3081e03fc7 0xdf0260f3081e03fc

def z615 : W := mkw 0x0000010000401200 0x0000001000040120 0xf027cf3f81c03f07 0xdf027cf3f81c03f0

def z616 : W := mkw 0x3ffdbe007f1ce407 0x03ffdbe007f1ce40 0x0fd830007e18c008 0x20fd830007e18c00

def z617 : W := mkw 0x20024000a4be000c 0x020024000a4be000 0x00000000003f0000 0x000000000003f000

def z618 : W := mkw 0x00c9155d064d5fd2 0x600c9155d064d5fd 0x71d93fff0e3fffff 0xb71d93fff0e3ffff

def z619 : W := mkw 0x449fc0ff80a309c8 0x2449fc0ff80a309c 0x401fc0ff002700c1 0x0401fc0ff002700c

def z620 : W := mkw 0x0002401580a309c8 0x20002401580a309c 0x4027cf3f002700c3 0xd4027cf3f002700c

def z621 : W := mkw 0x0002001080200880 0x0000200108020088 0x90000000802038c4 0x090000000802038c

def z622 : W := mkw 0x0000010400411340 0x0000001040041134 0xf0210f0c81e73fc7 0xdf0210f0c81e73fc

def z623 : W := mkw 0x6f36eaa2e9b2000c 0x06f36eaa2e9b2000 0x8e26cb33f1c00000 0x48e26cb33f1c0000

def z624 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0x8ffec000ffd80008 0x68ffec000ffd8000

def z625 : W := mkw 0x020228b0b030a8a0 0x8020228b0b030a8a 0xd00038f0f038f8fe 0x0d00038f0f038f8f

def z626 : W := mkw 0x041600b0b030a8a0 0x8041600b0b030a8a 0xd01e00f0f038f8fd 0x0d01e00f0f038f8f

def z627 : W := mkw 0x29abc000cdae000c 0x029abc000cdae000 0xa1e7c0008fe70005 0xda1e7c0008fe7000

def z628 : W := mkw 0x4ffdbeee060d4552 0x44ffdbeee060d455 0x6fffffff0e070703 0xf6fffffff0e07070

def z629 : W := mkw 0x3fffffb0fffefeaf 0x83fffffb0fffefea 0xfffffff0ffffffff 0xffffffff0fffffff

def z630 : W := mkw 0x49e9964a00000000 0x049e9964a0000000 0x01c0000000000000 0x001c000000000000

def z631 : W := mkw 0x0000000400010140 0x0000000040001014 0x30000000002707c4 0x030000000002707c

def z632 : W := mkw 0x6ffffefafdbea8ac 0x86ffffefafdbea8a 0xfffffffffffff8ff 0xffffffffffffff8f

def z633 : W := mkw 0x00cb145cb63dedf2 0xc00cb145cb63dedf 0xf1d934ccfe3fffff 0xbf1d934ccfe3ffff

def z634 : W := mkw 0x020028a01000a020 0x8020028a01000a02 0x000030c00000c030 0x0000030c00000c03

def z635 : W := mkw 0x42403eee02014552 0x442403eee0201455 0x50003fff0000c7f2 0x050003fff0000c7f

def z636 : W := mkw 0x0002400080a20008 0x00002400080a2000 0x8026c00081c00000 0x48026c00081c0000

def z637 : W := mkw 0x04160000a0300000 0x004160000a030000 0x001e000000380001 0x0001e00000038000

def z638 : W := mkw 0x3be9ff005fcef60f 0x03be9ff005fcef60 0xbfe1ff00ffc7ff0e 0xfbfe1ff00ffc7ff0

def z639 : W := mkw 0x020028b01000a8a0 0x8020028b01000a8a 0xde0038f0f000f8fe 0x7de0038f0f000f8f

def z640 : W := mkw 0x04160010a0300880 0x004160010a030088 0xde1e0830f03838cf 0x7de1e0830f03838c

def z641 : W := mkw 0x19e9174c4f4d5753 0x419e9174c4f4d575 0x71f937cc0fffc7ff 0xb71f937cc0fffc7f

def z642 : W := mkw 0x0000011500411bc0 0x20000011500411bc 0x5027cf3f00003fc3 0xd5027cf3f00003fc

def z643 : W := mkw 0x1b603f4c5b41f753 0x41b603f4c5b41f75 0xffe03fccffc0fffe 0xfffe03fccffc0fff

def z644 : W := mkw 0x2dbfc004efbf455e 0x42dbfc004efbf455 0xbfffc000ffffc7fd 0xfbfffc000ffffc7f

def z645 : W := mkw 0x4fffbefa80200880 0x04fffbefa8020088 0xdfffffff802038c7 0xfdfffffff802038c

def z646 : W := mkw 0x049f0000a43c0000 0x0049f0000a43c000 0xafdf0000fe3f000d 0xfafdf0000fe3f000

def z647 : W := mkw 0x0200280000000000 0x0020028000000000 0x0e00380000000002 0x70e0038000000000

def z648 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf001040c81e73fc7 0x9f001040c81e73fc

def z649 : W := mkw 0x00020014b63dedf2 0xc00020014b63dedf 0xb0000000fe3ffffc 0x0b0000000fe3ffff

def z650 : W := mkw 0x0002411586ef5fda 0x60002411586ef5fd 0xf027cf3f8fffffff 0xdf027cf3f8ffffff

def z651 : W := mkw 0x0414000000000000 0x0041400000000000 0x0e1e000000000001 0x70e1e00000000000

def z652 : W := mkw 0x4be9beea00000000 0x04be9beea0000000 0x41e1ffff00000002 0x841e1ffff0000000

def z653 : W := mkw 0x061669b580e31bc8 0x2061669b580e31bc 0xfe3fffff81e73fc7 0xffe3fffff81e73fc

def z654 : W := mkw 0x00020010b030a8a0 0x800020010b030a8a 0x80000000f0003800 0x080000000f000380

def z655 : W := mkw 0x6ffdfeea4d8e000c 0x06ffdfeea4d8e000 0x6fffffff0fc70003 0xf6fffffff0fc7000

def z656 : W := mkw 0x0b627f1580e31bc8 0x20b627f1580e31bc 0xffe7ff3f81e73fc7 0xfffe7ff3f81e73fc

def z657 : W := mkw 0x00000000060c4412 0x400000000060c441 0x000000000e18c038 0x0000000000e18c03

def z658 : W := mkw 0x4ffdbeee02014552 0x44ffdbeee0201455 0x5fffffff0000c7f3 0xf5fffffff0000c7f

def z659 : W := mkw 0x00020014802109c0 0x000020014802109c 0xf0070c3c80273fc7 0xdf0070c3c80273fc

def z660 : W := mkw 0x0000000049000000 0x0000000004900000 0xa0000000ffc0000c 0x0a0000000ffc0000

def z661 : W := mkw 0x00000004060d4552 0x400000004060d455 0x200000000e070700 0x0200000000e07070

def z662 : W := mkw 0x5be9bf4a5b40f603 0x05be9bf4a5b40f60 0xbfe1ff0fffc0ff0e 0xfbfe1ff0fffc0ff0

def z663 : W := mkw 0x0f763eb0b030a8a0 0x80f763eb0b030a8a 0xdffe3ff0f038f8ff 0xfdffe3ff0f038f8f

def z664 : W := mkw 0x3dbfc100fffef60f 0x03dbfc100fffef60 0xbfffc000ffffff0d 0xfbfffc000ffffff0

def z665 : W := mkw 0x000000003010a020 0x8000000003010a02 0x000000007018c038 0x0000000007018c03

def z666 : W := mkw 0x0b603f0000401200 0x00b603f000040120 0xbfe03f0081c03f06 0xfbfe03f0081c03f0

def z667 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xb027c00081e73fc5 0xdb027c00081e73fc

def z668 : W := mkw 0x061628b4b031a9e0 0x8061628b4b031a9e 0xfe1f3cfcf03fffff 0xffe1f3cfcf03ffff

def z669 : W := mkw 0x0002411180e21a88 0x20002411180e21a8 0xa027cb3381e73805 0xda027cb3381e7380

def z670 : W := mkw 0x0b603e0049000000 0x00b603e004900000 0xafe03f00ffc0000e 0xfafe03f00ffc0000

def z671 : W := mkw 0x0000010000401200 0x0000001000040120 0x80200b0081c03800 0x480200b0081c0380

def z672 : W := mkw 0x020029001040b200 0x0020029001040b20 0xbe203f00f1c0ff0e 0xfbe203f00f1c0ff0

def z673 : W := mkw 0x5ffdbeea5b00e403 0x05ffdbeea5b00e40 0x0fd830c07e00c008 0x20fd830c07e00c00

def z674 : W := mkw 0x1b603f001240f603 0x01b603f001240f60 0x1fe03f000000ff02 0xf1fe03f000000ff0

def z675 : W := mkw 0x0002001080200880 0x0000200108020088 0x40060030002000c1 0x040060030002000c

def z676 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4fd83fff00000002 0x24fd83fff0000000

def z677 : W := mkw 0x1b603fb05b40fea3 0x81b603fb05b40fea 0xffe03ff0ffc0fffe 0xfffe03ff0ffc0fff

def z678 : W := mkw 0x3f36eb00f9f2b20d 0x03f36eb00f9f2b20 0x8e26cb00f1c03800 0x48e26cb00f1c0380

def z679 : W := mkw 0x2dbd80006d1c0004 0x02dbd80006d1c000 0x2fd900007e3f000d 0xb2fd900007e3f000

def z680 : W := mkw 0x0000000000000000 0x0000000000000000 0x001800000038000d 0x3001800000038000

def z681 : W := mkw 0x1f743fa05b40f603 0x01f743fa05b40f60 0xfffe3ff0ffc0ff0f 0xffffe3ff0ffc0ff0

def z682 : W := mkw 0x6ffdbeea6d1c0004 0x06ffdbeea6d1c000 0x0fd830c07e180008 0x20fd830c07e18000

def z683 : W := mkw 0x3b627f00fffef60f 0x03b627f00fffef60 0xbfe03f00ffffff0e 0xfbfe03f00ffffff0

def z684 : W := mkw 0x09e9144c4f0d4552 0x409e9144c4f0d455 0xfff934ccffffc7ff 0xffff934ccffffc7f

def z685 : W := mkw 0x00c9144c00010140 0x000c9144c0001014 0x71d934cc002707c7 0xb71d934cc002707c

def z686 : W := mkw 0x00890000040c0000 0x000890000040c000 0x71d930c00e3fc0ff 0xb71d930c00e3fc0f

def z687 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xce1e08f0f03838f1 0x4ce1e08f0f03838f

def z688 : W := mkw 0x2d36c000e9b2000c 0x02d36c000e9b2000 0xafe6c000ffc0000c 0xfafe6c000ffc0000

def z689 : W := mkw 0x5ffdbfea1240f603 0x05ffdbfea1240f60 0x5fffffff0000ff03 0xf5fffffff0000ff0

def z690 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x51d834cc0e18c7fa 0x251d834cc0e18c7f

def z691 : W := mkw 0x02403cfc1201edf2 0xc02403cfc1201edf 0x50003cfc0000fff2 0x050003cfc0000fff

def z692 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x31c1040c0e3fc7fc 0x831c1040c0e3fc7f

def z693 : W := mkw 0x0dbfc11580e31bc8 0x20dbfc11580e31bc 0xffffcf3f81e73fc7 0xfffffcf3f81e73fc

def z694 : W := mkw 0x0202691590e3bbc8 0x20202691590e3bbc 0xfe27ff3ff1e7ffcf 0xffe27ff3ff1e7ffc

def z695 : W := mkw 0x0002011580611bc0 0x20002011580611bc 0xd0060f3f80203fc7 0x5d0060f3f80203fc

def z696 : W := mkw 0x06df7dfdb6fffffa 0xe06df7dfdb6fffff 0xffffffffffffffff 0xffffffffffffffff

def z697 : W := mkw 0x6ffffeeaa4be000c 0x06ffffeeaa4be000 0x4fffffff003f0003 0xf4fffffff003f000

def z698 : W := mkw 0x42427fff80e31bc8 0x242427fff80e31bc 0xf027ffff81e73fc7 0xdf027ffff81e73fc

def z699 : W := mkw 0x1be93f485f4cf613 0x41be93f485f4cf61 0xbff83fc0ffd8ff3e 0xfbff83fc0ffd8ff3

def z700 : W := mkw 0x00890004040d0140 0x000890004040d014 0x71d9040c0e3f07cf 0xb71d9040c0e3f07c

def z701 : W := mkw 0x249d8000241c0004 0x0249d8000241c000 0x0018000000180000 0x0001800000018000

def z702 : W := mkw 0x061428a000000000 0x0061428a00000000 0x0e06083000000000 0x40e0608300000000

def z703 : W := mkw 0x42403efa1000a8a0 0x842403efa1000a8a 0x50003fff0000f8f2 0x050003fff0000f8f

def z704 : W := mkw 0x0ffdbe0000000000 0x00ffdbe000000000 0x0fffff0000000003 0xf0fffff000000000

def z705 : W := mkw 0x04160010b030a8a0 0x804160010b030a8a 0x9e1e0000f038f8fd 0x79e1e0000f038f8f

def z706 : W := mkw 0x04164000a0b20008 0x004164000a0b2000 0xae3fc000f1ff000d 0xfae3fc000f1ff000

def z707 : W := mkw 0x00cb555986ee5e9a 0x600cb555986ee5e9 0x81fefbf38fd8f838 0x681fefbf38fd8f83

def z708 : W := mkw 0x0dfd944800000000 0x00dfd94480000000 0x4fffffff00000003 0xf4fffffff0000000

def z709 : W := mkw 0x4dbd80ea00000000 0x04dbd80ea0000000 0x4fffcfff00000003 0xf4fffcfff0000000

def z710 : W := mkw 0x249fc0b5a4bf09ec 0xa249fc0b5a4bf09e 0x401fc0ff003f00f1 0x0401fc0ff003f00f

def z711 : W := mkw 0x2ba9e8b05d8ea8ac 0x82ba9e8b05d8ea8a 0x71e1f8f00fc7f8f2 0x871e1f8f00fc7f8f

def z712 : W := mkw 0x061428b03010a8a0 0x8061428b03010a8a 0x5e1e38f07018f8fb 0x75e1e38f07018f8f

def z713 : W := mkw 0x549d81ea5b40f603 0x0549d81ea5b40f60 0xf01fc0ffffc0ff0d 0x0f01fc0ffffc0ff0

def z714 : W := mkw 0x0b603c005b00e402 0x00b603c005b00e40 0xbfe03c00ffc0ff0e 0xfbfe03c00ffc0ff0

def z715 : W := mkw 0x6ffdbeea6f1c4416 0x46ffdbeea6f1c441 0x4fffffff7e18c03b 0xf4fffffff7e18c03

def z716 : W := mkw 0x2d76d44cebb3455e 0x42d76d44cebb3455 0xde26f4ccf1c0c7f2 0x4de26f4ccf1c0c7f

def z717 : W := mkw 0x4f34aaa6060d4552 0x44f34aaa6060d455 0x3e26cb330e3fc7fc 0x43e26cb330e3fc7f

def z718 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xafe03f00ffc0ff08 0xeafe03f00ffc0ff0

def z719 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde1e38f0f018f8fa 0x6de1e38f0f018f8f

def z720 : W := mkw 0x06df3cfcb63dedf2 0xc06df3cfcb63dedf 0xafc70c3cfe073f00 0xcafc70c3cfe073f0

def z721 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x71d834cc0e3fc7fe 0x271d834cc0e3fc7f

def z722 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xb000000081fffffc 0x0b000000081fffff

def z723 : W := mkw 0x10024115cbe35fcb 0x210024115cbe35fc 0xb00000008fe73fc4 0x0b00000008fe73fc

def z724 : W := mkw 0x6ffdbeea7d1ca024 0x86ffdbeea7d1ca02 0x4fffffff7e18c03b 0xf4fffffff7e18c03

def z725 : W := mkw 0x061469a530d3b368 0xa061469a530d3b36 0x2e39f7cf71dfc738 0xa2e39f7cf71dfc73

def z726 : W := mkw 0x44dd96ea00000000 0x044dd96ea0000000 0x401fc7ff00000001 0x0401fc7ff0000000

def z727 : W := mkw 0x2dbfc0b0edbe08ac 0x82dbfc0b0edbe08a 0xffffc8f0ffff38ff 0xfffffc8f0ffff38f

def z728 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xa000000081c73f00 0x0a000000081c73f0

def z729 : W := mkw 0x4616a8b2b030a8a0 0x84616a8b2b030a8a 0xde1ef8f3f038f8ff 0x7de1ef8f3f038f8f

def z730 : W := mkw 0x42403eea00000000 0x042403eea0000000 0x4007ffff00000003 0x04007ffff0000000

def z731 : W := mkw 0x4ffdbeea1000a000 0x04ffdbeea1000a00 0xcffffffff0003803 0xfcffffffff000380

def z732 : W := mkw 0x42403eea00000000 0x042403eea0000000 0x4026ffff00000002 0x44026ffff0000000

def z733 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfe6ff33ffc0ff0e 0xfbfe6ff33ffc0ff0

def z734 : W := mkw 0x020228109020a880 0x0020228109020a88 0xde1e38f0f038f8ff 0x7de1e38f0f038f8f

def z735 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xefffc830ffff000f 0xfefffc830ffff000

def z736 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xaff9c000ffff000c 0xaaff9c000ffff000

def z737 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xafe00f00ffc03f0c 0xfafe00f00ffc03f0

def z738 : W := mkw 0x4f74beea00000000 0x04f74beea0000000 0x4e3effff00000003 0x74e3effff0000000

def z739 : W := mkw 0x4f74beea00000000 0x04f74beea0000000 0x0e26cf3f00000000 0x40e26cf3f0000000

def z740 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfc03f00ffc0ff0e 0x2bfc03f00ffc0ff0

def z741 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xbfffc000ffffc0fd 0xfbfffc000ffffc0f

def z742 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0xf1d93ccc8e3fffff 0xff1d93ccc8e3ffff

def z743 : W := mkw 0x4ffdbeea02004402 0x04ffdbeea0200440 0x5fffffff0000c703 0xf5fffffff0000c70

def z744 : W := mkw 0x4ffdbeea02004412 0x44ffdbeea0200441 0x4fffffff0000c033 0xf4fffffff0000c03

def z745 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfe1ff0fffc0ff0e 0xfbfe1ff0fffc0ff0

def z746 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfe03000ffc0ff0c 0xfbfe03000ffc0ff0

def z747 : W := mkw 0x3f36ebb0f9f2baad 0x83f36ebb0f9f2baa 0x8e26cb30f1c03800 0x48e26cb30f1c0380

def z748 : W := mkw 0x49eb965ab030a8a0 0x849eb965ab030a8a 0x91e1c70ff038f8fc 0x891e1c70ff038f8f

def z749 : W := mkw 0x36dfff00b6fef60f 0x036dfff00b6fef60 0x101fff00003fff03 0x0101fff00003fff0

def z750 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x6fffffff00270007 0xf6fffffff0027000

def z751 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafffc70fffff000d 0xfafffc70fffff000

def z752 : W := mkw 0x249fc0fca4bf09fc 0xc249fc0fca4bf09f 0x401fc0fc003f00f1 0x0401fc0fc003f00f

def z753 : W := mkw 0x196015005b40f603 0x0196015005b40f60 0xbfe03400ffc0ff0e 0xfbfe03400ffc0ff0

def z754 : W := mkw 0x061668b1b0b2a8a8 0xa061668b1b0b2a8a 0xde1ef8f3f038f8ff 0x7de1ef8f3f038f8f

def z755 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafd90000ffff000d 0xbafd90000ffff000

def z756 : W := mkw 0x4ffdbeea1000a020 0x84ffdbeea1000a02 0x4fffffff0000c033 0xf4fffffff0000c03

def z757 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0xf1f934cc8fffc7ff 0xff1f934cc8fffc7f

def z758 : W := mkw 0x1b627e15dba3edcb 0x21b627e15dba3edc 0x4fc7f03f7e27c0c9 0x24fc7f03f7e27c0c

def z759 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x71d830c00e3fc7ff 0x371d830c00e3fc7f

def z760 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xaffec000ffff000c 0x6affec000ffff000

def z761 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde1830c0f038f8ff 0x3de1830c0f038f8f

def z762 : W := mkw 0x2dbd81156d5d1bc4 0x22dbd81156d5d1bc 0x5fd80f3f7e183fca 0x25fd80f3f7e183fc

def z763 : W := mkw 0x0000000000000000 0x0000000000000000 0x4027cb3f00000001 0x44027cb3f0000000

def z764 : W := mkw 0x0920010049401200 0x0092001004940120 0xbfe00000ffc03f0c 0xfbfe00000ffc03f0

def z765 : W := mkw 0x1d7617b0eb705ea3 0x81d7617b0eb705ea 0x61fe07f00ff807f1 0x861fe07f00ff807f

def z766 : W := mkw 0x2dbdc0006d9e000c 0x02dbdc0006d9e000 0x2fe1c0007fc70000 0x82fe1c0007fc7000

def z767 : W := mkw 0x6dbfc0eaedbe000c 0x06dbfc0eaedbe000 0xefffcfffffff000f 0xfefffcfffffff000

def z768 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xe027cf3f81c73f03 0xde027cf3f81c73f0

def z769 : W := mkw 0x00890004060d4552 0x400890004060d455 0x71d930c00e3fc7ff 0xb71d930c00e3fc7f

def z770 : W := mkw 0x4ffdbeea49000000 0x04ffdbeea4900000 0x4fffffff7e00000b 0xf4fffffff7e00000

def z771 : W := mkw 0x29abc000edbe000c 0x029abc000edbe000 0xafe1c000ffff000c 0xfafe1c000ffff000

def z772 : W := mkw 0x29abc000cdae000c 0x029abc000cdae000 0xafe7c000ffe7000d 0xfafe7c000ffe7000

def z773 : W := mkw 0x0b603f0049401200 0x00b603f004940120 0xbfe03f00ffc03f0e 0xfbfe03f00ffc03f0

def z774 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfe03b00ffc0ff0c 0x6bfe03b00ffc0ff0

def z775 : W := mkw 0x4ffdbeea5900a000 0x04ffdbeea5900a00 0xffffffffffc0f80f 0xfffffffffffc0f80

def z776 : W := mkw 0x4ffdbeea02004402 0x04ffdbeea0200440 0x6fffffff0e000703 0xf6fffffff0e00070

def z777 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xd027cf3f81e73fc3 0x4d027cf3f81e73fc

def z778 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafe7c000ffff000c 0xcafe7c000ffff000

def z779 : W := mkw 0x008b411584ef1bc8 0x2008b411584ef1bc 0xb1d900008fff3fcd 0xbb1d900008fff3fc

def z780 : W := mkw 0x02403d001240f602 0x002403d001240f60 0xbfe03f00ffc0ff0e 0xfbfe03f00ffc0ff0

def z781 : W := mkw 0x59e9974e4f4d5753 0x459e9974e4f4d575 0x21e1c70f0fc70700 0x821e1c70f0fc7070

def z782 : W := mkw 0x400000ea00000000 0x0400000ea0000000 0x4027cfff00000003 0xd4027cfff0000000

def z783 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0x5e1e38f07038f8fb 0x25e1e38f07038f8f

def z784 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xefffc40cffff000f 0xfefffc40cffff000

def z785 : W := mkw 0x29a9c0004d8e000c 0x029a9c0004d8e000 0xaff9c000ffff000d 0xfaff9c000ffff000

def z786 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0x2fffc0007fff0009 0xa2fffc0007fff000

def z787 : W := mkw 0x12403f151241ffc3 0x212403f151241ffc 0x10003f000000ffc2 0x010003f000000ffc

def z788 : W := mkw 0x04160010b030a8a0 0x804160010b030a8a 0xde1e30c0f038f8ff 0x7de1e30c0f038f8f

def z789 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x0fffffff00000000 0xe0fffffff0000000

def z790 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x0fe7ff3f00000002 0xf0fe7ff3f0000000

def z791 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfc03400ffc0ff0e 0xbbfc03400ffc0ff0

def z792 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xfe3e38f0f1f8f8ff 0xffe3e38f0f1f8f8f

def z793 : W := mkw 0x09224115c9e31bc8 0x209224115c9e31bc 0xbfe00000ffe73fcc 0xfbfe00000ffe73fc

def z794 : W := mkw 0x5ffdbeea5f0ce413 0x45ffdbeea5f0ce41 0x0fd830c07e18c038 0x20fd830c07e18c03

def z795 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4fdfffff00000003 0x24fdfffff0000000

def z796 : W := mkw 0x0089004800000000 0x0008900480000000 0x403fcfff00000003 0xd403fcfff0000000

def z797 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4ffeffff00000002 0x64ffeffff0000000

def z798 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xffe03f3fffc0ff0e 0xfffe03f3fffc0ff0

def z799 : W := mkw 0x12403f041241f753 0x412403f041241f75 0x10003f000000fff2 0x010003f000000fff

def z800 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4fe7cf3f00000003 0xd4fe7cf3f0000000

def z801 : W := mkw 0x0040140002004402 0x0004014000200440 0x71e7ff3f0e00c70f 0xf71e7ff3f0e00c70

def z802 : W := mkw 0x02403e0000000000 0x002403e000000000 0x4027ff3f00000003 0xd4027ff3f0000000

def z803 : W := mkw 0x20024115efff5fde 0x620024115efff5fd 0xb0000000fffffffc 0x0b0000000fffffff

def z804 : W := mkw 0x00024115a0f31be8 0xa00024115a0f31be 0xf027cf3f81ff3ff7 0xdf027cf3f81ff3ff

def z805 : W := mkw 0x1ba92b4c5d4db351 0x41ba92b4c5d4db35 0xce390bccf1ff38f1 0x4ce390bccf1ff38f

def z806 : W := mkw 0x00024115a0f31bc8 0x200024115a0f31bc 0xf027cf3ff1ff3fcf 0xdf027cf3ff1ff3fc

def z807 : W := mkw 0x4f34aaea00000000 0x04f34aaea0000000 0x4e26cbff00000000 0x44e26cbff0000000

def z808 : W := mkw 0x12403ffc1241fff3 0xc12403ffc1241fff 0x50003ffc0000fff2 0x050003ffc0000fff

def z809 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafffc000ffc70001 0xfafffc000ffc7000

def z810 : W := mkw 0x1b603e005b00e403 0x01b603e005b00e40 0x4fe7ff3f7e00c00b 0xf4fe7ff3f7e00c00

def z811 : W := mkw 0x4dfd96ea00000000 0x04dfd96ea0000000 0x4fffc7ff00000001 0xf4fffc7ff0000000

def z812 : W := mkw 0x62427eeaedbe000c 0x062427eeaedbe000 0xe0003fffffff000e 0x0e0003fffffff000

def z813 : W := mkw 0x00c91448060c4412 0x400c91448060c441 0x41ffffff0e18c03b 0xf41ffffff0e18c03

def z814 : W := mkw 0x00024115b6fffffa 0xe00024115b6fffff 0xb0000000fffffffc 0x0b0000000fffffff

def z815 : W := mkw 0x5ffdbeea4b004403 0x05ffdbeea4b00440 0x4fffffff0e000003 0xf4fffffff0e00000

def z816 : W := mkw 0x42002aa200000000 0x042002aa20000000 0x4027cf3f00000003 0xd4027cf3f0000000

def z817 : W := mkw 0x1002411592e3ffcb 0x21002411592e3ffc 0xb000000081e7ffc4 0x0b000000081e7ffc

def z818 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xfe1e3cf0f038ffff 0xffe1e3cf0f038fff

def z819 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xffe13f0cffc0ff0f 0xfffe13f0cffc0ff0

def z820 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0x1000000000273fc0 0x01000000000273fc

def z821 : W := mkw 0x061428b03010a8a0 0x8061428b03010a8a 0x1e1830c07018f8f8 0x21e1830c07018f8f

def z822 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfe00f00ffc03f06 0xdbfe00f00ffc03f0

def z823 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xffffc000ffff00cf 0xfffffc000ffff00c

def z824 : W := mkw 0x6dbfc0a2edbe000c 0x06dbfc0a2edbe000 0xafffc033ffff000d 0xfafffc033ffff000

def z825 : W := mkw 0x12403f5d1241ffd3 0x612403f5d1241ffd 0x50003fff0000fff2 0x050003fff0000fff

def z826 : W := mkw 0x4ffdbeea040c0000 0x04ffdbeea040c000 0x4fffffff0e18000b 0xf4fffffff0e18000

def z827 : W := mkw 0x2dbfc010edbe088c 0x02dbfc010edbe088 0xefffc030ffff00cd 0xfefffc030ffff00c

def z828 : W := mkw 0x4f74bea200000000 0x04f74bea20000000 0x4fe7ff3f00000003 0xf4fe7ff3f0000000

def z829 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfe7ff00ffc0ff0f 0xfbfe7ff00ffc0ff0

def z830 : W := mkw 0x4fffffff80e31bc8 0x24fffffff80e31bc 0xbfd830c081e73fc4 0x2bfd830c081e73fc

def z831 : W := mkw 0x4fbdaaea00000000 0x04fbdaaea0000000 0x4fffcbff00000001 0xf4fffcbff0000000

def z832 : W := mkw 0x049d800000000000 0x0049d80000000000 0x403fcf3f00000003 0xd403fcf3f0000000

def z833 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4ffffbff00000001 0x64ffffbff0000000

def z834 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x5fffffff0000c00f 0xf5fffffff0000c00

def z835 : W := mkw 0x4ffdbeea1000a000 0x04ffdbeea1000a00 0xdffffffff038f8ff 0xfdffffffff038f8f

def z836 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde1e3ffff038f8ff 0x7de1e3ffff038f8f

def z837 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xafe03f00ffc03f02 0xfafe03f00ffc03f0

def z838 : W := mkw 0x4ffdbeea4d0c0000 0x04ffdbeea4d0c000 0xefffffffffff000f 0xfefffffffffff000

def z839 : W := mkw 0x46ddbeea00000000 0x046ddbeea0000000 0x403fffff00000003 0xd403fffff0000000

def z840 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xb001000081e73fc5 0x9b001000081e73fc

def z841 : W := mkw 0x2dbd80006d1c0004 0x02dbd80006d1c000 0xaff90000ffff000d 0xfaff90000ffff000

def z842 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xe027cf3f81e73fc1 0xce027cf3f81e73fc

def z843 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x71d934cc0e3fc7f3 0x871d934cc0e3fc7f

def z844 : W := mkw 0x4089804a00000000 0x04089804a0000000 0x4027cf3f00000003 0xd4027cf3f0000000

def z845 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xb020000081e73fc4 0xdb020000081e73fc

def z846 : W := mkw 0x4dfd96ea00000000 0x04dfd96ea0000000 0x41ffcfff00000003 0xd41ffcfff0000000

def z847 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xfff83fc0ffc0ff0f 0xffff83fc0ffc0ff0

def z848 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xaff80000ffff000c 0xfaff80000ffff000

def z849 : W := mkw 0x061668b0b0b2a8a8 0x8061668b0b0b2a8a 0xfe1e38f0f1fff8ff 0x7fe1e38f0f1fff8f

def z850 : W := mkw 0x29224000edbe000c 0x029224000edbe000 0xafc00000ffff000c 0x2afc00000ffff000

def z851 : W := mkw 0x0002411582e35fca 0x20002411582e35fc 0xb00000008fe7ffcc 0x0b00000008fe7ffc

def z852 : W := mkw 0x6ffdbeea6d1c0004 0x06ffdbeea6d1c000 0x6fffffff7e3f000f 0xf6fffffff7e3f000

def z853 : W := mkw 0x4ffdbeea060c4412 0x44ffdbeea060c441 0x5fffffff0e38c0ff 0xf5fffffff0e38c0f

def z854 : W := mkw 0x4ffdbeea3010a020 0x84ffdbeea3010a02 0x5fffffff7038c0ff 0xf5fffffff7038c0f

def z855 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x31d834c00e3fc7fe 0xb31d834c00e3fc7f

def z856 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde1ff8fff038f8ff 0x7de1ff8fff038f8f

def z857 : W := mkw 0x52403fff1241ffc3 0x252403fff1241ffc 0x50003fff0000ffc2 0x050003fff0000ffc

def z858 : W := mkw 0x2dbfc0a0edbe000c 0x02dbfc0a0edbe000 0xefffc0f0ffff000d 0xfefffc0f0ffff000

def z859 : W := mkw 0x0920000049000000 0x0092000004900000 0xafe10000ffe7000d 0xfafe10000ffe7000

def z860 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x6fffffff0e00000f 0xf6fffffff0e00000

def z861 : W := mkw 0x4ffdbeea4b004402 0x04ffdbeea4b00440 0xffffffffffc0c70f 0xfffffffffffc0c70

def z862 : W := mkw 0x1b603f485b40f603 0x01b603f485b40f60 0xffe03fccffc0ff0e 0xfffe03fccffc0ff0

def z863 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xb000080081e73fc6 0x5b000080081e73fc

def z864 : W := mkw 0x192001005b40f603 0x0192001005b40f60 0xbfc00000ffc0ff0c 0x2bfc00000ffc0ff0

def z865 : W := mkw 0x52403fee1241f753 0x452403fee1241f75 0x50003fff0000fff2 0x050003fff0000fff

def z866 : W := mkw 0x2dbfc010edbe088c 0x02dbfc010edbe088 0xbfffc000ffff38cd 0xfbfffc000ffff38c

def z867 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xefffc0c0ffff00fd 0xfefffc0c0ffff00f

def z868 : W := mkw 0x061668b0b0b2a8a8 0x8061668b0b0b2a8a 0xfe3ffffff1fff8ff 0xffe3ffffff1fff8f

def z869 : W := mkw 0x4fbdaaa200000000 0x04fbdaaa20000000 0x4fffcf3f00000003 0xf4fffcf3f0000000

def z870 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x31d934cc0e3fc7fc 0xa31d934cc0e3fc7f

def z871 : W := mkw 0x12403d005b40f603 0x012403d005b40f60 0xbfc03c00ffc0ff0e 0xfbfc03c00ffc0ff0

def z872 : W := mkw 0x1b627f15dbe3ffcb 0x21b627f15dbe3ffc 0xbfc03000ffe7ffcc 0x2bfc03000ffe7ffc

def z873 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0x8000000081e738c0 0x08000000081e738c

def z874 : W := mkw 0x06162800b030a000 0x006162800b030a00 0xde1e38c0f038f8ff 0x7de1e38c0f038f8f

def z875 : W := mkw 0x0002410080e21208 0x00002410080e2120 0xf027cf3f81e73f07 0xdf027cf3f81e73f0

def z876 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfc03800ffc0ff0e 0x7bfc03800ffc0ff0

def z877 : W := mkw 0x09224000c9a20008 0x009224000c9a2000 0xafe00000ffe7000c 0xfafe00000ffe7000

def z878 : W := mkw 0x4ffdbeea040c0010 0x44ffdbeea040c001 0x4fffffff00180033 0xf4fffffff0018003

def z879 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafdfc000ffff000d 0x2afdfc000ffff000

def z880 : W := mkw 0x196017005b40f603 0x0196017005b40f60 0xbfe00700ffc0ff0c 0xfbfe00700ffc0ff0

def z881 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafde0000ffff000d 0x7afde0000ffff000

def z882 : W := mkw 0x0000000000000000 0x0000000000000000 0x503fffff0038c0ff 0xf503fffff0038c0f

def z883 : W := mkw 0x00cb555d86ef5fda 0x600cb555d86ef5fd 0xb1d830c08ffffffc 0x2b1d830c08ffffff

def z884 : W := mkw 0x2dbdc0006d9e000c 0x02dbdc0006d9e000 0x2ff9c0007fff000d 0xb2ff9c0007fff000

def z885 : W := mkw 0x1b202b005940b201 0x01b202b005940b20 0xbfe00f00ffc03f0e 0xfbfe00f00ffc03f0

def z886 : W := mkw 0x10024115d9e3bbc9 0x210024115d9e3bbc 0xb0000000f1e73fc4 0x0b0000000f1e73fc

def z887 : W := mkw 0x2d36c000e9b2000c 0x02d36c000e9b2000 0xafe7c000ffe7000d 0xfafe7c000ffe7000

def z888 : W := mkw 0x0920400049820008 0x0092040004982000 0xafe1c000ffc7000c 0xfafe1c000ffc7000

def z889 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde3ff8f0f038f8ff 0xfde3ff8f0f038f8f

def z890 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x71d93fff0e3fc7ff 0xb71d93fff0e3fc7f

def z891 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4fffffff003800f3 0xf4fffffff003800f

def z892 : W := mkw 0x0920000000000000 0x0092000000000000 0x4fe7cf3f00000003 0xf4fe7cf3f0000000

def z893 : W := mkw 0x4dfd96ea00000000 0x04dfd96ea0000000 0x41fff7ff00000003 0xb41fff7ff0000000

def z894 : W := mkw 0x4dfd96ea00000000 0x04dfd96ea0000000 0x01e7c73f00000000 0x801e7c73f0000000

def z895 : W := mkw 0x12403fb51241ffe3 0xa12403fb51241ffe 0x50003fff0000fff2 0x050003fff0000fff

def z896 : W := mkw 0x0dbfc000c9a20008 0x00dbfc000c9a2000 0xafffc000ffe7000d 0xfafffc000ffe7000

def z897 : W := mkw 0x0000000000000000 0x0000000000000000 0x4027c73f00000001 0x84027c73f0000000

def z898 : W := mkw 0x40c9944e060d4552 0x440c9944e060d455 0x71d9f4cf0e3fc7ff 0xb71d9f4cf0e3fc7f

def z899 : W := mkw 0x061428a03010a020 0x8061428a03010a02 0x4e3fffff7018c03b 0xf4e3fffff7018c03

def z900 : W := mkw 0x0d364000e9b20008 0x00d364000e9b2000 0xafffc000ffff000d 0xfafffc000ffff000

def z901 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x71d930cc0e3fc7fd 0x271d930cc0e3fc7f

def z902 : W := mkw 0x0000411500c31bc8 0x20000411500c31bc 0x7027cf3f01c73fc3 0xd7027cf3f01c73fc

def z903 : W := mkw 0x20024115a4ff1bcc 0x220024115a4ff1bc 0xb000000081ff3fc4 0x0b000000081ff3fc

def z904 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xa027cf3f81e73f05 0xda027cf3f81e73f0

def z905 : W := mkw 0x0000410500c31348 0x20000410500c3134 0xf027cf3f81c73f07 0xdf027cf3f81c73f0

def z906 : W := mkw 0x0040144800000000 0x0004014480000000 0x4027ffff00000003 0xd4027ffff0000000

def z907 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0x9e1e38f0f038f8fc 0x69e1e38f0f038f8f

def z908 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafffcb33ffff000d 0xfafffcb33ffff000

def z909 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0xcffffffff000000f 0xfcffffffff000000

def z910 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xefffc03fffff000d 0xfefffc03fffff000

def z911 : W := mkw 0x0dbd80004d0c0000 0x00dbd80004d0c000 0xafffc000ffff000d 0xfafffc000ffff000

def z912 : W := mkw 0x29ab4000edbe000c 0x029ab4000edbe000 0xaff90000ffff000d 0xfaff90000ffff000

def z913 : W := mkw 0x6ffdbeea241c0004 0x06ffdbeea241c000 0x4fffffff00180003 0xf4fffffff0018000

def z914 : W := mkw 0x00024115b0f3bbe8 0xa00024115b0f3bbe 0xb0000000f1e73fc4 0x0b0000000f1e73fc

def z915 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfe03700ffc0ff0c 0xabfe03700ffc0ff0

def z916 : W := mkw 0x02022810b030a8a0 0x802022810b030a8a 0xde1838c0f038f8ff 0x7de1838c0f038f8f

def z917 : W := mkw 0x46ddbeea00000000 0x046ddbeea0000000 0x41dfffff00000003 0xb41dfffff0000000

def z918 : W := mkw 0x6dbfc04aedbe000c 0x06dbfc04aedbe000 0xafffc00fffff000d 0xfafffc00fffff000

def z919 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x7fffffff00000707 0xf7fffffff0000070

def z920 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xb027cf3f81c73f06 0xdb027cf3f81c73f0

def z921 : W := mkw 0x49e9964a00000000 0x049e9964a0000000 0x41ffffff00000003 0xf41ffffff0000000

def z922 : W := mkw 0x49e9964a00000000 0x049e9964a0000000 0x01e7cf3f00000000 0xc01e7cf3f0000000

def z923 : W := mkw 0x4ffdbeea49000000 0x04ffdbeea4900000 0x6fffffff0fc00003 0xf6fffffff0fc0000

def z924 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4fffcfff00000001 0xc4fffcfff0000000

def z925 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xfe1f38f0f03ff8ff 0xffe1f38f0f03ff8f

def z926 : W := mkw 0x0042551582e35fca 0x20042551582e35fc 0xb1c034008fe7ffce 0xbb1c034008fe7ffc

def z927 : W := mkw 0x0002411586ef5fda 0x60002411586ef5fd 0xb00000008fe73fc4 0x0b00000008fe73fc

def z928 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0xdfffffff80003807 0xfdfffffff8000380

def z929 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf027ff3f81e7ffcf 0xff027ff3f81e7ffc

def z930 : W := mkw 0x09a900004d0c0000 0x009a900004d0c000 0xafe10000ffc7000c 0xfafe10000ffc7000

def z931 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafffcf00ffff000f 0xfafffcf00ffff000

def z932 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x61d934cc0e3fc7f9 0xa61d934cc0e3fc7f

def z933 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xbfffc800ffff380f 0xfbfffc800ffff380

def z934 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf1e7cf3f8fe73fcf 0xff1e7cf3f8fe73fc

def z935 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xfe27cf3ff1e73fcf 0xffe27cf3ff1e73fc

def z936 : W := mkw 0x2dbfc010edbe088c 0x02dbfc010edbe088 0xafffc830ffff380d 0xfafffc830ffff380

def z937 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde3efbf3f038f8ff 0x7de3efbf3f038f8f

def z938 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0xefffffff81c00007 0xfefffffff81c0000

def z939 : W := mkw 0x0dbf0000ed3c0000 0x00dbf0000ed3c000 0xafff0000ffff000d 0xfafff0000ffff000

def z940 : W := mkw 0x4ffdbeea20100020 0x84ffdbeea2010002 0x4fffffff00180033 0xf4fffffff0018003

def z941 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x71dff4ff0e3fc7ff 0xb71dff4ff0e3fc7f

def z942 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x71fff4cc0e3fc7ff 0xf71fff4cc0e3fc7f

def z943 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0x2000000001e707c0 0x02000000001e707c

def z944 : W := mkw 0x0000000000000000 0x0000000000000000 0x6027cf3f00270007 0xd6027cf3f0027000

def z945 : W := mkw 0x449d80ea00000000 0x0449d80ea0000000 0x403fc7ff00000001 0x8403fc7ff0000000

def z946 : W := mkw 0x4b603eea00000000 0x04b603eea0000000 0x4fe7ffff00000003 0xf4fe7ffff0000000

def z947 : W := mkw 0x29a9c0004d8e000c 0x029a9c0004d8e000 0x2fe1c0007fc70008 0xa2fe1c0007fc7000

def z948 : W := mkw 0x0202691590e3bbc8 0x20202691590e3bbc 0xbe003800f1e7ffce 0x7be003800f1e7ffc

def z949 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xbffff000ffffc00f 0xfbffff000ffffc00

def z950 : W := mkw 0x1b2029005b40f603 0x01b2029005b40f60 0xbfe03800ffc0ff0e 0xfbfe03800ffc0ff0

def z951 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xeffff0c0ffff000f 0xfeffff0c0ffff000

def z952 : W := mkw 0x1b603fa05b40f603 0x01b603fa05b40f60 0xffe03ff0ffc0ff0e 0xfffe03ff0ffc0ff0

def z953 : W := mkw 0x7ffdbeea7f1ce407 0x07ffdbeea7f1ce40 0x0fd830c07e18c008 0x20fd830c07e18c00

def z954 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0x9000000081c03fc0 0x09000000081c03fc

def z955 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbff83f00fff8ff0f 0xfbff83f00fff8ff0

def z956 : W := mkw 0x0000000000000000 0x0000000000000000 0xd027cf3f80003807 0xdd027cf3f8000380

def z957 : W := mkw 0x1b603f485b40f613 0x41b603f485b40f61 0xbfe03fc0ffc0ff3e 0xfbfe03fc0ffc0ff3

def z958 : W := mkw 0x1b202b005b40f603 0x01b202b005b40f60 0xbfe00b00ffc0ff0c 0xfbfe00b00ffc0ff0

def z959 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0xffd934ccfe3fc7ff 0xfffd934ccfe3fc7f

def z960 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xffe03f00ffe0ffcf 0xfffe03f00ffe0ffc

def z961 : W := mkw 0x10024115fbf3ffeb 0xa10024115fbf3ffe 0xb0000000fffffffc 0x0b0000000fffffff

def z962 : W := mkw 0x2dbfc115edff1bcc 0x22dbfc115edff1bc 0xbfd80000ffff3fcc 0x2bfd80000ffff3fc

def z963 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbff83fc0ffd8ff3e 0xfbff83fc0ffd8ff3

def z964 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4fffffff0018c03b 0xf4fffffff0018c03

def z965 : W := mkw 0x4ffdbeea060c4412 0x44ffdbeea060c441 0x4fffffff0e000003 0xf4fffffff0e00000

def z966 : W := mkw 0x4ffdbeea060c4412 0x44ffdbeea060c441 0x6fffffff0e3fc03f 0xf6fffffff0e3fc03

def z967 : W := mkw 0x0000000000000000 0x0000000000000000 0x403fffff00000003 0xf403fffff0000000

def z968 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0x8fffc000ffff0009 0x68fffc000ffff000

def z969 : W := mkw 0x4ffdbeea3010a020 0x84ffdbeea3010a02 0x4fffffff70000003 0xf4fffffff7000000

def z970 : W := mkw 0x44dd94ea00000000 0x044dd94ea0000000 0x41ffffff00000003 0xf41ffffff0000000

def z971 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xffe03fc0ffc0fffe 0xfffe03fc0ffc0fff

def z972 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf027ffff81e7fff7 0xdf027ffff81e7fff

def z973 : W := mkw 0x4f34aaa200000000 0x04f34aaa20000000 0x0e27cf3f00000000 0xc0e27cf3f0000000

def z974 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x31d930c00e3fc7fd 0xb31d930c00e3fc7f

def z975 : W := mkw 0x4ffdbeea49000000 0x04ffdbeea4900000 0xcffffffff1c00003 0xfcffffffff1c0000

def z976 : W := mkw 0x0000000000000000 0x0000000000000000 0x0027cf3f00000000 0xc0027cf3f0000000

def z977 : W := mkw 0x4fbdaaea00000000 0x04fbdaaea0000000 0x4e3ffbff00000003 0x74e3ffbff0000000

def z978 : W := mkw 0x4fbdaaea00000000 0x04fbdaaea0000000 0x0e27cb3f00000000 0x40e27cb3f0000000

def z979 : W := mkw 0x46ddbeea00000000 0x046ddbeea0000000 0x4e1fffff00000003 0x74e1fffff0000000

def z980 : W := mkw 0x4f34aaa200000000 0x04f34aaa20000000 0x4e26cf3f00000002 0x44e26cf3f0000000

def z981 : W := mkw 0x5ffdbeea5f0ce413 0x45ffdbeea5f0ce41 0x4fffffff7e18c03b 0xf4fffffff7e18c03

def z982 : W := mkw 0x0002411584ef1bc8 0x20002411584ef1bc 0xb00000008fff3fcc 0x0b00000008fff3fc

def z983 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf027cf3f81c73fc2 0xcf027cf3f81c73fc

def z984 : W := mkw 0x2616e8b0b0b2a8ac 0x82616e8b0b0b2a8a 0xde1ef8f0f038f8ff 0x7de1ef8f0f038f8f

def z985 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xce1e38f0f038f8f9 0x6ce1e38f0f038f8f

def z986 : W := mkw 0x46162ab2b030a8a0 0x846162ab2b030a8a 0xde1e3bf3f038f8ff 0x7de1e3bf3f038f8f

def z987 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafffc000ffff0001 0xcafffc000ffff000

def z988 : W := mkw 0x6ffdbeea69100004 0x06ffdbeea6910000 0x4fffffff70000003 0xf4fffffff7000000

def z989 : W := mkw 0x4ffdbeea1000a000 0x04ffdbeea1000a00 0x4fffffff7000c00b 0xf4fffffff7000c00

def z990 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf03fcfff81ff3ff7 0xdf03fcfff81ff3ff

def z991 : W := mkw 0x0002411590e3bbc8 0x20002411590e3bbc 0xb0000000f1e7ffcc 0x0b0000000f1e7ffc

def z992 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafffc000ffdf0008 0xeafffc000ffdf000

def z993 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xaffff0c0ffffc03d 0xfaffff0c0ffffc03

def z994 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde1838f0f038f8fe 0x2de1838f0f038f8f

def z995 : W := mkw 0x2d36c000edbe000c 0x02d36c000edbe000 0xafe6c000ffff000c 0xfafe6c000ffff000

def z996 : W := mkw 0x4be9be4a00000000 0x04be9be4a0000000 0x4fe7ff3f00000003 0xf4fe7ff3f0000000

def z997 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0x9e1838c0f038f8fe 0x79e1838c0f038f8f

def z998 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf03fffff81e73fc7 0xff03fffff81e73fc

def z999 : W := mkw 0x061428a01000a000 0x0061428a01000a00 0xde1e38f0f038f8ff 0x7de1e38f0f038f8f

def z1000 : W := mkw 0x0002411590e3bbe8 0xa0002411590e3bbe 0xb000000081e7fff4 0x0b000000081e7fff

def z1001 : W := mkw 0x46543eea00000000 0x046543eea0000000 0x4e3fffff00000003 0xf4e3fffff0000000

def z1002 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x71f93fcc0e3fc7ff 0xf71f93fcc0e3fc7f

def z1003 : W := mkw 0x00890000040c0000 0x000890000040c000 0x61ffcf3f0e3f000f 0xf61ffcf3f0e3f000

def z1004 : W := mkw 0x39e9d74c4fcf575f 0x439e9d74c4fcf575 0x21e1c70c0fc70700 0x821e1c70c0fc7070

def z1005 : W := mkw 0x6dbfc0eaedbe000c 0x06dbfc0eaedbe000 0xafffc0c0ffff000d 0xfafffc0c0ffff000

def z1006 : W := mkw 0x2dbfc010edbe08ac 0x82dbfc010edbe08a 0xafffc000ffff00fd 0xfafffc000ffff00f

def z1007 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde1e30f0f038f8fd 0x2de1e30f0f038f8f

def z1008 : W := mkw 0x020028a000000000 0x0020028a00000000 0x4027ffff00000003 0xd4027ffff0000000

def z1009 : W := mkw 0x4f34aaa200000000 0x04f34aaa20000000 0x4e27cb3f00000001 0x44e27cb3f0000000

def z1010 : W := mkw 0x0920000049000000 0x0092000004900000 0xefe7cf3fffc0000f 0xfefe7cf3fffc0000

def z1011 : W := mkw 0x0b202a0000000000 0x00b202a000000000 0x4e27cf3f00000003 0xd4e27cf3f0000000

def z1012 : W := mkw 0x5ffdbeea5b00e403 0x05ffdbeea5b00e40 0x7fffffff7e00c70f 0xf7fffffff7e00c70

def z1013 : W := mkw 0x0000000000000000 0x0000000000000000 0x7027cf3f00000707 0xd7027cf3f0000070

def z1014 : W := mkw 0x00024115a0f31bc8 0x200024115a0f31bc 0xb0000000f1ff3fcc 0x0b0000000f1ff3fc

def z1015 : W := mkw 0x4f74beea00000000 0x04f74beea0000000 0x4e27ffff00000003 0xd4e27ffff0000000

def z1016 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf01830c081ffffff 0x3f01830c081fffff

def z1017 : W := mkw 0x4654beea00000000 0x04654beea0000000 0x4006ffff00000002 0x04006ffff0000000

def z1018 : W := mkw 0x00024115a0f31be8 0xa00024115a0f31be 0xb000000081ff3ff4 0x0b000000081ff3ff

def z1019 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x71f9f7cf0e3fc7ff 0xb71f9f7cf0e3fc7f

def z1020 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4fffffff0038000f 0xf4fffffff0038000

def z1021 : W := mkw 0x0960160000000000 0x0096016000000000 0x41e7cf3f00000003 0xd41e7cf3f0000000

def z1022 : W := mkw 0x1b603fa05b40f623 0x81b603fa05b40f62 0xbfe03fc0ffc0ff3e 0xfbfe03fc0ffc0ff3

def z1023 : W := mkw 0x4ffdbeea040c0000 0x04ffdbeea040c000 0x6fffffff0e070003 0xf6fffffff0e07000

def z1024 : W := mkw 0x0000000000000000 0x0000000000000000 0x5027cf3f002000c7 0xd5027cf3f002000c

def z1025 : W := mkw 0x5ffdbeea7b10e423 0x85ffdbeea7b10e42 0x4fffffff7e18c03b 0xf4fffffff7e18c03

def z1026 : W := mkw 0x20024115fdffbbec 0xa20024115fdffbbe 0xb0000000fffffffc 0x0b0000000fffffff

def z1027 : W := mkw 0x5ffdbeea1200e403 0x05ffdbeea1200e40 0x4fffffff0000c003 0xf4fffffff0000c00

def z1028 : W := mkw 0x041400a000000000 0x0041400a00000000 0x403fcfff00000003 0xd403fcfff0000000

def z1029 : W := mkw 0x0000010400411340 0x0000001040041134 0xf027cf3f81e73fc7 0xdf027cf3f81e73fc

def z1030 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xbfffc400ffff070f 0xfbfffc400ffff070

def z1031 : W := mkw 0x6ffdbeea6d1c0004 0x06ffdbeea6d1c000 0xefffffffffd8000f 0xfefffffffffd8000

def z1032 : W := mkw 0x0d34800000000000 0x00d3480000000000 0x4e27cf3f00000003 0xd4e27cf3f0000000

def z1033 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x71df3cfc0e3fc7ff 0xf71df3cfc0e3fc7f

def z1034 : W := mkw 0x020028b01000a8a0 0x8020028b01000a8a 0xde1838f0f038f8ff 0x7de1838f0f038f8f

def z1035 : W := mkw 0x2dbfc010edbe088c 0x02dbfc010edbe088 0xfffff8f0fffff8ff 0xffffff8f0fffff8f

def z1036 : W := mkw 0x0be93e4800000000 0x00be93e480000000 0x4fffffff00000003 0xf4fffffff0000000

def z1037 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf027cf3f81ffffff 0xdf027cf3f81fffff

def z1038 : W := mkw 0x4ffdbeea040c0000 0x04ffdbeea040c000 0x7fffffff0e3fc0ff 0xf7fffffff0e3fc0f

def z1039 : W := mkw 0x0000000000000000 0x0000000000000000 0x4007cf3f00000003 0x04007cf3f0000000

def z1040 : W := mkw 0x0002411582e35fda 0x60002411582e35fd 0xb000000081e7fff4 0x0b000000081e7fff

def z1041 : W := mkw 0x061428a03010a020 0x8061428a03010a02 0xde1838c0f038f8ff 0x7de1838c0f038f8f

def z1042 : W := mkw 0x061668b0b0b2a8a8 0x8061668b0b0b2a8a 0xde3ef8f0f1f8f8ff 0x7de3ef8f0f1f8f8f

def z1043 : W := mkw 0x00024115c9e31bc8 0x200024115c9e31bc 0xb0000000ffe73fcc 0x0b0000000ffe73fc

def z1044 : W := mkw 0x0000000000000000 0x0000000000000000 0x4026cf3f00000002 0x44026cf3f0000000

def z1045 : W := mkw 0x00c9144800000000 0x000c914480000000 0x41e7cf3f00000003 0xd41e7cf3f0000000

def z1046 : W := mkw 0x20024115cdef1bcc 0x220024115cdef1bc 0xb00000008fe73fc4 0x0b00000008fe73fc

def z1047 : W := mkw 0x649fc0ffa4bf09cc 0x2649fc0ffa4bf09c 0x401fc0ff003f00c1 0x0401fc0ff003f00c

def z1048 : W := mkw 0x00401404060d4552 0x400401404060d455 0x71d834c00e3fc7ff 0xb71d834c00e3fc7f

def z1049 : W := mkw 0x2dbdc0006d9e000c 0x02dbdc0006d9e000 0x2fd800007fdf0008 0x22fd800007fdf000

def z1050 : W := mkw 0x29224000edbe000c 0x029224000edbe000 0xafe7c000ffff000d 0xfafe7c000ffff000

def z1051 : W := mkw 0x092000004d0c0000 0x0092000004d0c000 0xafe00000ffff000c 0xfafe00000ffff000

def z1052 : W := mkw 0x4fbdaaea00000000 0x04fbdaaea0000000 0x4e3fcfff00000003 0xd4e3fcfff0000000

def z1053 : W := mkw 0x049f4000a4be0008 0x0049f4000a4be000 0xafffc000ffff000d 0xfafffc000ffff000

def z1054 : W := mkw 0x061669b5b0f3bbe8 0xa061669b5b0f3bbe 0xbe1830c0f1fffffc 0x2be1830c0f1fffff

def z1055 : W := mkw 0x19e9574d4fcf575b 0x619e9574d4fcf575 0x21e1c70f0fc70700 0x821e1c70f0fc7070

def z1056 : W := mkw 0x061428b03010a8a0 0x8061428b03010a8a 0xde1838f0f018f8fe 0x7de1838f0f018f8f

def z1057 : W := mkw 0x192001005b40f603 0x0192001005b40f60 0xbfe00f00ffc0ff0e 0xfbfe00f00ffc0ff0

def z1058 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfe03f00fff8fffe 0xfbfe03f00fff8fff

def z1059 : W := mkw 0x5b603fa25b40f603 0x05b603fa25b40f60 0xbfe03f33ffc0ff0e 0xfbfe03f33ffc0ff0

def z1060 : W := mkw 0x0000000000000000 0x0000000000000000 0xe027cf3f81c00007 0xde027cf3f81c0000

def z1061 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafe7c000ffe70005 0xdafe7c000ffe7000

def z1062 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf03fcf3f81ff3fcf 0xff03fcf3f81ff3fc

def z1063 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4fe7ffff00000002 0xc4fe7ffff0000000

def z1064 : W := mkw 0x096015004b405602 0x0096015004b40560 0xbfe03f00ffc0ff0e 0xfbfe03f00ffc0ff0

def z1065 : W := mkw 0x30024115ffffffcf 0x230024115ffffffc 0xb0000000ffffffcc 0x0b0000000ffffffc

def z1066 : W := mkw 0x0089000000000000 0x0008900000000000 0x41ffcf3f00000003 0xf41ffcf3f0000000

def z1067 : W := mkw 0x09a9800000000000 0x009a980000000000 0x41e7cf3f00000003 0xd41e7cf3f0000000

def z1068 : W := mkw 0x249fc015a4bf09cc 0x2249fc015a4bf09c 0x001fc000003f00c1 0x0001fc000003f00c

def z1069 : W := mkw 0x4dbd82ea00000000 0x04dbd82ea0000000 0x403fc3ff00000001 0x0403fc3ff0000000

def z1070 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfe13f00ffe7ff0f 0xfbfe13f00ffe7ff0

def z1071 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xffe63f30ffc0ff0f 0xfffe63f30ffc0ff0

def z1072 : W := mkw 0x2dbfc000edbe000c 0x02dbfc000edbe000 0xafe7c000ffc7000c 0xfafe7c000ffc7000

def z1073 : W := mkw 0x4ffdbeea060c4402 0x04ffdbeea060c440 0x7fffffff0e3fc70f 0xf7fffffff0e3fc70

def z1074 : W := mkw 0x4f34aaa200000000 0x04f34aaa20000000 0x4e3fffff00000003 0xf4e3fffff0000000

def z1075 : W := mkw 0x2dbdc0006d9e000c 0x02dbdc0006d9e000 0xaff9c000ffdf000c 0xfaff9c000ffdf000

def z1076 : W := mkw 0x5b603fea5b40f603 0x05b603fea5b40f60 0xffe7ffffffc0ff0f 0xfffe7ffffffc0ff0

def z1077 : W := mkw 0x2dbdc0004d8e000c 0x02dbdc0004d8e000 0xafffc000ffc7000d 0xfafffc000ffc7000

def z1078 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde1f3cfcf038f8ff 0xfde1f3cfcf038f8f

def z1079 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4ffff7ff00000001 0xa4ffff7ff0000000

def z1080 : W := mkw 0x2dbfc0b0edbe08ac 0x82dbfc0b0edbe08a 0xfffff0f0ffffc0ff 0xffffff0f0ffffc0f

def z1081 : W := mkw 0x469daaea00000000 0x0469daaea0000000 0x401fcbff00000001 0x0401fcbff0000000

def z1082 : W := mkw 0x02403dfd1241fff2 0xe02403dfd1241fff 0x50003fff0000fff2 0x050003fff0000fff

def z1083 : W := mkw 0x29e9d54d4fcf575e 0x629e9d54d4fcf575 0x21e1c70f0fc70700 0x821e1c70f0fc7070

def z1084 : W := mkw 0x4920820200000000 0x0492082020000000 0x4027cf3f00000003 0xd4027cf3f0000000

def z1085 : W := mkw 0x4f74beea00000000 0x04f74beea0000000 0x4fe6ffff00000002 0xf4fe6ffff0000000

def z1086 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0x7027cf3f01e73fc3 0x87027cf3f01e73fc

def z1087 : W := mkw 0x00c91400060c4402 0x000c91400060c440 0x71d934c00e3fc7ff 0xb71d934c00e3fc7f

def z1088 : W := mkw 0x2dbdc0006d9e000c 0x02dbdc0006d9e000 0x2fffc0007fdf0009 0xf2fffc0007fdf000

def z1089 : W := mkw 0x2dbfc048edbe001c 0x42dbfc048edbe001 0xafffc0c0ffff003d 0xfafffc0c0ffff003

def z1090 : W := mkw 0x49e9964a00000000 0x049e9964a0000000 0x41e7c73f00000001 0x841e7c73f0000000

def z1091 : W := mkw 0x020028001000a000 0x0020028001000a00 0xde27ff3ff000f80f 0xfde27ff3ff000f80

def z1092 : W := mkw 0x4ffdbeea1200e402 0x04ffdbeea1200e40 0xfffffffffe00ff0f 0xffffffffffe00ff0

def z1093 : W := mkw 0x42c93eea00000000 0x042c93eea0000000 0x41ffffff00000003 0xf41ffffff0000000

def z1094 : W := mkw 0x449d80ea00000000 0x0449d80ea0000000 0x401fcfff00000003 0x0401fcfff0000000

def z1095 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x0fffcf3f00000001 0xf0fffcf3f0000000

def z1096 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xb027cf3f81e73fc4 0xcb027cf3f81e73fc

def z1097 : W := mkw 0x249f4000edbe000c 0x0249f4000edbe000 0xafdf0000ffff000d 0xfafdf0000ffff000

def z1098 : W := mkw 0x10024115dfefffdb 0x610024115dfefffd 0xb0000000fffffffc 0x0b0000000fffffff

def z1099 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x5fffffff002000c7 0xf5fffffff002000c

def z1100 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0x9fe03f00ffc0ff0a 0x69fe03f00ffc0ff0

def z1101 : W := mkw 0x5ffdbeea5900a001 0x05ffdbeea5900a00 0x4fffffff70000003 0xf4fffffff7000000

def z1102 : W := mkw 0x6ffdbeea4d0c0004 0x06ffdbeea4d0c000 0x4fffffff0e000003 0xf4fffffff0e00000

def z1103 : W := mkw 0x249fc05da4bf09dc 0x6249fc05da4bf09d 0x401fc0ff003f00f1 0x0401fc0ff003f00f

def z1104 : W := mkw 0x2dbfc0b0edbe08ac 0x82dbfc0b0edbe08a 0xafffc030ffff000d 0xfafffc030ffff000

def z1105 : W := mkw 0x6dbfc0faedbe08ac 0x86dbfc0faedbe08a 0xefffc0ffffff00fd 0xfefffc0ffffff00f

def z1106 : W := mkw 0x5b60bf025b40f603 0x05b60bf025b40f60 0xbfe0ff03ffc0ff0e 0xfbfe0ff03ffc0ff0

def z1107 : W := mkw 0x6dbfc202edbe000c 0x06dbfc202edbe000 0xafffc303ffff000d 0xfafffc303ffff000

def z1108 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xb000040081e73fc6 0x9b000040081e73fc

def z1109 : W := mkw 0x061428b03010a8a0 0x8061428b03010a8a 0x5e1838f07038f8ff 0x35e1838f07038f8f

def z1110 : W := mkw 0x5b603fea5b40f603 0x05b603fea5b40f60 0xbfe03fc0ffc0ff0e 0xfbfe03fc0ffc0ff0

def z1111 : W := mkw 0x0200280000000000 0x0020028000000000 0x4e27ff3f00000003 0xf4e27ff3f0000000

def z1112 : W := mkw 0x4be9beea00000000 0x04be9beea0000000 0x41e7ffff00000003 0xd41e7ffff0000000

def z1113 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xffde38f0fe38f8ff 0xfffde38f0fe38f8f

def z1114 : W := mkw 0x04160010a0300880 0x004160010a030088 0xde1e38f0f038f8ff 0x7de1e38f0f038f8f

def z1115 : W := mkw 0x2dbfc011edbe088c 0x22dbfc011edbe088 0xafffc033ffff000d 0xfafffc033ffff000

def z1116 : W := mkw 0x4ffdbeea060c4412 0x44ffdbeea060c441 0x7fffffff0e18c73f 0xf7fffffff0e18c73

def z1117 : W := mkw 0x4ffdbeea1000a000 0x04ffdbeea1000a00 0x5fffffff0000f803 0xf5fffffff0000f80

def z1118 : W := mkw 0x0f743ea000000000 0x00f743ea00000000 0x4fffffff00000003 0xf4fffffff0000000

def z1119 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x41ffffff00000003 0x841ffffff0000000

def z1120 : W := mkw 0x4040164a00000000 0x04040164a0000000 0x4027cf3f00000003 0xd4027cf3f0000000

def z1121 : W := mkw 0x7ffdbeea7f1ce407 0x07ffdbeea7f1ce40 0x4fffffff7e18c00b 0xf4fffffff7e18c00

def z1122 : W := mkw 0x196017004b405603 0x0196017004b40560 0xbfe00f00ffc03f0e 0xfbfe00f00ffc03f0

def z1123 : W := mkw 0x2d364000edbe000c 0x02d364000edbe000 0xaffe0000ffff000d 0xfaffe0000ffff000

def z1124 : W := mkw 0x12403f051241f743 0x212403f051241f74 0x10003f0f0000ff02 0x010003f0f0000ff0

def z1125 : W := mkw 0x29a9c0004d8e000c 0x029a9c0004d8e000 0xafe1c000ffc70000 0xcafe1c000ffc7000

def z1126 : W := mkw 0x2dbd80006d1c0004 0x02dbd80006d1c000 0x4fffcf3f7e18000b 0xf4fffcf3f7e18000

def z1127 : W := mkw 0x4ffdbeea3010a020 0x84ffdbeea3010a02 0xdffffffff018f83f 0xfdffffffff018f83

def z1128 : W := mkw 0x4ffdbeea02004402 0x04ffdbeea0200440 0x7fffffff0e38c7ff 0xf7fffffff0e38c7f

def z1129 : W := mkw 0x2f36e9b1f9f2baac 0xa2f36e9b1f9f2baa 0x8e26cb33f1c03800 0x48e26cb33f1c0380

def z1130 : W := mkw 0x5ffdbeea5b00e403 0x05ffdbeea5b00e40 0xdffffffffe00f80f 0xfdffffffffe00f80

def z1131 : W := mkw 0x441480a200000000 0x0441480a20000000 0x4027cf3f00000003 0xd4027cf3f0000000

def z1132 : W := mkw 0x40c9164e060d4552 0x440c9164e060d455 0x71d937cf0e3fc7ff 0xb71d937cf0e3fc7f

def z1133 : W := mkw 0x06dd3ce800000000 0x006dd3ce80000000 0x4fffffff00000003 0xf4fffffff0000000

def z1134 : W := mkw 0x449d80ea00000000 0x0449d80ea0000000 0x403fcbff00000001 0x4403fcbff0000000

def z1135 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde1e38f0f038f8f3 0x4de1e38f0f038f8f

def z1136 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0xde3e3ff0f038f8ff 0xfde3e3ff0f038f8f

def z1137 : W := mkw 0x061628b0b030a8a0 0x8061628b0b030a8a 0x9e1e30c0f038f8fd 0x79e1e30c0f038f8f

def z1138 : W := mkw 0x2dbfc010edbe088c 0x02dbfc010edbe088 0xffffcf3fffff38cf 0xfffffcf3fffff38c

def z1139 : W := mkw 0x00890004040d0140 0x000890004040d014 0x71d934cc0e3fc7ff 0xb71d934cc0e3fc7f

def z1140 : W := mkw 0x5ffdbeea5b00e403 0x05ffdbeea5b00e40 0xefffffffffc0c00f 0xfefffffffffc0c00

def z1141 : W := mkw 0x0414000000000000 0x0041400000000000 0x4e3fcf3f00000003 0xf4e3fcf3f0000000

def z1142 : W := mkw 0x2dbfc048edbe000c 0x02dbfc048edbe000 0xefffc0ccffff000d 0xfefffc0ccffff000

def z1143 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfe03f00ffc0ff02 0xcbfe03f00ffc0ff0

def z1144 : W := mkw 0x2dbfc0a0edbe002c 0x82dbfc0a0edbe002 0xafffc0c0ffff003d 0xfafffc0c0ffff003

def z1145 : W := mkw 0x061428a000000000 0x0061428a00000000 0x4e27cf3f00000003 0xd4e27cf3f0000000

def z1146 : W := mkw 0x4ffdbeea02004402 0x04ffdbeea0200440 0x4fffffff0e00c00b 0xf4fffffff0e00c00

def z1147 : W := mkw 0x0002411580e31bc8 0x20002411580e31bc 0xf000000081e73fc7 0x1f000000081e73fc

def z1148 : W := mkw 0x5b603f4a5b40f603 0x05b603f4a5b40f60 0xbfe03f0fffc0ff0e 0xfbfe03f0fffc0ff0

def z1149 : W := mkw 0x09ab4000cdae0008 0x009ab4000cdae000 0xafffc000ffff000d 0xfafffc000ffff000

def z1150 : W := mkw 0x292040004d8e000c 0x0292040004d8e000 0xafe00000ffc7000c 0xfafe00000ffc7000

def z1151 : W := mkw 0x4ffdbeea20100000 0x04ffdbeea2010000 0x4fffffff7018000b 0xf4fffffff7018000

def z1152 : W := mkw 0x12403f4c1241f753 0x412403f4c1241f75 0x10003f0c0000ff02 0x010003f0c0000ff0

def z1153 : W := mkw 0x0002411584ef1bd8 0x60002411584ef1bd 0xb000000081ff3ff4 0x0b000000081ff3ff

def z1154 : W := mkw 0x049f40fda4bf09f8 0xe049f40fda4bf09f 0x401fc0ff003f00f1 0x0401fc0ff003f00f

def z1155 : W := mkw 0x0ffdbe0000000000 0x00ffdbe000000000 0x4fffff3f00000003 0xf4fffff3f0000000

def z1156 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x5fffffff0000c0f3 0xf5fffffff0000c0f

def z1157 : W := mkw 0x4ffdbeea361ce432 0xc4ffdbeea361ce43 0x4fffffff7e18c03b 0xf4fffffff7e18c03

def z1158 : W := mkw 0x20024115e9f31bcc 0x220024115e9f31bc 0xb0000000f1e73fc4 0x0b0000000f1e73fc

def z1159 : W := mkw 0x12403f041241f743 0x012403f041241f74 0x50003f0c0000ffc2 0x050003f0c0000ffc

def z1160 : W := mkw 0x0040140402014542 0x0004014040201454 0x71d934cc0e3fc7ff 0xb71d934cc0e3fc7f

def z1161 : W := mkw 0x469da8ea00000000 0x0469da8ea0000000 0x4e3fffff00000003 0xf4e3fffff0000000

def z1162 : W := mkw 0x0b2029005940b200 0x00b2029005940b20 0xbfe03f00ffc0ff0e 0xfbfe03f00ffc0ff0

def z1163 : W := mkw 0x0fbda8a000000000 0x00fbda8a00000000 0x4fffffff00000003 0xf4fffffff0000000

def z1164 : W := mkw 0x00c9144c060d4552 0x400c9144c060d455 0x51d934cc0e3fc7fb 0x251d934cc0e3fc7f

def z1165 : W := mkw 0x061668b0b0b2a8a8 0x8061668b0b0b2a8a 0xde1ff8f0f03ff8ff 0x7de1ff8f0f03ff8f

def z1166 : W := mkw 0x1b603f005b40f603 0x01b603f005b40f60 0xbfe00f00ffc0ff0c 0xcbfe00f00ffc0ff0

def z1167 : W := mkw 0x0040140000000000 0x0004014000000000 0x41e7ff3f00000003 0xf41e7ff3f0000000

def z1168 : W := mkw 0x1f366bb1f9f2baa9 0xa1f366bb1f9f2baa 0x8e26cb33f1c03800 0x48e26cb33f1c0380

def z1169 : W := mkw 0x4dfd964a00000000 0x04dfd964a0000000 0x4fffcf3f00000003 0xf4fffcf3f0000000

def z1170 : W := mkw 0x4ffdbeea00000000 0x04ffdbeea0000000 0x4e3fffff00000003 0x44e3fffff0000000

def z1171 : W := mkw 0x4ffdbeea040c0000 0x04ffdbeea040c000 0x4fffffff003f0003 0xf4fffffff003f000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z6])],[(0,[z8,z1,z2,z3,z4,z5,z6]),(0,[z9,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z11,z3,z4,z5,z6]),(0,[z1,z2,z12,z3,z4,z5,z6])],[(0,[z13,z1,z2,z3,z14,z4,z5])],[(0,[z15,z16,z2,z3,z4,z5,z6]),(0,[z1,z2,z17,z18,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z5,z6]),(0,[z1,z2,z20,z4,z21,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z22]),(0,[z1,z2,z3,z4,z5,z23,z6]),(0,[z1,z2,z3,z4,z5,z24,z6]),(0,[z1,z2,z3,z25,z4,z26,z6]),(0,[z27,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z28,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z29]),(0,[z1,z2,z3,z4,z30,z5,z6]),(0,[z1,z31,z2,z3,z25,z4,z6]),(0,[z1,z2,z32,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z33,z5,z6])],[(0,[z1,z2,z34,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z35,z5,z6]),(0,[z36,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z37,z3,z4,z5,z6])],[(0,[z1,z2,z3,z38,z39,z5,z6]),(0,[z40,z41,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z42,z6]),(0,[z1,z2,z3,z43,z4,z44,z6])]],
   [[(0,[z41,z1,z2,z3,z25,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z45])],[(0,[z46,z1,z2,z3,z4,z5,z47]),(0,[z48,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z49,z4,z6]),(0,[z1,z2,z3,z4,z50,z51,z6])],[(1,[z1,z2,z3,z52,z4,z5]),(0,[z40,z1,z2,z3,z25,z4,z6]),(1,[z53,z1,z54,z4,z5,z6]),(0,[z1,z2,z3,z4,z55,z5,z6])],[(0,[z1,z2,z3,z56,z4,z5,z6]),(0,[z1,z2,z3,z4,z57,z5,z6]),(0,[z13,z1,z2,z58,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z59,z6]),(0,[z1,z2,z3,z4,z5,z6,z60])],[(0,[z16,z2,z3,z61,z4,z5,z6]),(0,[z1,z62,z2,z3,z4,z5,z6]),(1,[z1,z63,z3,z64,z5,z6]),(0,[z1,z2,z3,z65,z4,z5,z6]),(0,[z1,z2,z3,z4,z26,z66,z6])],[(0,[z1,z2,z3,z4,z67,z5,z6]),(1,[z1,z68,z69,z4,z5,z6]),(0,[z1,z2,z3,z70,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z51,z71])],[(0,[z1,z72,z2,z3,z4,z5,z6]),(0,[z73,z1,z2,z3,z44,z5,z6]),(0,[z1,z2,z3,z74,z4,z5,z6]),(1,[z1,z2,z75,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z76,z6])],[(0,[z1,z2,z3,z4,z77,z5,z6]),(0,[z78,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z66,z6,z79])]],
   [[(0,[z1,z80,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z81,z6]),(0,[z13,z1,z2,z3,z4,z26,z5]),(0,[z1,z2,z3,z82,z4,z5,z6])],[(0,[z83,z1,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z61,z4,z5]),(0,[z1,z2,z3,z4,z26,z5,z6])],[(0,[z1,z2,z3,z4,z5,z84,z6]),(0,[z41,z2,z3,z4,z5,z85,z6])],[(0,[z86,z1,z2,z3,z4,z87,z6]),(0,[z88,z2,z3,z4,z39,z5,z6]),(0,[z1,z89,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z90,z4,z5,z6]),(0,[z1,z2,z3,z91,z4,z39,z6]),(0,[z92,z1,z2,z3,z4,z5,z6]),(0,[z1,z93,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z94,z5,z6]),(0,[z1,z2,z3,z4,z5,z47,z95]),(0,[z1,z2,z3,z4,z5,z96,z6]),(0,[z1,z2,z3,z97,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z98]),(0,[z1,z2,z3,z4,z5,z6,z99])],[(0,[z1,z2,z3,z4,z5,z100,z6]),(0,[z53,z13,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z101,z6]),(0,[z1,z2,z3,z4,z102,z5,z6])],[(0,[z103,z1,z2,z18,z4,z5,z6]),(0,[z1,z2,z3,z104,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z105,z6])],[(0,[z106,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z107,z5,z6]),(0,[z1,z2,z108,z3,z4,z5,z6]),(0,[z109,z1,z2,z3,z4,z5,z6]),(0,[z110,z1,z2,z4,z5,z111,z6]),(0,[z1,z2,z112,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z50,z5,z6])]],
   [[(0,[z1,z113,z2,z3,z61,z4,z5]),(0,[z1,z2,z3,z114,z4,z5,z6]),(0,[z13,z1,z2,z115,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z116]),(0,[z1,z2,z117,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z47,z118]),(0,[z1,z2,z3,z119,z4,z5,z6]),(0,[z120,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z121,z6]),(0,[z1,z2,z3,z4,z5,z6,z122])],[(0,[z86,z1,z2,z18,z4,z5,z6]),(0,[z123,z1,z2,z3,z4,z5,z6]),(0,[z1,z31,z2,z3,z43,z4,z6]),(0,[z1,z124,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z125,z4,z5,z6]),(0,[z1,z2,z126,z3,z4,z5,z99])],[(0,[z1,z2,z3,z4,z5,z6,z127]),(0,[z1,z2,z128,z3,z4,z5,z6]),(0,[z1,z2,z129,z3,z21,z5,z6])],[(0,[z1,z130,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z131,z6]),(0,[z1,z2,z3,z4,z5,z6,z132])],[(0,[z41,z1,z2,z3,z43,z4,z6]),(0,[z13,z1,z2,z3,z38,z4,z5]),(0,[z1,z2,z133,z3,z4,z5,z6]),(0,[z1,z2,z134,z3,z4,z5,z6])],[(0,[z1,z2,z135,z3,z4,z5,z6]),(0,[z53,z1,z2,z3,z4,z136,z6]),(0,[z53,z1,z3,z54,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z137,z6]),(0,[z1,z2,z3,z4,z138,z5,z6]),(0,[z1,z2,z3,z38,z4,z5,z51])],[(0,[z1,z139,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z140,z5,z6]),(0,[z1,z2,z141,z3,z4,z5,z6]),(0,[z40,z1,z2,z3,z43,z4,z6]),(0,[z10,z1,z124,z3,z4,z5,z6]),(0,[z1,z2,z3,z142,z4,z5,z6])],[(0,[z1,z2,z143,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z71]),(0,[z1,z2,z3,z4,z5,z144,z6]),(1,[z1,z2,z3,z4,z5,z127]),(0,[z1,z2,z3,z145,z38,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z146])]],
   [[(0,[z1,z2,z69,z3,z4,z5,z6]),(0,[z1,z147,z2,z3,z148,z5,z6]),(0,[z1,z2,z3,z43,z4,z26,z6])],[(0,[z46,z15,z1,z2,z3,z4,z5]),(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z150,z5,z6,z95]),(0,[z41,z1,z2,z74,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z148,z5]),(0,[z1,z2,z3,z4,z151,z5,z6])],[(0,[z13,z1,z2,z3,z4,z21,z5]),(0,[z1,z2,z152,z3,z4,z5,z6]),(0,[z1,z2,z3,z25,z4,z153,z6])],[(0,[z1,z2,z3,z154,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z155,z6])],[(1,[z1,z2,z3,z4,z5,z42]),(0,[z1,z2,z3,z20,z64,z5,z6]),(0,[z1,z2,z3,z4,z156,z5,z6])],[(0,[z157,z1,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z158,z4,z5]),(0,[z159,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z160,z4,z5,z6])],[(0,[z1,z2,z3,z4,z26,z19,z6]),(1,[z1,z2,z3,z4,z161,z6]),(0,[z162,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z111,z95]),(0,[z1,z2,z3,z4,z26,z5,z66])],[(0,[z1,z2,z3,z4,z19,z5,z163]),(0,[z46,z1,z2,z3,z4,z164,z5]),(0,[z165,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z166]),(0,[z1,z167,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z168,z3,z4,z5,z6]),(0,[z1,z2,z169,z3,z4,z5,z6]),(1,[z1,z2,z3,z170,z4,z5]),(0,[z41,z1,z2,z3,z4,z85,z6]),(0,[z1,z2,z3,z171,z4,z5,z6]),(0,[z46,z1,z2,z126,z3,z4,z5]),(0,[z172,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z173,z4,z5,z6]),(0,[z1,z2,z3,z145,z4,z5,z6])],[(1,[z46,z1,z2,z75,z4,z5]),(0,[z1,z2,z3,z174,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z175]),(0,[z1,z2,z134,z3,z4,z176,z6]),(0,[z1,z2,z3,z177,z4,z5,z66])],[(0,[z40,z1,z2,z3,z4,z85,z6]),(1,[z46,z13,z2,z3,z4,z5]),(0,[z1,z63,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z178]),(1,[z1,z2,z3,z5,z6,z79])],[(0,[z1,z2,z18,z3,z4,z5,z179]),(1,[z41,z2,z3,z4,z85,z6]),(0,[z1,z2,z3,z180,z4,z5,z6]),(0,[z1,z2,z129,z3,z4,z181,z6])],[(0,[z1,z2,z3,z4,z5,z6,z182]),(0,[z183,z13,z1,z2,z3,z4,z5]),(0,[z1,z2,z58,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z166]),(0,[z1,z2,z3,z184,z4,z5,z6]),(0,[z1,z185,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z71,z6]),(0,[z186,z1,z2,z3,z4,z5,z6]),(0,[z1,z187,z2,z3,z4,z5,z6])],[(1,[z46,z1,z2,z3,z4,z76]),(0,[z188,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z189]),(0,[z1,z190,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z191]),(0,[z1,z2,z3,z158,z4,z5,z6]),(0,[z53,z1,z2,z69,z4,z5,z6]),(0,[z1,z2,z129,z3,z4,z35,z6]),(0,[z1,z2,z3,z192,z4,z5,z6])],[(0,[z1,z2,z193,z4,z148,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z194])]],
   [[(0,[z46,z1,z2,z195,z3,z4,z5]),(0,[z46,z1,z2,z3,z4,z196,z5]),(0,[z1,z2,z3,z197,z4,z5,z6]),(0,[z1,z2,z3,z25,z4,z198,z6])],[(0,[z1,z2,z199,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z200]),(0,[z1,z2,z3,z201,z4,z5,z6])],[(0,[z1,z2,z3,z4,z202,z5,z6])],[(0,[z15,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z163,z6]),(0,[z1,z2,z3,z49,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z203,z6]),(0,[z1,z2,z134,z4,z5,z198,z6]),(0,[z1,z2,z3,z204,z4,z5,z6])],[(0,[z1,z2,z3,z205,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z47,z99]),(1,[z1,z2,z134,z4,z198,z6]),(0,[z1,z2,z3,z4,z206,z5,z6]),(0,[z1,z2,z3,z4,z5,z207,z6])],[],[(0,[z1,z208,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z158,z4,z5,z6]),(0,[z1,z209,z2,z3,z4,z5,z6])],[(0,[z1,z2,z210,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z211,z5,z6]),(1,[z1,z124,z3,z4,z5,z47]),(0,[z1,z2,z3,z4,z5,z6,z212])]],
   [[(0,[z16,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z213,z3,z4,z5,z6]),(0,[z1,z2,z75,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z111,z6,z99])],[(0,[z1,z214,z2,z3,z4,z5,z6]),(1,[z40,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z19,z5,z215]),(0,[z13,z1,z2,z3,z4,z148,z5]),(0,[z1,z2,z3,z4,z5,z216,z6])],[(0,[z1,z2,z3,z4,z217,z5,z6]),(0,[z46,z1,z2,z3,z218,z5,z6]),(0,[z1,z2,z3,z219,z4,z5,z6]),(0,[z220,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z129,z3,z20,z5,z6])],[(0,[z1,z221,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z67,z5,z85,z6]),(0,[z1,z2,z3,z4,z196,z5,z6]),(0,[z1,z222,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z118])],[(0,[z1,z223,z2,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z224,z4,z5])],[(0,[z225,z1,z2,z3,z4,z5,z6]),(1,[z1,z226,z3,z4,z5,z6]),(0,[z1,z2,z3,z227,z4,z5,z6]),(0,[z1,z228,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z229,z6]),(0,[z46,z1,z2,z3,z54,z4,z5]),(0,[z13,z1,z147,z2,z3,z4,z5]),(0,[z230,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z231,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z232,z6]),(0,[z183,z1,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z4,z5,z233]),(0,[z1,z2,z3,z64,z4,z5,z6]),(0,[z1,z2,z3,z4,z234,z5,z6]),(0,[z1,z2,z3,z4,z5,z235,z6]),(0,[z1,z2,z236,z3,z4,z5,z6])]],
   [[(1,[z88,z2,z3,z39,z5,z6]),(0,[z13,z1,z2,z126,z3,z4,z5]),(0,[z1,z2,z3,z237,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z238,z6]),(1,[z1,z2,z3,z38,z5,z51]),(0,[z1,z2,z3,z38,z5,z51,z6])],[(0,[z1,z239,z3,z4,z5,z6,z47]),(0,[z1,z2,z3,z240,z4,z5,z6]),(0,[z88,z1,z2,z3,z43,z5,z6]),(0,[z2,z3,z150,z4,z39,z5,z6]),(0,[z1,z2,z3,z4,z241,z5,z6]),(0,[z13,z1,z2,z3,z4,z242,z5]),(0,[z1,z147,z2,z3,z4,z5,z243]),(0,[z244,z1,z2,z3,z4,z5,z6]),(0,[z1,z245,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z246,z6]),(0,[z1,z2,z3,z4,z5,z247,z6]),(0,[z1,z2,z248,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z249,z5,z6]),(0,[z1,z2,z3,z4,z176,z250,z6]),(0,[z1,z2,z3,z4,z5,z66,z47]),(0,[z1,z2,z3,z43,z5,z6,z95])],[(1,[z1,z251,z2,z3,z4,z5]),(0,[z252,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z253,z3,z4,z5,z6])],[(0,[z254,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z255,z6]),(0,[z1,z2,z3,z256,z4,z5,z6]),(0,[z1,z2,z3,z177,z4,z6,z118])],[(0,[z1,z2,z3,z257,z4,z5,z6]),(0,[z258,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z224,z4,z5,z6]),(0,[z110,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z259,z3,z4,z5,z6]),(0,[z1,z2,z3,z260,z4,z5,z6]),(0,[z1,z2,z3,z170,z4,z39,z5]),(0,[z73,z1,z2,z3,z150,z5,z6]),(0,[z46,z53,z1,z2,z3,z4,z5]),(0,[z46,z1,z2,z3,z38,z4,z5]),(0,[z13,z1,z261,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z262,z6]),(0,[z1,z2,z3,z263,z4,z5,z6])]],
   [[(0,[z46,z1,z11,z2,z3,z4,z5]),(0,[z264,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z163]),(0,[z1,z2,z3,z4,z164,z5,z6]),(0,[z1,z31,z2,z3,z4,z5,z127]),(0,[z1,z265,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z266])],[(0,[z1,z2,z3,z4,z267,z5,z6]),(0,[z1,z2,z3,z150,z4,z5,z268]),(0,[z123,z46,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z269,z4,z5,z6]),(0,[z1,z2,z270,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z271,z5,z6]),(0,[z1,z2,z272,z3,z4,z5,z6])],[(0,[z273,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z274,z4,z5,z6]),(0,[z275,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z276,z6])],[(0,[z277,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z278,z3,z4,z5,z6]),(0,[z1,z279,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z280,z4,z5,z6]),(0,[z1,z2,z3,z4,z281,z5,z6])],[(0,[z1,z2,z3,z4,z5,z282,z6]),(0,[z46,z1,z2,z3,z4,z39,z5]),(0,[z1,z2,z3,z4,z5,z283,z6]),(0,[z1,z2,z3,z284,z4,z5,z6]),(0,[z1,z285,z2,z3,z4,z5,z6])],[(0,[z1,z286,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z21,z5]),(0,[z1,z2,z3,z4,z5,z287,z6]),(1,[z1,z31,z3,z4,z250,z6]),(0,[z1,z2,z3,z145,z4,z5,z51]),(0,[z1,z2,z3,z4,z5,z288,z6])],[(0,[z1,z2,z3,z4,z5,z268,z6]),(0,[z1,z31,z2,z3,z4,z250,z6]),(0,[z1,z2,z3,z4,z5,z289,z6]),(0,[z1,z2,z3,z38,z44,z5,z6])],[(0,[z46,z16,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z290]),(0,[z1,z2,z3,z291,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z51,z118])]],
   [[(0,[z1,z2,z3,z4,z5,z292,z6]),(0,[z1,z68,z2,z20,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z179,z6]),(0,[z1,z2,z3,z4,z293,z5,z6]),(0,[z1,z2,z3,z4,z5,z111,z6])],[(0,[z294,z1,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z196,z5,z6]),(0,[z295,z1,z2,z3,z4,z5,z6]),(0,[z1,z296,z2,z3,z4,z5,z6])],[(0,[z297,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z85,z198,z6]),(0,[z1,z2,z3,z4,z298,z5,z85]),(0,[z46,z110,z1,z2,z3,z4,z5]),(0,[z53,z1,z2,z3,z299,z5,z6]),(0,[z1,z2,z3,z4,z5,z300,z6])],[(0,[z1,z2,z3,z4,z5,z301,z6]),(1,[z46,z1,z2,z3,z4,z5]),(1,[z13,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z302,z5,z6])],[(0,[z303,z1,z2,z3,z4,z5,z6]),(0,[z304,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z305]),(0,[z157,z46,z1,z2,z3,z4,z5])],[(0,[z13,z1,z2,z3,z54,z4,z5]),(0,[z1,z2,z3,z306,z4,z5,z6])],[(0,[z1,z124,z2,z3,z4,z5,z47]),(0,[z1,z2,z3,z4,z5,z6,z307])]],
   [[(0,[z2,z239,z3,z61,z4,z5,z6]),(0,[z1,z2,z18,z3,z4,z5,z308]),(0,[z1,z2,z3,z4,z5,z309,z6])],[(0,[z1,z2,z310,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z311,z5,z6]),(0,[z1,z2,z3,z312,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z66,z71]),(0,[z1,z2,z313,z4,z21,z5,z6]),(0,[z1,z2,z3,z44,z5,z6,z95]),(0,[z1,z2,z3,z314,z4,z5,z6])],[(0,[z1,z2,z3,z4,z315,z5,z6]),(1,[z1,z2,z3,z4,z5,z215]),(0,[z46,z1,z2,z3,z4,z164,z6]),(0,[z1,z2,z316,z3,z4,z5,z6]),(0,[z317,z1,z2,z3,z4,z5,z6]),(0,[z1,z318,z2,z3,z4,z5,z6])],[(0,[z1,z319,z2,z3,z4,z5,z6]),(0,[z1,z31,z3,z4,z5,z250,z6]),(0,[z1,z2,z3,z4,z5,z320,z6])],[(0,[z1,z2,z3,z321,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z85,z6]),(1,[z1,z2,z3,z4,z136,z6]),(0,[z53,z1,z2,z313,z4,z5,z6]),(0,[z1,z322,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z323]),(0,[z1,z2,z3,z4,z5,z181,z6]),(0,[z1,z2,z3,z4,z5,z324,z6])],[(0,[z46,z1,z2,z239,z3,z4,z5]),(0,[z1,z2,z3,z52,z4,z39,z5]),(0,[z1,z2,z3,z4,z176,z85,z6]),(0,[z46,z1,z2,z3,z4,z5,z95])],[(0,[z1,z2,z325,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z326,z5,z6]),(0,[z1,z2,z3,z4,z5,z327,z6])]],
   [[(0,[z13,z1,z11,z2,z3,z4,z5]),(0,[z1,z2,z328,z3,z4,z5,z6]),(0,[z1,z2,z3,z91,z4,z5,z6]),(0,[z1,z2,z3,z329,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z330]),(0,[z1,z2,z3,z4,z331,z5,z6])],[(0,[z1,z251,z2,z239,z3,z4,z5]),(0,[z1,z2,z3,z218,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z332]),(0,[z46,z1,z2,z3,z4,z5,z118]),(1,[z1,z209,z3,z4,z333,z6]),(0,[z1,z2,z3,z4,z334,z5,z6])],[(0,[z1,z2,z3,z4,z5,z335,z6]),(0,[z46,z1,z2,z3,z4,z176,z5]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z3,z4,z5,z6,z336]),(0,[z1,z2,z337,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z338,z6]),(0,[z1,z2,z313,z3,z4,z5,z339]),(0,[z1,z2,z3,z340,z4,z5,z6]),(0,[z1,z2,z3,z341,z4,z5,z6])],[(0,[z15,z13,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z342,z5,z6]),(0,[z1,z2,z343,z3,z4,z5,z6]),(1,[z1,z2,z17,z4,z176,z6])],[(1,[z15,z239,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z39,z5]),(0,[z46,z1,z2,z3,z4,z5,z85]),(0,[z1,z68,z2,z3,z4,z5,z6]),(0,[z344,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z345,z5,z6])],[(0,[z15,z1,z11,z3,z4,z5,z6]),(0,[z46,z1,z2,z75,z3,z4,z5]),(0,[z46,z1,z124,z2,z3,z4,z5]),(0,[z1,z2,z3,z346,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z330])],[(0,[z1,z2,z3,z347,z4,z5,z6]),(0,[z1,z226,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z61,z4,z5,z198,z6]),(1,[z1,z195,z3,z4,z5,z6]),(0,[z1,z2,z126,z3,z4,z5,z6])]],
   [[(0,[z16,z13,z1,z2,z3,z4,z5]),(0,[z1,z348,z2,z3,z4,z5,z6]),(0,[z1,z2,z313,z3,z21,z5,z6]),(0,[z1,z2,z349,z3,z4,z5,z6])],[(1,[z16,z11,z3,z4,z5,z6]),(0,[z46,z1,z147,z2,z3,z4,z5]),(0,[z13,z1,z2,z3,z177,z4,z5]),(0,[z350,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z351,z5,z6]),(0,[z16,z1,z11,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z19,z5]),(0,[z1,z2,z3,z352,z4,z5,z6]),(0,[z353,z1,z2,z3,z4,z5,z6]),(0,[z354,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z355,z6])],[(1,[z1,z2,z3,z4,z5,z179]),(0,[z356,z1,z2,z3,z4,z5,z6]),(0,[z1,z63,z2,z3,z148,z5,z6]),(0,[z1,z2,z3,z4,z5,z51,z99]),(1,[z1,z2,z3,z25,z44,z6]),(0,[z357,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z358]),(0,[z1,z63,z3,z64,z4,z5,z6]),(0,[z1,z2,z3,z20,z4,z5,z6])],[(0,[z10,z1,z239,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z359]),(0,[z225,z46,z1,z2,z3,z4,z5]),(0,[z46,z1,z2,z3,z4,z5,z198]),(0,[z13,z2,z3,z4,z5,z360,z6]),(0,[z1,z2,z361,z3,z4,z5,z6]),(0,[z1,z2,z362,z3,z4,z5,z6]),(0,[z1,z124,z2,z3,z4,z5,z71]),(0,[z1,z2,z3,z25,z4,z176,z6]),(0,[z1,z363,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z364,z4,z5,z6]),(0,[z365,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z366]),(0,[z1,z2,z3,z4,z367,z5,z6])]],
   [[(0,[z1,z11,z3,z4,z5,z6,z47]),(0,[z88,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z368,z4,z5,z6]),(0,[z2,z3,z4,z19,z5,z85,z6]),(1,[z110,z1,z2,z4,z5,z111])],[(0,[z1,z369,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z76]),(0,[z1,z2,z3,z370,z4,z5,z6]),(0,[z1,z2,z17,z3,z4,z198,z6]),(0,[z1,z2,z3,z4,z5,z371,z6])],[(0,[z103,z2,z239,z3,z4,z5,z6]),(0,[z372,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z34,z3,z4,z5]),(0,[z373,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z374,z4,z5,z6]),(0,[z46,z1,z2,z75,z4,z5,z6]),(0,[z1,z2,z3,z4,z333,z5,z6])],[(0,[z46,z1,z68,z2,z3,z4,z5]),(0,[z1,z2,z3,z375,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z376])],[(0,[z252,z46,z1,z2,z3,z4,z5]),(0,[z1,z2,z377,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z378,z5,z6]),(0,[z1,z2,z3,z177,z4,z26,z6])],[(0,[z13,z1,z2,z239,z3,z4,z5]),(0,[z254,z13,z1,z2,z3,z4,z5]),(0,[z13,z1,z2,z3,z4,z5,z95]),(0,[z1,z2,z3,z4,z379,z5,z6]),(0,[z1,z2,z3,z4,z5,z380,z6])],[(1,[z1,z2,z3,z381,z4,z6]),(0,[z46,z1,z2,z129,z3,z4,z5]),(0,[z110,z13,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z382,z6]),(0,[z1,z2,z3,z4,z5,z383,z6]),(0,[z1,z2,z3,z4,z5,z384,z6]),(0,[z1,z2,z3,z385,z4,z5,z6])],[(0,[z110,z1,z2,z61,z4,z5,z6]),(0,[z1,z2,z3,z4,z298,z5,z6]),(0,[z1,z2,z3,z4,z19,z6,z118]),(1,[z46,z1,z2,z3,z196,z5]),(0,[z386,z1,z2,z3,z4,z5,z6]),(0,[z110,z1,z2,z3,z4,z5,z111]),(0,[z1,z2,z3,z4,z5,z6,z79])]],
   [[(0,[z1,z2,z18,z4,z5,z6,z99]),(0,[z1,z2,z3,z387,z4,z5,z6]),(0,[z264,z13,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z388,z4,z5,z6]),(0,[z1,z2,z389,z3,z4,z5,z6]),(0,[z1,z2,z3,z390,z4,z5,z6])],[(0,[z73,z2,z3,z150,z4,z5,z6]),(0,[z1,z2,z391,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z5,z332]),(0,[z13,z1,z2,z3,z4,z5,z118]),(0,[z1,z3,z4,z333,z5,z250,z6]),(1,[z1,z2,z3,z4,z35,z6])],[(0,[z1,z2,z392,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z176,z5]),(0,[z1,z2,z3,z4,z161,z5,z6]),(0,[z393,z1,z2,z3,z4,z5,z6]),(1,[z10,z1,z3,z4,z5,z71]),(0,[z394,z1,z2,z3,z4,z5,z6]),(0,[z395,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z396,z5,z85,z6]),(0,[z1,z2,z3,z4,z5,z397,z6]),(0,[z277,z46,z1,z2,z3,z4,z5]),(0,[z277,z13,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z398,z4,z5,z6])],[(0,[z13,z1,z2,z3,z4,z5,z85]),(0,[z1,z2,z3,z399,z4,z5,z6]),(0,[z400,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z51,z6,z95])],[(0,[z401,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z402,z6]),(0,[z46,z1,z2,z3,z4,z5,z99]),(0,[z13,z1,z124,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z403,z5,z6]),(0,[z404,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z43,z25,z5,z6])],[(0,[z405,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z406,z4,z6]),(0,[z1,z2,z407,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z408,z5,z6])],[(0,[z88,z1,z2,z3,z39,z5,z6]),(0,[z1,z2,z409,z3,z4,z5,z6]),(0,[z46,z40,z1,z2,z3,z4,z5]),(0,[z1,z410,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z411,z5,z6]),(0,[z1,z2,z412,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z39,z5,z6]),(0,[z1,z2,z413,z3,z4,z5,z6]),(1,[z353,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z64,z21,z5,z6]),(0,[z1,z2,z3,z4,z5,z339,z6]),(0,[z1,z2,z414,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z415,z6])],[(0,[z46,z1,z31,z2,z3,z4,z5]),(0,[z1,z2,z3,z416,z4,z5,z6]),(0,[z417,z1,z2,z3,z4,z5,z6])],[(0,[z418,z1,z2,z3,z4,z5,z6]),(0,[z1,z419,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z420,z6]),(0,[z13,z1,z2,z3,z4,z19,z5]),(0,[z421,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z43,z4,z153,z6])],[(0,[z88,z1,z2,z3,z44,z5,z6]),(0,[z1,z2,z3,z170,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z243,z6]),(0,[z1,z2,z3,z4,z422,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z423])],[(0,[z103,z16,z2,z3,z4,z5,z6]),(0,[z1,z2,z424,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z282]),(0,[z1,z2,z3,z425,z4,z5,z85]),(0,[z304,z13,z1,z2,z3,z4,z5]),(0,[z13,z1,z2,z3,z4,z5,z198]),(0,[z1,z2,z3,z4,z5,z6,z426]),(0,[z53,z1,z68,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z427,z6]),(0,[z1,z2,z3,z4,z428,z5,z6]),(0,[z1,z2,z3,z4,z5,z250,z6]),(0,[z1,z2,z3,z4,z5,z6,z429]),(0,[z1,z2,z3,z4,z430,z5,z6]),(0,[z1,z2,z431,z3,z4,z5,z6]),(0,[z432,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z433,z4,z5,z6]),(1,[z1,z2,z3,z425,z4,z5]),(0,[z434,z1,z2,z3,z4,z5,z6]),(0,[z1,z435,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z38,z150,z5,z6]),(0,[z1,z2,z3,z4,z5,z436,z6]),(0,[z1,z2,z3,z4,z437,z5,z6]),(0,[z1,z2,z3,z4,z5,z438,z6]),(0,[z1,z68,z69,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z439,z5,z6]),(0,[z1,z2,z3,z440,z4,z5,z6]),(0,[z1,z2,z3,z345,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z441,z4,z5,z6]),(1,[z46,z1,z2,z3,z4,z164]),(0,[z46,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z313,z3,z20,z5,z6])],[(0,[z1,z2,z442,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z153,z6])],[(0,[z1,z11,z2,z3,z4,z5,z6]),(0,[z1,z443,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z444,z6]),(0,[z1,z2,z3,z445,z4,z5,z6]),(0,[z1,z446,z2,z3,z4,z5,z6])],[(0,[z86,z2,z3,z61,z4,z5,z6]),(0,[z1,z447,z2,z3,z4,z5,z6]),(0,[z13,z1,z68,z2,z3,z4,z5]),(0,[z1,z448,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z449,z5,z6]),(0,[z450,z1,z2,z3,z4,z5,z6])],[(0,[z1,z251,z2,z3,z4,z5,z6]),(0,[z1,z2,z451,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z323,z6]),(0,[z10,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z452,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z453])],[(0,[z454,z1,z2,z3,z4,z5,z6]),(0,[z53,z1,z2,z3,z455,z5,z6]),(0,[z1,z2,z3,z456,z4,z5,z6])],[(0,[z86,z1,z2,z3,z4,z229,z6]),(0,[z13,z1,z2,z129,z3,z4,z5]),(0,[z457,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z50,z6])],[(0,[z458,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z34,z3,z61,z4,z5]),(0,[z1,z459,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z460,z5,z6])]],
   [[(0,[z1,z2,z3,z461,z4,z5,z6]),(0,[z1,z2,z3,z396,z4,z5,z6]),(0,[z1,z2,z3,z43,z4,z198,z6]),(1,[z1,z2,z3,z145,z5,z95])],[(0,[z1,z2,z3,z4,z5,z462,z6])],[(0,[z88,z73,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z463,z6]),(0,[z46,z10,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z299,z5,z6]),(1,[z1,z2,z193,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z464,z6]),(0,[z465,z1,z2,z3,z4,z5,z6]),(0,[z1,z466,z2,z3,z4,z5,z6])],[(0,[z41,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z467,z6]),(0,[z1,z2,z3,z4,z5,z6,z468]),(0,[z46,z1,z2,z3,z177,z4,z5]),(0,[z2,z3,z4,z5,z360,z6,z332]),(0,[z1,z469,z2,z3,z4,z5,z6])],[(0,[z1,z2,z470,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z471,z5,z6]),(0,[z1,z2,z472,z3,z4,z5,z6]),(0,[z40,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z5,z99]),(0,[z1,z2,z3,z43,z4,z5,z309]),(0,[z1,z2,z473,z3,z4,z5,z6])],[(0,[z474,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z475,z6]),(0,[z476,z1,z2,z3,z4,z5,z6]),(0,[z477,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z313,z3,z4,z5,z98]),(0,[z1,z2,z3,z4,z478,z5,z6]),(0,[z1,z2,z3,z479,z4,z5,z6])],[(0,[z13,z1,z1,z2,z3,z4,z5]),(0,[z53,z459,z2,z3,z4,z5,z6]),(0,[z1,z147,z2,z3,z64,z5,z6]),(0,[z1,z2,z174,z4,z148,z5,z6]),(0,[z1,z2,z3,z480,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z198,z6]),(0,[z1,z2,z3,z4,z481,z5,z6]),(0,[z1,z2,z3,z4,z5,z66,z95])]],
   [[(1,[z1,z2,z3,z4,z5,z308]),(0,[z1,z2,z3,z4,z5,z6,z482]),(0,[z1,z2,z3,z4,z5,z6,z215]),(0,[z1,z68,z2,z313,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z483,z6]),(0,[z1,z2,z3,z484,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z485,z6]),(0,[z1,z2,z3,z486,z4,z5,z6]),(0,[z1,z2,z3,z487,z4,z5,z6]),(0,[z1,z488,z2,z3,z4,z5,z6]),(0,[z1,z2,z126,z3,z4,z5,z111])],[(1,[z1,z2,z3,z4,z5,z468]),(0,[z13,z1,z31,z2,z3,z4,z5]),(0,[z489,z1,z2,z3,z4,z5,z6]),(0,[z1,z490,z2,z3,z4,z5,z6])],[(0,[z1,z491,z2,z3,z4,z5,z6]),(0,[z492,z1,z2,z3,z4,z5,z6]),(0,[z53,z1,z2,z54,z4,z5,z6]),(0,[z1,z493,z2,z3,z4,z5,z6])],[(0,[z1,z2,z239,z3,z4,z5,z6]),(0,[z494,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z115,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z495,z6]),(0,[z496,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z497,z4,z5,z6])],[(0,[z46,z1,z2,z3,z150,z4,z5]),(0,[z1,z498,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z51,z6,z266]),(0,[z1,z2,z3,z4,z499,z5,z6])],[(0,[z1,z2,z3,z150,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z500,z6]),(0,[z501,z1,z2,z3,z4,z5,z6]),(0,[z1,z502,z2,z3,z4,z5,z6]),(0,[z1,z209,z2,z3,z4,z333,z6]),(0,[z1,z2,z17,z134,z4,z5,z6]),(0,[z1,z2,z503,z3,z4,z5,z6])],[(0,[z1,z2,z504,z3,z4,z5,z6]),(0,[z1,z2,z3,z505,z4,z5,z6])]],
   [[(0,[z88,z13,z1,z2,z3,z4,z5]),(0,[z13,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z47]),(0,[z1,z2,z3,z4,z66,z6,z118])],[(0,[z1,z2,z3,z506,z4,z5,z6]),(0,[z46,z1,z226,z3,z4,z5,z6]),(0,[z1,z2,z3,z507,z4,z5,z6]),(0,[z1,z2,z17,z3,z4,z5,z6]),(0,[z1,z508,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z509,z6]),(0,[z16,z11,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z339]),(0,[z1,z2,z3,z510,z4,z5,z6])],[(0,[z511,z1,z2,z3,z4,z5,z6]),(0,[z46,z2,z3,z4,z5,z6,z332]),(0,[z13,z1,z2,z3,z4,z5,z101]),(0,[z1,z2,z3,z25,z4,z5,z6])],[(0,[z86,z13,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z512,z5,z6]),(0,[z46,z1,z2,z3,z145,z4,z5])],[(0,[z513,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z514,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z515])],[(0,[z1,z2,z3,z4,z26,z85,z6]),(0,[z1,z2,z3,z516,z4,z5,z6]),(0,[z1,z2,z3,z517,z4,z5,z6]),(0,[z1,z2,z518,z3,z4,z5,z6]),(0,[z1,z2,z17,z4,z176,z5,z6])],[(0,[z1,z147,z2,z3,z4,z5,z178]),(0,[z1,z519,z2,z3,z4,z5,z6])]],
   [[(0,[z110,z1,z2,z18,z4,z5,z6]),(0,[z1,z2,z368,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z19,z6]),(0,[z46,z1,z209,z2,z3,z4,z5])],[(0,[z1,z2,z3,z425,z4,z5,z6]),(0,[z1,z2,z3,z148,z21,z5,z6]),(0,[z1,z520,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z521,z6])],[(0,[z1,z2,z3,z4,z5,z522,z6]),(0,[z46,z86,z1,z2,z3,z4,z5]),(0,[z523,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z524,z6]),(0,[z40,z1,z2,z3,z4,z19,z6]),(0,[z53,z1,z2,z3,z4,z5,z166]),(0,[z525,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z526,z3,z4,z5,z6]),(0,[z1,z2,z3,z527,z4,z5,z6]),(0,[z1,z2,z3,z177,z4,z5,z118])],[(0,[z1,z2,z3,z528,z4,z5,z6]),(0,[z529,z1,z2,z3,z4,z5,z6]),(0,[z1,z209,z3,z4,z333,z5,z6]),(0,[z1,z209,z2,z3,z25,z4,z6]),(0,[z1,z2,z3,z44,z5,z153,z6]),(0,[z1,z2,z3,z145,z5,z6,z95])],[(0,[z1,z2,z3,z4,z5,z530,z6]),(0,[z1,z2,z3,z4,z531,z5,z6]),(0,[z1,z532,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z533]),(0,[z1,z2,z3,z4,z534,z5,z6]),(0,[z46,z1,z2,z17,z3,z4,z5]),(0,[z46,z1,z2,z3,z4,z5,z51]),(0,[z1,z68,z2,z69,z4,z5,z6]),(0,[z1,z2,z3,z20,z148,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z535]),(0,[z1,z536,z2,z3,z4,z5,z6])],[(0,[z15,z2,z239,z3,z4,z5,z6]),(0,[z537,z1,z2,z3,z4,z5,z6]),(0,[z1,z538,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z396,z5,z6]),(1,[z1,z2,z3,z4,z76,z6]),(0,[z1,z2,z3,z14,z4,z5,z6]),(0,[z1,z2,z17,z3,z4,z176,z6])],[(0,[z539,z1,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z313,z3,z4,z5]),(0,[z1,z540,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z406,z4,z148,z6]),(0,[z1,z2,z541,z3,z4,z5,z6])],[(0,[z542,z1,z2,z3,z4,z5,z6]),(1,[z46,z1,z195,z3,z4,z5]),(0,[z46,z1,z2,z3,z20,z4,z5]),(0,[z13,z1,z2,z3,z4,z5,z153]),(0,[z1,z209,z2,z3,z4,z250,z6]),(0,[z1,z2,z4,z176,z5,z198,z6])],[(1,[z1,z2,z74,z4,z5,z6])],[(0,[z1,z2,z3,z543,z4,z5,z6]),(0,[z1,z2,z3,z381,z4,z39,z6]),(0,[z1,z2,z3,z4,z544,z5,z6])],[(0,[z103,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z87,z5,z6]),(0,[z13,z1,z2,z3,z150,z4,z5])],[(0,[z13,z1,z2,z3,z4,z5,z66])],[(0,[z1,z2,z3,z25,z44,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z545])],[(0,[z86,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z546,z5,z6]),(0,[z1,z2,z3,z547,z4,z5,z6]),(1,[z1,z2,z3,z43,z153,z6]),(0,[z1,z2,z3,z43,z38,z5,z6])]],
   [[(0,[z46,z46,z1,z2,z3,z4,z5]),(0,[z46,z13,z1,z2,z3,z4,z5]),(1,[z13,z2,z3,z4,z5,z360]),(0,[z1,z2,z548,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z549,z6])],[(0,[z11,z2,z239,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z111]),(1,[z1,z2,z3,z4,z181,z6]),(0,[z1,z2,z3,z550,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z51,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z551,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z552]),(0,[z1,z2,z3,z145,z4,z5,z95])],[(0,[z103,z2,z18,z3,z4,z5,z6]),(0,[z40,z2,z3,z4,z19,z5,z6]),(0,[z46,z1,z2,z134,z3,z4,z5]),(0,[z1,z2,z553,z3,z4,z5,z6]),(0,[z10,z1,z3,z4,z5,z71,z6])],[(0,[z1,z2,z554,z3,z4,z5,z6]),(0,[z10,z13,z1,z2,z3,z4,z5]),(0,[z13,z1,z2,z3,z145,z4,z5]),(0,[z1,z2,z3,z555,z4,z5,z6]),(0,[z1,z2,z3,z556,z4,z5,z6]),(0,[z557,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z558,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z333,z5]),(0,[z1,z559,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z71,z95]),(0,[z1,z2,z3,z560,z4,z5,z6]),(0,[z1,z2,z3,z43,z4,z5,z330])],[(0,[z1,z2,z3,z4,z5,z561,z6]),(0,[z458,z46,z1,z2,z3,z4,z5]),(1,[z46,z1,z2,z3,z218,z5]),(0,[z46,z1,z2,z3,z218,z4,z5]),(0,[z46,z1,z2,z3,z4,z5,z250]),(0,[z1,z2,z3,z4,z562,z5,z6]),(0,[z1,z2,z3,z4,z5,z563,z6]),(0,[z1,z2,z3,z4,z5,z564,z6]),(0,[z1,z209,z2,z3,z43,z4,z6]),(0,[z1,z2,z565,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z67,z5,z6]),(0,[z46,z1,z63,z2,z3,z4,z5]),(0,[z13,z1,z209,z2,z3,z4,z5]),(0,[z1,z2,z566,z3,z4,z5,z6]),(0,[z1,z2,z3,z43,z4,z5,z6])],[(0,[z46,z13,z2,z3,z4,z5,z6]),(0,[z1,z69,z3,z54,z4,z5,z6]),(0,[z1,z567,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z568]),(0,[z569,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z570,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z571]),(0,[z1,z2,z3,z4,z572,z5,z6]),(0,[z46,z1,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z71,z118]),(0,[z1,z2,z3,z4,z573,z5,z6]),(0,[z1,z2,z3,z4,z5,z66,z6])],[(1,[z1,z2,z3,z4,z87,z6]),(1,[z86,z2,z61,z4,z5,z6]),(0,[z41,z13,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z574,z5,z6]),(1,[z1,z2,z129,z20,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z575])],[(0,[z1,z2,z3,z4,z5,z576,z6]),(0,[z46,z1,z2,z69,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z577])],[(0,[z40,z13,z1,z2,z3,z4,z5]),(0,[z46,z1,z2,z3,z64,z4,z5]),(0,[z13,z1,z2,z17,z3,z4,z5]),(0,[z1,z2,z3,z4,z578,z5,z6]),(0,[z13,z1,z2,z3,z4,z5,z51]),(0,[z1,z2,z129,z20,z4,z5,z6])],[(0,[z46,z103,z1,z2,z3,z4,z5]),(0,[z476,z46,z1,z2,z3,z4,z5]),(0,[z474,z13,z1,z2,z3,z4,z5]),(0,[z579,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z126,z4,z5,z99])],[(0,[z73,z1,z2,z3,z39,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z13,z1,z2,z313,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z580,z6]),(0,[z1,z2,z3,z4,z5,z581,z6]),(0,[z582,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z44,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z583,z5,z6]),(0,[z1,z31,z2,z3,z4,z5,z323]),(0,[z1,z2,z3,z4,z176,z5,z6]),(0,[z1,z2,z3,z584,z4,z5,z6])],[(0,[z1,z2,z3,z585,z4,z5,z6]),(0,[z1,z586,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z587,z4,z5,z6]),(0,[z13,z1,z2,z3,z20,z4,z5]),(1,[z1,z2,z3,z4,z5,z243])],[(0,[z1,z2,z3,z4,z588,z5,z6]),(0,[z1,z2,z3,z4,z5,z589,z6]),(0,[z46,z1,z2,z3,z25,z4,z5]),(0,[z10,z1,z2,z3,z4,z5,z47]),(0,[z1,z2,z3,z4,z590,z5,z6]),(0,[z1,z2,z3,z591,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z592,z6]),(0,[z1,z2,z3,z4,z5,z95,z118])],[(0,[z46,z1,z195,z3,z4,z5,z6]),(0,[z1,z2,z3,z593,z4,z5,z6]),(0,[z1,z2,z3,z4,z250,z198,z6])],[(0,[z1,z2,z3,z4,z594,z5,z6]),(0,[z73,z1,z2,z3,z43,z5,z6]),(1,[z1,z2,z3,z455,z5,z6]),(0,[z1,z147,z63,z3,z4,z5,z6]),(0,[z1,z595,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z596,z6]),(0,[z1,z2,z3,z4,z597,z5,z6]),(0,[z1,z2,z3,z4,z5,z598,z6]),(0,[z1,z2,z3,z4,z5,z599,z6])],[(0,[z600,z1,z2,z3,z4,z5,z6]),(0,[z1,z601,z2,z3,z4,z5,z6]),(1,[z103,z2,z18,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z602,z6]),(1,[z1,z2,z174,z4,z5,z6]),(0,[z1,z2,z3,z43,z4,z176,z6]),(0,[z1,z2,z3,z38,z4,z5,z95]),(0,[z1,z2,z3,z4,z603,z5,z6])],[(0,[z1,z2,z3,z4,z5,z604,z6])],[(0,[z46,z88,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z5,z268]),(0,[z46,z1,z2,z3,z4,z76,z6]),(0,[z1,z2,z3,z4,z605,z5,z6])]],
   [[(0,[z1,z2,z3,z150,z4,z5,z468]),(0,[z13,z13,z1,z2,z3,z4,z5]),(0,[z606,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z607])],[(0,[z15,z1,z239,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z608,z5,z6]),(0,[z1,z2,z3,z609,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z5,z111]),(0,[z53,z1,z2,z20,z4,z5,z6]),(0,[z1,z2,z610,z3,z4,z5,z6]),(0,[z1,z2,z3,z177,z4,z5,z6])],[(0,[z1,z2,z3,z611,z4,z5,z6]),(0,[z1,z2,z17,z61,z4,z5,z6]),(0,[z1,z113,z2,z3,z4,z5,z6]),(1,[z1,z2,z158,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z111,z47])],[(0,[z1,z612,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z198,z6]),(0,[z511,z13,z1,z2,z3,z4,z5]),(0,[z13,z1,z2,z134,z3,z4,z5]),(0,[z1,z2,z3,z4,z613,z5,z6]),(0,[z1,z31,z2,z3,z4,z5,z6]),(0,[z614,z1,z2,z3,z4,z5,z6]),(0,[z615,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z233]),(0,[z1,z2,z3,z4,z5,z616,z6]),(0,[z1,z2,z3,z25,z4,z6,z118]),(0,[z1,z2,z3,z4,z617,z5,z6])],[(1,[z73,z2,z3,z150,z5,z6]),(0,[z1,z2,z618,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z619,z6]),(0,[z13,z1,z2,z3,z4,z333,z5]),(0,[z620,z1,z2,z3,z4,z5,z6])],[(0,[z16,z1,z239,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z308]),(1,[z1,z2,z3,z218,z5,z6]),(0,[z621,z13,z1,z2,z3,z4,z5]),(1,[z459,z2,z3,z4,z5,z6]),(0,[z1,z68,z2,z54,z4,z5,z6]),(0,[z622,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z98])],[(0,[z13,z1,z2,z3,z4,z5,z250]),(0,[z1,z147,z3,z4,z148,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z623])]],
   [[(0,[z1,z2,z3,z4,z624,z5,z6]),(0,[z13,z1,z63,z2,z3,z4,z5]),(0,[z1,z2,z3,z43,z5,z153,z6]),(0,[z1,z2,z625,z3,z4,z5,z6]),(0,[z1,z2,z3,z345,z5,z66,z6])],[(1,[z1,z2,z3,z4,z5,z233]),(0,[z1,z2,z129,z3,z4,z5,z6])],[(0,[z1,z2,z626,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z627,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z628]),(0,[z1,z2,z3,z4,z5,z629,z6])],[(0,[z1,z2,z3,z4,z5,z630,z6]),(0,[z1,z2,z3,z52,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z153]),(0,[z631,z13,z1,z2,z3,z4,z5]),(0,[z13,z1,z2,z69,z3,z4,z5]),(1,[z1,z2,z313,z21,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z632]),(0,[z1,z2,z633,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z26,z66])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z18,z3,z4,z5]),(0,[z1,z2,z634,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z176,z19,z6]),(0,[z13,z1,z2,z3,z64,z4,z5]),(0,[z1,z2,z3,z4,z5,z635,z6])],[(0,[z636,z1,z2,z3,z4,z5,z6]),(0,[z537,z46,z1,z2,z3,z4,z5]),(0,[z46,z1,z2,z3,z43,z4,z5]),(0,[z1,z261,z2,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z5,z47]),(0,[z1,z2,z3,z4,z5,z71,z99]),(0,[z1,z2,z637,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z638,z6])],[(0,[z103,z86,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z91,z4,z6]),(0,[z41,z1,z2,z368,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z44,z5]),(0,[z1,z2,z3,z4,z299,z5,z6]),(0,[z1,z147,z2,z3,z4,z5,z6]),(0,[z1,z2,z313,z129,z4,z5,z6]),(0,[z1,z2,z639,z3,z4,z5,z6])]],
   [[(0,[z2,z18,z3,z61,z4,z5,z6]),(0,[z1,z2,z640,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z66]),(0,[z10,z1,z2,z3,z4,z5,z71]),(0,[z1,z2,z3,z641,z4,z5,z6]),(0,[z642,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z229,z6]),(0,[z1,z2,z3,z4,z643,z5,z6])],[(1,[z1,z2,z3,z4,z298,z5]),(0,[z13,z1,z2,z3,z25,z4,z5]),(0,[z1,z63,z2,z3,z64,z5,z6]),(0,[z1,z2,z3,z4,z5,z644,z6])],[(0,[z1,z2,z3,z4,z5,z6,z645]),(0,[z46,z1,z2,z3,z4,z5,z360]),(0,[z1,z2,z646,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z71,z6,z47]),(0,[z1,z2,z647,z3,z4,z5,z6])],[(0,[z1,z2,z18,z3,z4,z5,z6]),(0,[z1,z2,z61,z4,z5,z6,z99]),(0,[z103,z13,z1,z2,z3,z4,z5]),(0,[z46,z73,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z406,z4,z5,z6]),(0,[z1,z209,z31,z3,z4,z5,z6]),(0,[z648,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z313,z3,z4,z5,z6])],[(0,[z103,z1,z2,z61,z4,z5,z6]),(0,[z53,z1,z2,z3,z4,z5,z6]),(0,[z53,z1,z2,z3,z4,z5,z42]),(0,[z649,z1,z2,z3,z4,z5,z6]),(0,[z1,z650,z2,z3,z4,z5,z6]),(0,[z1,z2,z651,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z652,z6])],[(0,[z13,z1,z2,z3,z61,z4,z5]),(0,[z1,z2,z3,z653,z4,z5,z6])],[(0,[z53,z1,z2,z3,z4,z161,z6]),(0,[z654,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z655]),(0,[z1,z2,z3,z656,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z66,z51])]],
   [[(0,[z657,z1,z2,z3,z4,z5,z6]),(0,[z86,z1,z2,z61,z4,z5,z6]),(0,[z73,z13,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z658]),(0,[z1,z2,z3,z4,z5,z111,z71]),(1,[z1,z2,z3,z4,z6,z266])],[(0,[z621,z1,z2,z3,z4,z5,z6]),(0,[z659,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z99,z95]),(0,[z660,z1,z2,z3,z4,z5,z6])],[(0,[z551,z46,z1,z2,z3,z4,z5]),(0,[z661,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z662]),(0,[z1,z2,z3,z4,z5,z51,z111]),(0,[z1,z2,z3,z25,z4,z44,z6]),(0,[z1,z2,z3,z663,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z664,z6]),(0,[z1,z2,z3,z4,z26,z5,z118])],[(0,[z1,z11,z2,z3,z4,z5,z282]),(0,[z665,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z666,z4,z5,z6]),(0,[z667,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z668,z4,z5,z6]),(0,[z46,z1,z226,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z5,z178]),(0,[z1,z2,z134,z3,z4,z198,z6])],[(1,[z46,z1,z226,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z360,z6]),(0,[z669,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z176,z333,z6]),(0,[z1,z2,z3,z670,z4,z5,z6])],[(0,[z671,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z672,z3,z4,z5,z6]),(1,[z1,z2,z3,z196,z5,z6])],[(0,[z631,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z673]),(0,[z1,z2,z3,z674,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z39,z5,z6,z95])],[(0,[z675,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z676,z6]),(0,[z46,z41,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z677,z5,z6]),(0,[z1,z2,z3,z43,z4,z6,z118]),(0,[z1,z2,z3,z4,z5,z678,z6])],[(0,[z1,z2,z3,z4,z679,z5,z6]),(0,[z680,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z54,z4,z5,z6]),(0,[z1,z2,z3,z4,z681,z5,z6])],[(0,[z1,z139,z2,z239,z3,z4,z5]),(1,[z46,z2,z3,z4,z5,z332]),(0,[z13,z1,z2,z3,z4,z578,z5]),(0,[z110,z1,z2,z126,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z682]),(0,[z1,z2,z3,z4,z5,z683,z6])],[(0,[z1,z2,z3,z61,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z5,z71]),(0,[z1,z2,z3,z455,z4,z5,z6]),(0,[z1,z2,z3,z684,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z95])],[(0,[z13,z1,z2,z18,z3,z4,z5]),(0,[z1,z685,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z148,z5,z6]),(0,[z1,z2,z3,z4,z21,z5,z6]),(0,[z1,z686,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z164,z6]),(0,[z13,z1,z2,z3,z43,z4,z5]),(0,[z1,z2,z687,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z688,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z689])],[(0,[z1,z690,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z85,z6,z118]),(0,[z13,z1,z2,z3,z4,z44,z5]),(0,[z1,z2,z691,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z51,z47]),(0,[z1,z692,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z693,z4,z5,z6])]],
   [[(0,[z46,z1,z2,z3,z4,z26,z5]),(0,[z1,z2,z3,z4,z5,z6,z332]),(0,[z1,z31,z2,z3,z4,z333,z6]),(0,[z1,z2,z694,z3,z4,z5,z6]),(0,[z110,z1,z2,z3,z4,z5,z99])],[(1,[z1,z113,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z242,z5,z6]),(0,[z695,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z309]),(1,[z1,z2,z3,z177,z4,z118])],[(0,[z1,z2,z3,z696,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z697])],[(0,[z1,z2,z18,z4,z5,z198,z6]),(0,[z73,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z5,z360]),(1,[z1,z147,z3,z148,z5,z6]),(0,[z1,z2,z126,z4,z5,z6,z99]),(0,[z1,z2,z3,z4,z5,z698,z6])],[(0,[z1,z2,z3,z4,z699,z5,z6])],[(0,[z1,z700,z2,z3,z4,z5,z6]),(0,[z1,z2,z195,z3,z4,z5,z6]),(0,[z1,z2,z193,z3,z4,z5,z6])],[(1,[z1,z139,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z701,z5,z6]),(1,[z46,z1,z2,z158,z4,z5]),(0,[z53,z353,z2,z3,z4,z5,z6]),(0,[z1,z2,z702,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z703,z6]),(0,[z1,z2,z3,z704,z4,z5,z6]),(0,[z1,z2,z705,z3,z4,z5,z6])],[(0,[z1,z2,z706,z3,z4,z5,z6]),(0,[z88,z1,z2,z3,z150,z5,z6]),(0,[z1,z2,z3,z381,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z136,z6]),(0,[z1,z3,z64,z4,z148,z5,z6]),(0,[z1,z2,z3,z49,z4,z148,z6]),(0,[z1,z2,z3,z4,z333,z198,z6]),(0,[z1,z124,z3,z4,z5,z6,z47])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z15,z707,z3,z4,z5,z6]),(0,[z1,z2,z3,z708,z4,z5]),(0,[z1,z2,z34,z158,z4,z5]),(0,[z1,z2,z3,z4,z5,z709]),(0,[z1,z2,z3,z345,z26,z66])],[(0,[z15,z13,z239,z3,z4,z5]),(0,[z1,z2,z3,z710,z5,z6]),(0,[z1,z2,z4,z711,z198,z6])],[(0,[z16,z11,z3,z4,z5,z233]),(0,[z615,z2,z3,z39,z5,z6]),(0,[z1,z2,z640,z4,z198,z6]),(0,[z13,z1,z2,z712,z4,z5]),(0,[z1,z2,z3,z4,z5,z713])],[(0,[z86,z2,z61,z4,z87,z6]),(0,[z1,z2,z3,z196,z5,z111]),(0,[z615,z13,z2,z3,z4,z5]),(0,[z1,z2,z3,z714,z5,z6]),(0,[z1,z2,z3,z4,z5,z127]),(0,[z1,z2,z3,z4,z5,z715]),(0,[z1,z209,z3,z4,z716,z6]),(1,[z1,z3,z4,z5,z717]),(0,[z1,z2,z313,z21,z5,z6]),(0,[z1,z2,z3,z4,z26,z66])],[],[(0,[z1,z2,z3,z718,z5,z6]),(0,[z1,z2,z719,z4,z5,z6]),(0,[z46,z1,z2,z158,z196,z5])],[(0,[z1,z2,z3,z91,z4,z6]),(0,[z1,z2,z720,z4,z5,z6])],[(0,[z1,z2,z3,z425,z67,z5]),(0,[z252,z1,z2,z3,z196,z5]),(0,[z46,z1,z721,z3,z4,z5]),(0,[z46,z1,z2,z3,z299,z5]),(0,[z13,z1,z2,z3,z299,z5]),(0,[z13,z1,z63,z3,z64,z5]),(0,[z722,z459,z2,z3,z4,z5]),(0,[z1,z2,z3,z5,z309,z95])]],
   [[(0,[z46,z2,z12,z3,z4,z5]),(0,[z1,z68,z641,z4,z5,z6]),(0,[z1,z2,z3,z723,z4,z5]),(0,[z1,z2,z3,z4,z5,z724])],[(0,[z86,z2,z725,z4,z5,z6]),(0,[z1,z2,z3,z4,z298,z5]),(0,[z1,z2,z3,z4,z5,z726])],[(0,[z1,z2,z3,z4,z727,z6]),(0,[z728,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z161,z6]),(0,[z1,z2,z3,z4,z161,z42]),(0,[z1,z2,z4,z5,z729,z6])],[(0,[z11,z707,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z730]),(0,[z1,z2,z3,z158,z196,z5]),(0,[z1,z226,z75,z4,z5,z6]),(0,[z46,z2,z3,z693,z4,z5]),(0,[z46,z1,z2,z3,z5,z79]),(0,[z13,z1,z2,z3,z5,z79]),(0,[z1,z2,z3,z4,z5,z731])],[(0,[z1,z2,z3,z4,z5,z732]),(0,[z1,z226,z195,z3,z4,z5]),(0,[z46,z1,z195,z3,z4,z164]),(0,[z46,z1,z2,z3,z733,z5]),(0,[z264,z1,z2,z3,z4,z101]),(0,[z353,z2,z3,z455,z5,z6]),(0,[z1,z147,z3,z406,z148,z6])],[(0,[z1,z2,z734,z4,z5,z6]),(0,[z1,z2,z3,z4,z735,z6]),(0,[z1,z2,z3,z4,z736,z6]),(0,[z46,z1,z2,z75,z4,z5]),(0,[z1,z2,z3,z737,z5,z6]),(0,[z1,z2,z3,z4,z5,z738]),(0,[z1,z2,z3,z4,z5,z739])],[(0,[z15,z139,z239,z3,z4,z5]),(0,[z46,z40,z2,z3,z4,z19]),(0,[z46,z1,z2,z3,z740,z5]),(0,[z46,z2,z3,z653,z4,z5]),(0,[z1,z2,z3,z4,z741,z6])],[(0,[z1,z742,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z743])]],
   [[(0,[z103,z2,z135,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z744]),(0,[z46,z1,z2,z3,z745,z5]),(0,[z46,z667,z2,z3,z4,z5]),(0,[z46,z1,z2,z3,z746,z5]),(0,[z13,z2,z3,z4,z5,z200]),(0,[z1,z2,z3,z4,z5,z166]),(0,[z1,z3,z4,z5,z747,z6])],[(0,[z15,z251,z239,z3,z4,z5]),(0,[z13,z2,z3,z4,z5,z673]),(1,[z1,z3,z4,z716,z6]),(0,[z1,z2,z4,z5,z748,z6]),(0,[z1,z2,z3,z25,z749,z6])],[(0,[z1,z2,z3,z381,z6,z95]),(0,[z46,z159,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z750]),(0,[z1,z2,z3,z4,z751,z6]),(0,[z1,z2,z3,z752,z5,z6]),(0,[z1,z2,z3,z4,z5,z178]),(0,[z1,z2,z193,z406,z4,z6]),(0,[z1,z2,z3,z753,z5,z6])],[(0,[z1,z2,z754,z4,z5,z6]),(0,[z46,z1,z226,z3,z4,z5]),(0,[z13,z1,z226,z3,z4,z5]),(0,[z225,z1,z2,z3,z4,z164])],[(0,[z1,z2,z3,z4,z755,z6]),(0,[z1,z2,z3,z4,z5,z756]),(0,[z1,z195,z3,z196,z5,z6])],[(0,[z1,z757,z3,z4,z5,z6]),(0,[z1,z2,z195,z3,z196,z5])],[(0,[z2,z3,z758,z39,z5,z6]),(0,[z46,z622,z2,z3,z4,z5]),(0,[z1,z2,z325,z4,z5,z99]),(0,[z1,z2,z17,z4,z711,z6]),(0,[z1,z2,z3,z38,z5,z309])]],
   [[(0,[z1,z759,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z760]),(0,[z1,z2,z134,z4,z198,z6])],[(0,[z1,z2,z761,z4,z5,z6]),(0,[z46,z1,z2,z3,z381,z4]),(0,[z13,z1,z2,z3,z381,z4]),(0,[z1,z2,z3,z196,z76,z6])],[(0,[z46,z1,z2,z3,z218,z164]),(0,[z46,z2,z3,z4,z5,z332]),(0,[z46,z195,z3,z4,z5,z332]),(0,[z1,z2,z193,z20,z5,z6]),(0,[z1,z2,z3,z479,z4,z118]),(0,[z1,z2,z3,z38,z51,z266])],[(0,[z2,z3,z4,z19,z762,z6]),(0,[z46,z53,z1,z54,z4,z5]),(0,[z763,z1,z2,z3,z4,z5]),(0,[z1,z124,z3,z4,z5,z47])],[(0,[z1,z2,z3,z764,z5,z6]),(0,[z1,z2,z20,z765,z5,z6])],[(0,[z1,z2,z3,z4,z766,z6]),(0,[z1,z2,z3,z4,z268,z767]),(0,[z40,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z164,z6]),(0,[z1,z195,z3,z4,z164,z6]),(0,[z304,z1,z2,z3,z14,z5]),(0,[z768,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z269,z4,z118]),(0,[z1,z769,z3,z4,z5,z6]),(0,[z1,z2,z3,z345,z5,z309]),(0,[z1,z2,z3,z345,z5,z95])],[(0,[z1,z2,z3,z4,z5,z770]),(0,[z46,z2,z3,z4,z5,z324]),(0,[z1,z2,z3,z4,z771,z6]),(0,[z1,z2,z3,z50,z6,z95])],[(0,[z1,z2,z3,z4,z772,z6]),(0,[z1,z2,z3,z773,z5,z6]),(0,[z1,z2,z3,z43,z95,z118])]],
   [[(0,[z1,z2,z3,z774,z5,z6]),(0,[z1,z113,z2,z3,z4,z5]),(1,[z2,z3,z758,z5,z6]),(0,[z1,z195,z3,z4,z5,z95]),(0,[z1,z2,z3,z4,z5,z717]),(0,[z1,z2,z3,z4,z5,z775]),(0,[z1,z2,z3,z4,z5,z309]),(0,[z1,z2,z3,z177,z4,z118])],[(0,[z1,z2,z3,z4,z5,z776]),(0,[z777,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z765,z5,z6])],[(0,[z458,z1,z195,z3,z4,z5]),(0,[z1,z2,z3,z4,z778,z6]),(0,[z1,z147,z3,z148,z5,z6])],[(0,[z1,z779,z2,z3,z4,z5]),(0,[z353,z2,z3,z4,z161,z6])],[(0,[z46,z15,z239,z3,z4,z5]),(0,[z1,z2,z780,z3,z5,z6]),(0,[z41,z2,z3,z4,z762,z6]),(0,[z1,z195,z3,z4,z5,z118]),(0,[z1,z2,z3,z4,z76,z95]),(0,[z1,z2,z4,z5,z6,z781]),(0,[z1,z2,z3,z4,z5,z782])],[(0,[z1,z139,z2,z3,z4,z5]),(0,[z103,z2,z725,z4,z5,z6]),(0,[z103,z2,z18,z4,z5,z308]),(0,[z1,z2,z783,z4,z5,z6]),(0,[z46,z1,z2,z368,z4,z5]),(0,[z13,z1,z2,z368,z4,z5]),(0,[z46,z1,z2,z158,z4,z5]),(0,[z13,z1,z2,z158,z4,z5]),(0,[z46,z1,z2,z3,z4,z784]),(0,[z1,z2,z3,z4,z785,z6]),(0,[z1,z2,z134,z4,z711,z6]),(0,[z1,z2,z3,z43,z749,z6])],[(0,[z1,z2,z3,z4,z786,z6]),(0,[z1,z2,z3,z38,z242,z5]),(0,[z1,z2,z3,z787,z4,z6]),(0,[z1,z2,z788,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z789]),(0,[z1,z2,z193,z299,z5,z6]),(0,[z1,z2,z3,z4,z5,z790])]],
   [[(0,[z1,z251,z2,z3,z4,z5]),(0,[z1,z2,z3,z791,z5,z6]),(0,[z120,z2,z18,z4,z5,z6]),(0,[z1,z2,z792,z4,z5,z6]),(0,[z620,z2,z3,z150,z5,z6]),(0,[z537,z1,z2,z3,z4,z76]),(0,[z459,z2,z3,z299,z5,z6]),(0,[z1,z2,z3,z4,z711,z6])],[(0,[z1,z2,z3,z44,z463,z6]),(0,[z46,z1,z2,z3,z4,z751]),(0,[z1,z2,z3,z793,z4,z5]),(0,[z353,z2,z3,z4,z5,z166]),(0,[z1,z69,z720,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z794])],[(0,[z1,z2,z3,z4,z5,z795]),(0,[z46,z13,z2,z3,z4,z76]),(0,[z1,z2,z3,z196,z5,z66]),(0,[z1,z796,z2,z3,z4,z5]),(0,[z1,z2,z3,z43,z428,z6])],[(0,[z1,z2,z3,z4,z5,z797]),(0,[z1,z2,z3,z798,z5,z6]),(0,[z1,z195,z3,z158,z4,z5]),(0,[z1,z2,z3,z455,z136,z6]),(0,[z1,z2,z3,z799,z4,z6]),(0,[z1,z2,z129,z765,z5,z6])],[(0,[z1,z2,z3,z4,z5,z800]),(0,[z13,z1,z2,z74,z4,z5]),(0,[z1,z2,z3,z4,z5,z163]),(1,[z2,z3,z4,z762,z6]),(0,[z1,z801,z2,z3,z4,z5]),(1,[z1,z720,z4,z5,z6]),(0,[z1,z31,z3,z4,z250,z127]),(0,[z1,z2,z802,z3,z4,z5])],[(0,[z2,z3,z4,z762,z5,z6]),(0,[z186,z13,z2,z3,z4,z5]),(0,[z1,z2,z4,z176,z711,z6])],[(0,[z1,z2,z3,z4,z803,z5]),(0,[z16,z707,z3,z4,z5,z6]),(0,[z73,z2,z3,z150,z5,z468]),(0,[z123,z1,z2,z158,z4,z5]),(0,[z1,z2,z3,z4,z716,z6]),(0,[z1,z2,z3,z5,z47,z79]),(0,[z804,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z748])],[(0,[z1,z2,z3,z52,z91,z4]),(0,[z421,z13,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z740,z5,z6]),(0,[z46,z1,z2,z75,z196,z5]),(0,[z511,z1,z2,z3,z4,z578]),(0,[z1,z2,z3,z49,z4,z6]),(0,[z1,z2,z3,z765,z5,z6])],[(0,[z46,z13,z2,z3,z196,z5]),(0,[z353,z13,z2,z3,z4,z5]),(0,[z53,z1,z54,z4,z5,z6]),(0,[z53,z1,z54,z4,z5,z42]),(0,[z1,z63,z3,z805,z5,z6]),(0,[z806,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z711,z5,z6]),(0,[z1,z2,z112,z4,z198,z6]),(0,[z1,z2,z3,z4,z5,z807])],[(0,[z1,z2,z3,z4,z164,z66]),(0,[z1,z2,z3,z808,z4,z6])],[(0,[z1,z2,z3,z4,z809,z6]),(0,[z1,z2,z3,z43,z638,z6])],[(0,[z88,z1,z2,z3,z381,z6]),(0,[z1,z2,z3,z810,z4,z5]),(0,[z1,z195,z3,z4,z5,z76]),(0,[z46,z1,z2,z3,z196,z76]),(0,[z1,z68,z69,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z811]),(0,[z1,z2,z3,z4,z66,z812])],[(0,[z1,z813,z2,z3,z4,z5]),(0,[z1,z814,z2,z3,z4,z5]),(0,[z1,z2,z75,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z815]),(0,[z1,z2,z3,z396,z26,z6]),(0,[z1,z195,z75,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z816]),(0,[z1,z2,z3,z817,z4,z5]),(0,[z1,z2,z3,z177,z4,z812])],[],[(0,[z1,z2,z818,z4,z5,z6]),(0,[z1,z2,z3,z819,z5,z6]),(0,[z707,z239,z3,z4,z5,z6]),(0,[z46,z394,z2,z3,z4,z5]),(0,[z1,z2,z158,z4,z5,z47]),(0,[z13,z1,z2,z313,z21,z5]),(0,[z820,z1,z2,z3,z4,z5])]],
   [[(0,[z46,z648,z2,z3,z4,z5]),(0,[z1,z2,z3,z5,z599,z95]),(0,[z1,z2,z821,z4,z5,z6])],[(0,[z1,z2,z3,z822,z5,z6]),(0,[z1,z2,z75,z4,z5,z179]),(0,[z1,z2,z3,z4,z5,z812])],[(0,[z1,z2,z3,z4,z823,z6]),(0,[z46,z1,z2,z3,z4,z229]),(0,[z13,z1,z2,z3,z4,z229]),(0,[z88,z2,z3,z52,z39,z5]),(0,[z2,z3,z4,z758,z5,z6]),(0,[z40,z1,z2,z3,z396,z6]),(0,[z162,z13,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z6,z824])],[(0,[z2,z707,z3,z4,z5,z6]),(0,[z1,z2,z3,z825,z4,z6]),(0,[z1,z2,z3,z4,z5,z826]),(0,[z1,z2,z3,z4,z827,z6])],[(0,[z1,z2,z3,z4,z5,z828]),(0,[z46,z1,z2,z3,z829,z5]),(0,[z1,z2,z3,z4,z5,z830]),(0,[z400,z13,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z831]),(0,[z1,z2,z129,z20,z181,z6]),(0,[z1,z2,z832,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z833]),(0,[z106,z239,z3,z4,z5,z6]),(0,[z225,z1,z195,z3,z4,z5]),(0,[z551,z1,z2,z75,z4,z5]),(0,[z1,z2,z3,z4,z5,z834])],[(0,[z46,z1,z2,z3,z406,z4]),(0,[z13,z1,z2,z3,z406,z4]),(0,[z1,z2,z193,z4,z5,z835]),(0,[z1,z2,z313,z21,z5,z339])],[]],
   [[(0,[z46,z1,z2,z836,z4,z5]),(0,[z1,z195,z3,z4,z5,z99]),(0,[z13,z490,z2,z3,z4,z5]),(0,[z1,z2,z3,z837,z5,z6]),(0,[z1,z720,z54,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z838]),(1,[z1,z2,z3,z749,z6])],[(0,[z1,z2,z3,z4,z5,z839]),(0,[z46,z1,z2,z75,z4,z164]),(0,[z840,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z416,z5,z95])],[(0,[z1,z2,z3,z4,z841,z6]),(0,[z46,z353,z2,z3,z4,z5]),(0,[z842,z2,z3,z4,z5,z6]),(0,[z1,z843,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z844]),(0,[z1,z2,z4,z5,z111,z748]),(0,[z1,z2,z3,z4,z812,z118])],[(0,[z1,z2,z3,z425,z4,z76]),(0,[z46,z1,z195,z3,z218,z5])],[(0,[z1,z2,z3,z218,z76,z6]),(0,[z1,z2,z3,z805,z5,z6]),(0,[z1,z31,z3,z684,z4,z6]),(0,[z1,z2,z765,z21,z5,z6])],[(0,[z1,z2,z3,z52,z38,z5]),(0,[z13,z650,z2,z3,z4,z5]),(0,[z1,z209,z3,z4,z333,z6]),(0,[z845,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z846]),(1,[z1,z2,z158,z196,z5]),(0,[z621,z1,z2,z224,z4,z5]),(0,[z1,z2,z3,z847,z5,z6])],[(0,[z1,z2,z3,z4,z848,z6]),(0,[z41,z2,z3,z4,z298,z85]),(0,[z1,z2,z3,z145,z196,z5]),(0,[z13,z1,z2,z849,z4,z5]),(0,[z1,z2,z17,z4,z176,z6])]],
   [[(0,[z1,z2,z3,z4,z850,z6]),(0,[z1,z2,z3,z43,z217,z6]),(0,[z46,z1,z226,z3,z4,z164]),(0,[z1,z2,z3,z4,z136,z166]),(0,[z1,z851,z2,z3,z4,z5]),(0,[z1,z2,z3,z43,z683,z6])],[(0,[z1,z2,z3,z4,z5,z852]),(0,[z1,z2,z3,z4,z5,z853]),(0,[z73,z1,z2,z3,z381,z6]),(0,[z46,z2,z3,z4,z5,z616]),(0,[z53,z13,z1,z54,z4,z5]),(0,[z1,z187,z3,z4,z5,z47]),(0,[z110,z1,z2,z4,z5,z748])],[(0,[z1,z2,z3,z5,z51,z713])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z854]),(0,[z1,z855,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z42])],[(0,[z1,z2,z856,z4,z5,z6]),(0,[z2,z3,z4,z5,z360,z830])],[(0,[z1,z2,z3,z170,z91,z4]),(0,[z1,z2,z3,z4,z6,z857]),(0,[z1,z2,z3,z4,z163,z118]),(0,[z1,z2,z158,z4,z5,z71]),(0,[z1,z2,z20,z437,z5,z6]),(0,[z1,z147,z193,z148,z5,z6]),(0,[z1,z2,z3,z4,z858,z6])],[(0,[z1,z2,z74,z25,z4,z6]),(0,[z1,z2,z712,z4,z5,z6])],[(0,[z1,z2,z3,z859,z4,z6]),(0,[z1,z2,z3,z170,z4,z5]),(0,[z1,z2,z3,z4,z5,z860]),(0,[z1,z3,z4,z5,z71,z717]),(0,[z1,z2,z3,z749,z153,z6])]],
   [[(0,[z1,z2,z3,z396,z298,z5]),(0,[z13,z1,z2,z75,z4,z5]),(0,[z1,z2,z3,z4,z5,z861]),(0,[z1,z2,z3,z862,z5,z6]),(0,[z863,z1,z2,z3,z4,z5]),(0,[z1,z2,z236,z4,z5,z111])],[(0,[z695,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z864,z5,z163]),(0,[z46,z13,z2,z3,z4,z5]),(0,[z46,z489,z2,z3,z4,z5]),(0,[z13,z2,z3,z4,z5,z194]),(0,[z1,z2,z3,z4,z6,z865]),(0,[z1,z2,z3,z5,z6,z79])],[(0,[z88,z2,z3,z91,z39,z6]),(0,[z41,z2,z3,z4,z85,z6]),(0,[z13,z1,z2,z3,z4,z866]),(0,[z1,z2,z3,z4,z867,z6]),(0,[z1,z2,z868,z4,z5,z6])],[(0,[z1,z2,z3,z4,z760,z6]),(0,[z2,z725,z61,z4,z5,z6]),(0,[z40,z2,z3,z4,z19,z215]),(0,[z1,z2,z3,z196,z5,z47])],[(0,[z1,z2,z3,z4,z5,z869]),(0,[z46,z1,z2,z3,z4,z76]),(0,[z13,z1,z2,z3,z4,z76]),(0,[z46,z1,z870,z3,z4,z5]),(0,[z1,z2,z3,z871,z5,z6]),(0,[z110,z1,z2,z4,z5,z111]),(0,[z1,z2,z3,z4,z749,z6])],[(0,[z1,z532,z3,z4,z5,z47])],[(0,[z1,z2,z34,z3,z4,z5]),(0,[z41,z13,z2,z3,z4,z85]),(0,[z46,z1,z2,z3,z25,z44])],[(0,[z1,z2,z3,z4,z872,z5]),(0,[z46,z1,z2,z3,z798,z5]),(0,[z873,z1,z2,z3,z4,z5]),(0,[z1,z2,z874,z4,z5,z6]),(0,[z875,z2,z3,z4,z5,z6])]],
   [[(1,[z2,z725,z4,z5,z6]),(0,[z1,z2,z34,z4,z5,z99]),(0,[z46,z1,z2,z3,z876,z5]),(0,[z46,z1,z2,z3,z4,z35]),(0,[z13,z1,z2,z3,z877,z4]),(0,[z13,z1,z2,z3,z4,z35]),(0,[z53,z459,z54,z4,z5,z6])],[(0,[z494,z2,z61,z4,z5,z6]),(0,[z46,z1,z2,z158,z4,z164]),(0,[z46,z1,z2,z129,z20,z5]),(0,[z13,z1,z2,z129,z20,z5])],[(0,[z1,z2,z3,z4,z5,z878]),(0,[z1,z2,z3,z381,z4,z6]),(0,[z46,z1,z2,z3,z4,z879]),(0,[z417,z1,z2,z4,z5,z111]),(0,[z1,z2,z3,z880,z5,z6])],[(0,[z1,z2,z3,z4,z881,z6]),(0,[z46,z1,z2,z3,z196,z5]),(0,[z13,z1,z2,z3,z196,z5]),(0,[z882,z1,z2,z3,z4,z5]),(0,[z46,z1,z2,z3,z4,z136]),(0,[z13,z1,z2,z3,z764,z5]),(0,[z13,z1,z2,z3,z4,z136])],[(0,[z1,z2,z883,z3,z4,z5])],[(0,[z13,z2,z3,z263,z4,z5])],[(0,[z1,z707,z3,z4,z5,z6]),(0,[z1,z251,z3,z4,z5,z47]),(0,[z1,z2,z3,z4,z884,z6]),(0,[z1,z2,z3,z885,z5,z6]),(0,[z1,z2,z158,z4,z196,z5]),(0,[z10,z1,z3,z4,z5,z71])],[(0,[z1,z2,z3,z886,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z887,z6]),(0,[z1,z2,z3,z888,z4,z6]),(0,[z46,z1,z2,z889,z4,z5]),(0,[z46,z1,z890,z3,z4,z5]),(0,[z46,z557,z2,z3,z4,z5]),(0,[z1,z2,z3,z25,z6,z146])],[(0,[z1,z890,z3,z4,z5,z6]),(0,[z46,z2,z3,z4,z76,z332]),(0,[z1,z2,z3,z4,z5,z891]),(0,[z1,z2,z3,z892,z4,z5])],[(0,[z1,z2,z74,z43,z4,z6]),(0,[z1,z2,z3,z396,z198,z6]),(0,[z1,z2,z3,z218,z196,z5]),(0,[z459,z2,z3,z455,z5,z6]),(0,[z1,z2,z3,z4,z5,z893]),(0,[z1,z2,z3,z4,z5,z894])],[(0,[z1,z2,z3,z895,z4,z6]),(0,[z1,z2,z3,z896,z4,z6]),(0,[z46,z1,z2,z3,z4,z735]),(0,[z897,z1,z2,z3,z4,z5]),(0,[z1,z3,z4,z5,z898,z6]),(1,[z1,z2,z4,z711,z6])],[(0,[z353,z2,z3,z4,z5,z6]),(0,[z1,z226,z3,z4,z5,z6]),(0,[z1,z2,z899,z3,z4,z5]),(0,[z1,z2,z3,z900,z4,z6]),(0,[z1,z2,z253,z4,z198,z6]),(0,[z1,z901,z3,z4,z5,z6]),(0,[z88,z13,z2,z3,z39,z5]),(0,[z353,z2,z3,z4,z5,z42]),(0,[z582,z1,z3,z4,z5,z71]),(0,[z1,z2,z313,z765,z5,z6]),(0,[z902,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z903,z5])],[(0,[z1,z2,z3,z4,z229,z6]),(0,[z46,z1,z2,z193,z4,z5]),(0,[z46,z2,z610,z3,z4,z5]),(0,[z13,z1,z2,z193,z4,z5]),(0,[z904,z2,z3,z4,z5,z6]),(0,[z905,z2,z3,z4,z5,z6])],[(0,[z1,z2,z75,z4,z5,z111]),(0,[z620,z13,z2,z3,z4,z5]),(0,[z1,z906,z2,z3,z4,z5])],[(0,[z1,z2,z907,z4,z5,z6]),(0,[z88,z2,z3,z39,z5,z6]),(0,[z2,z3,z150,z758,z5,z6]),(0,[z46,z1,z2,z3,z4,z908]),(0,[z1,z2,z3,z4,z578,z118]),(0,[z1,z2,z343,z20,z5,z6]),(0,[z1,z2,z3,z38,z5,z51])]],
   [[(0,[z46,z16,z11,z3,z4,z5]),(0,[z1,z2,z158,z218,z5,z6])],[(0,[z1,z2,z3,z196,z5,z71]),(0,[z53,z1,z54,z4,z136,z6]),(0,[z1,z31,z3,z4,z250,z323]),(0,[z1,z2,z3,z4,z5,z909])],[(0,[z1,z2,z3,z4,z908,z6]),(0,[z110,z1,z2,z4,z5,z179]),(0,[z1,z2,z3,z4,z910,z6]),(0,[z1,z2,z3,z425,z4,z5]),(0,[z46,z1,z195,z75,z4,z5]),(1,[z1,z3,z805,z5,z6]),(0,[z1,z2,z3,z911,z4,z6]),(0,[z1,z2,z3,z4,z912,z6])],[(0,[z10,z1,z3,z4,z5,z282]),(0,[z1,z2,z3,z4,z5,z913]),(0,[z1,z914,z2,z3,z4,z5])],[(0,[z1,z2,z3,z915,z5,z6]),(0,[z46,z1,z2,z3,z49,z4]),(0,[z13,z1,z2,z3,z49,z4]),(0,[z1,z2,z916,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z917]),(0,[z1,z2,z3,z4,z6,z918])],[(0,[z1,z2,z3,z4,z5,z919]),(0,[z46,z88,z2,z3,z39,z5]),(0,[z920,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z345,z5,z51])],[(0,[z1,z2,z3,z4,z5,z921]),(0,[z1,z2,z3,z4,z5,z922]),(0,[z1,z2,z74,z4,z85,z6]),(0,[z1,z2,z3,z4,z5,z923])],[(0,[z1,z2,z3,z4,z5,z924]),(0,[z1,z3,z4,z716,z250,z6]),(0,[z1,z124,z3,z4,z5,z717])]],
   [[(0,[z1,z2,z925,z4,z5,z6]),(0,[z1,z2,z3,z864,z5,z6]),(0,[z1,z195,z3,z4,z5,z51]),(0,[z1,z926,z2,z3,z4,z5]),(0,[z1,z927,z2,z3,z4,z5]),(0,[z1,z686,z3,z4,z250,z6])],[],[(0,[z1,z2,z3,z4,z5,z928]),(0,[z929,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z930,z4,z6]),(0,[z1,z2,z313,z21,z5,z98])],[(0,[z1,z2,z3,z4,z784,z6]),(0,[z1,z2,z3,z4,z931,z6]),(0,[z1,z2,z3,z298,z67,z5]),(0,[z46,z1,z2,z856,z4,z5])],[(0,[z1,z932,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z767]),(0,[z46,z1,z2,z3,z791,z5]),(0,[z1,z31,z3,z4,z250,z6]),(0,[z1,z2,z3,z145,z5,z95])],[(0,[z1,z2,z3,z4,z933,z6]),(1,[z1,z2,z3,z196,z76]),(0,[z46,z2,z3,z4,z5,z830]),(0,[z13,z2,z3,z4,z5,z830]),(0,[z934,z2,z3,z4,z5,z6]),(0,[z1,z363,z3,z4,z5,z71]),(0,[z935,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z936,z6]),(0,[z1,z2,z937,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z938]),(0,[z1,z2,z3,z425,z4,z118]),(0,[z1,z2,z3,z299,z5,z42]),(0,[z1,z2,z3,z939,z4,z6]),(0,[z1,z2,z541,z4,z198,z6])],[(0,[z1,z2,z3,z4,z5,z940]),(0,[z46,z1,z941,z3,z4,z5])]],
   [[(0,[z1,z942,z3,z4,z5,z6]),(0,[z46,z1,z2,z75,z218,z5]),(0,[z943,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z299,z161,z6]),(0,[z944,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z25,z4,z127])],[(0,[z1,z2,z3,z4,z5,z945]),(0,[z46,z1,z2,z3,z91,z4]),(0,[z13,z1,z2,z3,z91,z4]),(0,[z1,z2,z3,z4,z5,z946])],[(0,[z73,z2,z3,z408,z5,z6]),(0,[z631,z1,z115,z3,z4,z5]),(0,[z53,z1,z720,z4,z5,z6]),(0,[z1,z318,z3,z64,z5,z6])],[(0,[z46,z1,z2,z3,z4,z5]),(0,[z13,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z947,z6]),(0,[z46,z2,z3,z4,z5,z96]),(0,[z1,z2,z948,z3,z4,z5])],[(0,[z1,z2,z75,z4,z76,z6]),(0,[z1,z2,z3,z4,z949,z6]),(0,[z1,z2,z3,z950,z5,z6])],[(0,[z1,z2,z3,z4,z5,z468]),(0,[z46,z1,z2,z937,z4,z5]),(0,[z1,z2,z3,z4,z951,z6]),(0,[z1,z2,z3,z952,z5,z6]),(0,[z2,z3,z4,z5,z6,z953])],[(0,[z432,z2,z3,z4,z85,z6]),(0,[z183,z1,z261,z3,z4,z5]),(0,[z954,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z299,z5,z166]),(0,[z1,z2,z3,z955,z5,z6]),(0,[z1,z2,z3,z25,z643,z6]),(0,[z956,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z425,z4,z26]),(0,[z46,z1,z226,z3,z218,z5])]],
   [[(0,[z1,z2,z3,z957,z5,z6]),(0,[z1,z2,z889,z4,z5,z6]),(0,[z1,z2,z158,z196,z5,z6]),(0,[z1,z2,z3,z958,z5,z6]),(0,[z1,z959,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z26,z309])],[(0,[z1,z2,z3,z960,z5,z6]),(0,[z1,z2,z3,z961,z4,z5]),(0,[z1,z2,z3,z4,z5,z215])],[(0,[z1,z2,z3,z4,z5,z962]),(0,[z46,z1,z195,z158,z4,z5]),(0,[z474,z1,z2,z3,z242,z5]),(0,[z10,z1,z115,z3,z4,z5])],[(0,[z1,z2,z3,z963,z5,z6]),(0,[z46,z1,z2,z3,z396,z5]),(0,[z13,z1,z2,z3,z396,z5]),(0,[z1,z2,z3,z396,z425,z5]),(0,[z1,z2,z3,z4,z136,z6]),(0,[z1,z2,z3,z4,z136,z42]),(0,[z1,z2,z3,z4,z5,z323])],[(0,[z1,z2,z3,z4,z5,z964]),(0,[z1,z2,z3,z4,z5,z965]),(0,[z46,z1,z2,z174,z4,z5]),(0,[z13,z1,z2,z174,z4,z5]),(0,[z1,z147,z3,z148,z5,z243])],[(0,[z1,z251,z195,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z966]),(0,[z46,z13,z2,z3,z4,z164]),(0,[z1,z124,z195,z3,z4,z5]),(0,[z46,z2,z158,z4,z5,z332]),(0,[z967,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z968,z6]),(0,[z1,z2,z3,z4,z5,z969]),(0,[z1,z2,z3,z4,z5,z970]),(0,[z1,z2,z3,z745,z5,z6]),(0,[z1,z2,z3,z971,z5,z6]),(0,[z1,z3,z64,z805,z5,z6])],[(0,[z40,z2,z3,z510,z4,z6]),(0,[z972,z2,z3,z4,z5,z6])]],
   [[(0,[z110,z1,z2,z34,z4,z5]),(0,[z1,z2,z3,z4,z5,z973]),(0,[z41,z2,z3,z452,z4,z6]),(0,[z46,z1,z974,z3,z4,z5]),(0,[z1,z2,z158,z4,z164,z6]),(0,[z1,z147,z174,z148,z5,z6]),(0,[z1,z2,z3,z4,z5,z975])],[(0,[z46,z1,z901,z3,z4,z5]),(0,[z1,z2,z3,z4,z196,z76]),(0,[z46,z2,z3,z218,z5,z332]),(0,[z976,z353,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z977]),(0,[z1,z2,z3,z4,z5,z978])],[(0,[z1,z2,z3,z4,z50,z309])],[(0,[z15,z239,z3,z4,z5,z6]),(0,[z1,z2,z3,z25,z546,z6]),(0,[z551,z1,z2,z3,z196,z5]),(0,[z1,z2,z158,z4,z5,z95]),(0,[z1,z2,z3,z4,z5,z979]),(0,[z1,z2,z3,z345,z5,z6])],[(0,[z1,z2,z3,z4,z5,z980]),(0,[z1,z2,z3,z218,z164,z6]),(0,[z1,z2,z3,z4,z5,z981]),(0,[z1,z982,z2,z3,z4,z5]),(0,[z1,z2,z3,z43,z4,z127]),(0,[z1,z2,z3,z4,z5,z330])],[(0,[z46,z1,z2,z3,z4,z848]),(0,[z46,z1,z2,z17,z4,z176]),(0,[z983,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z984,z5,z6])],[(0,[z1,z2,z985,z4,z5,z6]),(0,[z1,z195,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z455,z5]),(0,[z13,z1,z2,z3,z455,z5]),(0,[z1,z2,z4,z5,z986,z6]),(0,[z1,z2,z3,z274,z5,z51]),(0,[z1,z2,z3,z4,z50,z118])],[(0,[z46,z1,z2,z3,z196,z164]),(0,[z46,z2,z541,z3,z4,z5]),(0,[z1,z2,z3,z218,z5,z95]),(0,[z46,z2,z3,z656,z4,z5]),(0,[z1,z2,z3,z4,z987,z6])]],
   [[(0,[z16,z11,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z736]),(0,[z46,z1,z2,z158,z218,z5]),(0,[z254,z1,z2,z58,z4,z5])],[(0,[z1,z2,z3,z4,z5,z988]),(0,[z1,z2,z3,z4,z6,z812])],[(0,[z1,z2,z3,z4,z5,z179]),(0,[z1,z2,z3,z396,z5,z6]),(0,[z1,z2,z3,z4,z76,z6]),(0,[z1,z2,z3,z25,z44,z6])],[(0,[z1,z2,z3,z4,z5,z989]),(0,[z990,z2,z3,z4,z5,z6]),(0,[z1,z991,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z992,z6]),(0,[z1,z2,z3,z4,z993,z6]),(0,[z1,z2,z994,z4,z5,z6]),(0,[z1,z2,z3,z4,z26,z76]),(0,[z46,z1,z2,z3,z4,z266]),(0,[z13,z1,z2,z3,z4,z266])],[(0,[z46,z73,z2,z3,z150,z5]),(0,[z1,z2,z126,z158,z4,z5])],[(0,[z1,z2,z61,z4,z229,z6]),(0,[z86,z13,z2,z61,z4,z5]),(0,[z46,z41,z2,z3,z4,z85]),(0,[z46,z1,z2,z3,z4,z161]),(0,[z13,z1,z2,z3,z4,z161]),(0,[z1,z2,z3,z4,z995,z6]),(0,[z1,z2,z3,z4,z71,z266])],[(0,[z1,z2,z368,z4,z5,z6]),(0,[z1,z870,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z996]),(0,[z1,z147,z3,z49,z148,z6])]],
   [[(0,[z1,z2,z997,z4,z5,z6]),(0,[z998,z2,z3,z4,z5,z6]),(0,[z1,z2,z999,z4,z5,z6]),(0,[z1,z1000,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1001]),(0,[z1,z2,z3,z876,z5,z6]),(0,[z41,z2,z3,z396,z85,z6]),(0,[z46,z365,z2,z3,z4,z5]),(0,[z46,z1,z1002,z3,z4,z5]),(0,[z1,z1003,z2,z3,z4,z5]),(0,[z46,z1,z2,z3,z345,z5]),(0,[z13,z1,z2,z3,z25,z44]),(0,[z13,z1,z2,z3,z345,z5]),(0,[z1,z31,z3,z4,z716,z6]),(0,[z1,z2,z3,z145,z5,z713]),(0,[z1,z2,z3,z4,z26,z812])],[(0,[z46,z1,z2,z3,z4,z881]),(0,[z1,z2,z3,z406,z4,z838]),(0,[z1,z2,z4,z5,z1004,z6]),(0,[z1,z3,z4,z5,z717,z6]),(1,[z1,z2,z3,z4,z812])],[(0,[z88,z2,z3,z170,z39,z5]),(0,[z1,z2,z3,z4,z6,z1005]),(0,[z1,z2,z117,z4,z198,z6]),(0,[z1,z2,z3,z4,z1006,z6])],[(0,[z46,z1,z2,z1007,z4,z5]),(0,[z353,z2,z3,z4,z136,z6]),(0,[z10,z1,z3,z4,z5,z717]),(0,[z1,z2,z1008,z3,z4,z5])],[(0,[z41,z2,z74,z4,z85,z6]),(0,[z1,z2,z195,z158,z4,z5]),(0,[z13,z1,z2,z3,z787,z4]),(0,[z1,z209,z3,z284,z4,z6]),(0,[z1,z2,z3,z4,z181,z6])],[(0,[z86,z113,z2,z61,z4,z5]),(0,[z162,z2,z61,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1009]),(0,[z41,z2,z368,z4,z85,z6]),(0,[z46,z1,z2,z994,z4,z5]),(0,[z1,z2,z3,z1010,z4,z5]),(0,[z1,z2,z193,z49,z4,z6]),(0,[z1,z2,z3,z1011,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1012]),(0,[z1,z2,z3,z396,z176,z6]),(0,[z46,z1,z209,z3,z4,z333]),(0,[z13,z1,z209,z3,z4,z333]),(0,[z53,z1,z54,z299,z5,z6]),(0,[z53,z1,z128,z4,z5,z6]),(0,[z1013,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z43,z276,z6])]],
   [[(0,[z1,z2,z3,z4,z35,z6]),(0,[z1,z1014,z2,z3,z4,z5]),(0,[z1,z2,z349,z4,z5,z99])],[(0,[z46,z2,z3,z196,z5,z332])],[(0,[z46,z459,z2,z3,z4,z5]),(0,[z1,z226,z3,z4,z5,z47]),(0,[z13,z459,z2,z3,z4,z5]),(0,[z1,z2,z3,z44,z6,z60])],[(0,[z16,z13,z11,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1015]),(0,[z1,z2,z3,z4,z866,z6]),(0,[z1,z1002,z3,z4,z5,z6]),(0,[z1,z195,z3,z4,z5,z66]),(0,[z1016,z1,z2,z3,z4,z5]),(0,[z1,z3,z4,z333,z716,z6])],[(0,[z1,z2,z3,z67,z5,z6]),(0,[z1,z2,z849,z4,z5,z6]),(0,[z1,z2,z75,z218,z5,z6]),(0,[z1,z2,z3,z196,z164,z6]),(0,[z1,z2,z3,z4,z5,z1017])],[(0,[z46,z1,z2,z3,z4,z181]),(0,[z1,z2,z20,z299,z5,z6]),(0,[z1,z2,z3,z406,z4,z6]),(0,[z1,z1018,z2,z3,z4,z5])],[(0,[z1,z2,z706,z4,z198,z6]),(0,[z88,z2,z3,z381,z39,z6]),(0,[z1,z2,z3,z758,z5,z6]),(0,[z46,z1,z226,z75,z4,z5]),(0,[z46,z1,z1019,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1020]),(0,[z1,z68,z720,z4,z5,z6]),(0,[z1,z2,z3,z1021,z4,z5])],[(0,[z1,z2,z3,z4,z87,z6]),(0,[z86,z2,z61,z4,z5,z6]),(0,[z1,z2,z3,z381,z52,z4]),(0,[z73,z2,z3,z150,z5,z268]),(0,[z1,z147,z3,z148,z5,z178])]],
   [[(0,[z1,z2,z3,z1022,z5,z6]),(0,[z1,z2,z3,z218,z5,z268]),(0,[z41,z2,z3,z425,z4,z85]),(0,[z1,z2,z3,z4,z5,z1023])],[(0,[z40,z13,z2,z3,z4,z19]),(0,[z46,z2,z3,z4,z164,z332]),(0,[z1024,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z47,z266]),(0,[z1,z2,z3,z4,z5,z1025])],[(0,[z1,z2,z3,z4,z1026,z5]),(0,[z1,z2,z3,z4,z5,z1027]),(0,[z46,z1,z2,z3,z774,z5]),(0,[z1,z2,z1028,z3,z4,z5]),(0,[z1,z2,z126,z4,z5,z99]),(0,[z1,z2,z3,z5,z749,z6]),(0,[z1,z2,z3,z44,z749,z6])],[(0,[z41,z2,z3,z67,z85,z6]),(0,[z1,z226,z3,z4,z76,z6]),(0,[z1,z2,z3,z196,z5,z118]),(0,[z1029,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z282]),(0,[z1,z2,z3,z4,z1030,z6]),(0,[z1,z2,z3,z4,z5,z1031]),(0,[z537,z1,z195,z3,z4,z5]),(0,[z46,z1,z2,z3,z4,z910]),(0,[z1,z2,z3,z1032,z4,z5]),(1,[z1,z2,z4,z5,z748]),(0,[z1,z2,z3,z38,z50,z6])],[(0,[z46,z1,z1033,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z243]),(0,[z1,z2,z1034,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1035,z6]),(0,[z16,z11,z3,z4,z5,z282]),(0,[z88,z2,z3,z452,z5,z6]),(0,[z46,z13,z195,z3,z4,z5]),(0,[z1,z2,z3,z4,z26,z101]),(1,[z1,z2,z765,z5,z6])],[(0,[z1,z2,z3,z1036,z4,z5]),(0,[z46,z1,z2,z3,z4,z164]),(0,[z13,z1,z2,z3,z4,z164])]],
   [[(0,[z46,z1,z942,z3,z4,z5]),(0,[z1037,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1038])],[(0,[z103,z2,z18,z4,z5,z6]),(0,[z1,z2,z3,z381,z38,z6]),(0,[z46,z1,z195,z3,z4,z76]),(0,[z1039,z1,z2,z3,z4,z5]),(0,[z1,z1040,z2,z3,z4,z5]),(0,[z1,z2,z3,z670,z5,z95])],[(0,[z46,z103,z2,z18,z4,z5]),(0,[z40,z2,z3,z4,z762,z6]),(0,[z46,z1,z2,z134,z4,z198]),(0,[z10,z1,z195,z3,z4,z5]),(0,[z13,z1,z2,z134,z4,z198]),(0,[z1,z2,z3,z455,z161,z6])],[(0,[z88,z2,z3,z758,z5,z6]),(0,[z1,z2,z3,z4,z164,z118]),(0,[z642,z13,z2,z3,z4,z5]),(0,[z1,z2,z3,z877,z4,z6]),(0,[z1,z2,z3,z43,z153,z309])],[(0,[z1,z2,z1041,z4,z5,z6]),(0,[z1,z2,z1042,z4,z5,z6]),(0,[z1,z1043,z2,z3,z4,z5]),(0,[z1,z2,z3,z5,z713,z95])],[(0,[z1044,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z309,z118]),(0,[z1,z2,z3,z4,z50,z6])],[(0,[z496,z2,z61,z4,z5,z6]),(1,[z2,z3,z4,z5,z830]),(0,[z432,z13,z2,z3,z4,z5]),(0,[z1,z1045,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1046,z5])],[(0,[z1,z2,z3,z5,z6,z1047]),(0,[z1,z2,z3,z4,z76,z51]),(0,[z13,z2,z3,z4,z460,z5]),(0,[z1,z1048,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1049,z6])]],
   [[(0,[z642,z2,z3,z4,z19,z6]),(0,[z46,z1,z195,z3,z196,z5]),(0,[z1,z226,z3,z4,z5,z71]),(0,[z1,z2,z58,z4,z5,z99]),(0,[z1,z2,z3,z455,z5,z166])],[(0,[z1,z2,z3,z4,z1050,z6]),(0,[z1,z721,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z830,z332]),(0,[z1,z2,z3,z299,z5,z6]),(0,[z1,z2,z193,z4,z5,z6])],[(0,[z1,z2,z3,z5,z268,z95]),(0,[z537,z1,z2,z3,z218,z5]),(0,[z1,z2,z3,z14,z5,z95]),(0,[z459,z2,z3,z4,z5,z42]),(0,[z1,z2,z3,z1051,z4,z6])],[(0,[z1,z2,z3,z4,z5,z1052]),(0,[z1,z2,z3,z196,z5,z76]),(0,[z46,z1,z2,z3,z4,z50]),(0,[z13,z1,z2,z3,z4,z50])],[(0,[z1,z2,z1053,z3,z4,z6]),(0,[z1,z2,z3,z1054,z4,z5]),(0,[z46,z13,z2,z3,z218,z5]),(0,[z46,z465,z2,z3,z4,z5]),(0,[z1,z2,z75,z196,z5,z6]),(0,[z459,z2,z3,z4,z161,z6]),(0,[z1,z2,z3,z345,z6,z118])],[(0,[z1,z2,z3,z4,z5,z233]),(0,[z1,z2,z1055,z4,z5,z6]),(0,[z1,z2,z1056,z4,z5,z6]),(0,[z252,z1,z2,z3,z4,z76])],[(0,[z1,z2,z3,z1057,z5,z6]),(0,[z46,z1,z226,z158,z4,z5]),(0,[z1,z2,z3,z1058,z5,z6]),(0,[z1,z2,z32,z4,z176,z6])],[(0,[z1,z2,z3,z4,z5,z308]),(0,[z46,z1,z2,z761,z4,z5]),(0,[z46,z1,z2,z3,z218,z76]),(0,[z1,z195,z3,z4,z5,z111]),(0,[z110,z1,z2,z224,z4,z5]),(0,[z1,z2,z3,z5,z6,z1059]),(0,[z1060,z1,z2,z3,z4,z5])]],
   [[(0,[z252,z1,z226,z3,z4,z5]),(0,[z157,z1,z2,z3,z196,z5]),(0,[z225,z1,z2,z3,z196,z5]),(0,[z110,z1,z2,z158,z4,z5])],[(0,[z1,z2,z3,z4,z1061,z6]),(0,[z86,z2,z61,z4,z229,z6]),(0,[z46,z2,z75,z4,z5,z332]),(0,[z2,z3,z4,z5,z6,z830]),(0,[z1062,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1063])],[(0,[z1,z2,z3,z1064,z5,z6]),(0,[z1,z2,z3,z4,z5,z1065]),(0,[z2,z3,z4,z762,z85,z6]),(0,[z976,z1,z2,z3,z4,z5]),(0,[z459,z2,z3,z4,z5,z166]),(0,[z1,z1066,z2,z3,z4,z5]),(0,[z1,z2,z3,z1067,z4,z5])],[(0,[z1,z2,z3,z396,z6,z118]),(1,[z1,z195,z158,z4,z5]),(0,[z46,z1,z855,z3,z4,z5]),(0,[z1,z2,z3,z4,z164,z76]),(0,[z1,z2,z4,z5,z748,z99])],[(0,[z421,z2,z18,z4,z5,z6]),(0,[z1,z2,z836,z4,z5,z6]),(0,[z46,z1,z63,z3,z64,z5]),(0,[z1,z2,z75,z4,z164,z6]),(0,[z1,z2,z3,z1068,z5,z6]),(0,[z1,z2,z3,z4,z5,z1069])],[(0,[z1,z226,z3,z4,z5,z282]),(0,[z551,z1,z195,z3,z4,z5]),(0,[z46,z2,z3,z4,z5,z105]),(0,[z1,z3,z805,z148,z5,z6])],[(0,[z1,z2,z3,z1070,z5,z6]),(0,[z46,z1,z2,z3,z1071,z5]),(0,[z46,z1,z2,z3,z915,z5]),(0,[z1,z2,z3,z4,z1072,z6])],[(0,[z1,z2,z18,z4,z229,z6]),(0,[z1,z2,z3,z196,z5,z99]),(0,[z1,z2,z3,z4,z5,z1073])]],
   [[(0,[z73,z2,z3,z758,z5,z6])],[(0,[z16,z369,z3,z4,z5,z6]),(0,[z1,z2,z3,z381,z170,z4]),(0,[z46,z1,z2,z907,z4,z5]),(0,[z1,z2,z3,z4,z5,z339])],[(0,[z46,z1,z2,z3,z819,z5]),(0,[z1,z2,z3,z4,z50,z66])],[(0,[z1,z2,z3,z4,z5,z1074])],[(0,[z1,z2,z3,z4,z1075,z6]),(0,[z1,z2,z195,z3,z4,z76]),(0,[z1,z3,z720,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z266])],[(0,[z1,z2,z3,z5,z163,z1076]),(0,[z1,z2,z3,z4,z1077,z6])],[(0,[z1,z2,z1078,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1079]),(0,[z1,z2,z4,z5,z179,z99]),(0,[z1,z2,z3,z52,z196,z5]),(0,[z1,z2,z3,z4,z1080,z6]),(0,[z1,z2,z3,z4,z5,z1081])],[(0,[z1,z2,z1082,z3,z4,z6]),(0,[z1,z2,z4,z1083,z5,z6]),(0,[z1,z2,z3,z4,z26,z163]),(0,[z46,z1,z2,z3,z4,z755]),(0,[z1,z226,z158,z4,z5,z6]),(0,[z1,z2,z3,z4,z161,z166]),(0,[z1,z2,z3,z4,z5,z1084]),(0,[z1,z2,z3,z4,z5,z1085]),(0,[z1086,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z76,z47]),(0,[z13,z1,z2,z17,z4,z176]),(0,[z1,z2,z193,z4,z5,z894]),(0,[z1,z2,z3,z4,z5,z835]),(0,[z1,z1087,z3,z4,z5,z6])],[(0,[z252,z1,z2,z158,z4,z5]),(0,[z13,z1,z2,z3,z4,z1088]),(0,[z728,z353,z2,z3,z4,z5]),(0,[z1,z2,z3,z38,z50,z51])],[(0,[z1,z2,z3,z4,z1089,z6]),(0,[z1,z2,z3,z196,z5,z6]),(0,[z1,z2,z3,z4,z5,z1090]),(0,[z1,z2,z75,z158,z4,z5]),(0,[z13,z2,z3,z4,z5,z682]),(0,[z353,z2,z3,z299,z5,z6])],[(0,[z46,z395,z2,z3,z4,z5]),(0,[z1,z2,z1091,z3,z4,z5]),(0,[z1,z226,z3,z218,z5,z6]),(0,[z1,z2,z3,z4,z5,z1092])],[(0,[z1,z2,z3,z4,z5,z1093]),(0,[z86,z2,z34,z61,z4,z5])],[(0,[z46,z1,z2,z3,z67,z5]),(0,[z13,z1,z2,z3,z67,z5]),(0,[z1,z2,z3,z4,z5,z1094]),(0,[z1,z2,z3,z746,z5,z6]),(0,[z46,z1,z31,z3,z4,z250]),(0,[z1,z195,z3,z4,z76,z6]),(0,[z13,z1,z31,z3,z4,z250]),(0,[z1,z2,z3,z4,z5,z1095]),(0,[z1096,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1097,z6])],[(0,[z1,z2,z3,z1098,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1099]),(0,[z1,z2,z3,z1100,z5,z6]),(0,[z1,z2,z3,z4,z5,z1101]),(0,[z1,z2,z3,z4,z5,z1102]),(0,[z496,z2,z3,z4,z85,z6])]],
   [[(1,[z707,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z282,z47]),(0,[z46,z1,z195,z3,z4,z5]),(0,[z13,z1,z195,z3,z4,z5]),(0,[z1,z3,z4,z5,z717,z47]),(0,[z1,z2,z3,z5,z71,z79])],[(0,[z1,z2,z3,z1103,z5,z6]),(0,[z1,z2,z74,z4,z5,z6]),(0,[z53,z1,z54,z455,z5,z6]),(0,[z1,z2,z3,z4,z1104,z6]),(0,[z1,z2,z3,z4,z531,z66]),(0,[z1,z2,z3,z4,z6,z1105])],[(0,[z1,z2,z3,z1071,z5,z6]),(0,[z1,z2,z3,z5,z6,z1106]),(0,[z1,z2,z3,z4,z6,z1107]),(0,[z1,z147,z3,z805,z5,z6])],[(0,[z46,z1,z147,z3,z148,z5]),(0,[z1,z2,z158,z4,z5,z51]),(0,[z13,z1,z147,z3,z148,z5]),(0,[z1108,z1,z2,z3,z4,z5]),(0,[z1,z2,z126,z4,z5,z748])],[(0,[z1,z2,z3,z43,z153,z330])],[(0,[z1,z2,z1109,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z1110]),(0,[z1,z2,z1111,z3,z4,z5]),(0,[z1,z2,z3,z4,z415,z118])],[(0,[z1,z2,z725,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1112]),(0,[z1,z2,z3,z4,z879,z6]),(0,[z1,z2,z1113,z4,z5,z6]),(0,[z1,z2,z406,z174,z4,z6]),(0,[z1,z2,z3,z43,z153,z6])],[(0,[z1,z2,z1114,z4,z5,z6]),(0,[z1,z2,z3,z4,z1115,z6]),(0,[z1,z1033,z3,z4,z5,z6]),(0,[z2,z725,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1116]),(0,[z13,z2,z3,z4,z5,z360]),(0,[z1,z2,z3,z218,z5,z51]),(0,[z1,z2,z3,z4,z5,z1117])]],
   [[(0,[z10,z1,z251,z3,z4,z5]),(0,[z1,z2,z3,z1118,z4,z5]),(0,[z46,z1,z2,z1078,z4,z5]),(0,[z46,z1,z2,z3,z4,z931]),(0,[z722,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1119]),(0,[z1,z2,z3,z4,z5,z1120]),(0,[z1,z2,z3,z4,z5,z1121])],[(0,[z1,z2,z3,z1122,z5,z6]),(0,[z1,z2,z3,z43,z6,z453])],[(0,[z1,z2,z3,z97,z5,z51]),(0,[z1,z2,z3,z4,z1123,z6])],[(0,[z1,z2,z3,z1124,z4,z6]),(0,[z258,z1,z2,z3,z43,z6]),(0,[z46,z13,z2,z75,z4,z5])],[(0,[z400,z11,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1125,z6]),(0,[z1,z285,z3,z4,z5,z71]),(0,[z1,z2,z3,z25,z28,z6])],[(0,[z1,z2,z3,z4,z1088,z6]),(0,[z2,z18,z725,z4,z5,z6]),(0,[z1,z2,z3,z4,z1126,z5]),(0,[z476,z1,z2,z3,z4,z76]),(0,[z1,z261,z3,z4,z5,z47])],[(0,[z1,z2,z3,z733,z5,z6]),(0,[z46,z1,z2,z3,z4,z87]),(0,[z13,z1,z2,z3,z4,z87]),(0,[z1,z2,z3,z43,z462,z6]),(0,[z1,z2,z3,z4,z5,z1127]),(0,[z46,z1,z2,z3,z218,z5]),(0,[z13,z1,z2,z3,z218,z5]),(0,[z46,z1,z2,z75,z4,z76]),(0,[z1,z2,z3,z4,z76,z71]),(0,[z1,z2,z3,z4,z5,z1128])],[(0,[z1,z3,z4,z5,z1129,z6]),(0,[z1,z2,z3,z4,z5,z1130]),(0,[z1,z2,z75,z4,z5,z99]),(0,[z1,z2,z3,z4,z5,z1131]),(0,[z1,z3,z4,z5,z1132,z6])]],
   [[(0,[z1,z2,z3,z1133,z4,z5]),(0,[z1,z2,z3,z4,z5,z1134]),(0,[z1,z2,z1007,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z181])],[(0,[z46,z1,z2,z74,z4,z5]),(0,[z1,z2,z1135,z4,z5,z6])],[(0,[z46,z13,z226,z3,z4,z5]),(0,[z46,z1,z2,z1136,z4,z5]),(0,[z46,z1,z2,z1137,z4,z5]),(0,[z1,z2,z3,z38,z196,z5]),(0,[z1,z2,z49,z174,z4,z6]),(0,[z1,z2,z129,z20,z5,z6]),(0,[z1,z2,z3,z4,z1138,z6])],[(0,[z1,z1139,z3,z4,z5,z6]),(0,[z1,z2,z17,z4,z627,z6]),(0,[z1,z2,z3,z4,z5,z1140]),(0,[z1,z226,z3,z196,z5,z6]),(0,[z1,z2,z1141,z3,z4,z5]),(0,[z1,z2,z3,z345,z26,z6])],[(0,[z1,z2,z1137,z4,z5,z6]),(0,[z46,z1,z2,z997,z4,z5]),(0,[z1,z536,z3,z4,z333,z6]),(0,[z1,z2,z3,z142,z5,z95])],[(0,[z1,z2,z3,z38,z5,z268]),(0,[z46,z1,z226,z3,z4,z76]),(0,[z1,z2,z3,z177,z4,z76]),(0,[z1,z2,z313,z299,z5,z6]),(0,[z1,z2,z3,z4,z1142,z6])],[(0,[z1,z2,z3,z52,z4,z5]),(0,[z1,z2,z74,z4,z19,z6]),(0,[z1,z2,z3,z1143,z5,z6]),(1,[z1,z2,z3,z5,z713])],[(0,[z41,z1,z2,z3,z396,z6]),(0,[z967,z459,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z1144,z6]),(0,[z46,z78,z2,z3,z4,z5]),(0,[z46,z226,z3,z4,z5,z332]),(0,[z53,z1,z54,z4,z161,z6]),(0,[z1,z2,z1145,z3,z4,z5]),(0,[z1,z63,z3,z64,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1146]),(0,[z1,z2,z3,z299,z136,z6]),(0,[z1147,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z5,z6,z1148])],[(0,[z1,z2,z3,z829,z5,z6]),(1,[z1,z195,z3,z4,z76]),(0,[z459,z2,z3,z4,z136,z6]),(0,[z1,z245,z3,z4,z5,z47])],[(0,[z1,z2,z3,z1149,z4,z6]),(0,[z1,z941,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z850,z268]),(0,[z1,z195,z3,z4,z196,z5]),(0,[z1,z226,z3,z4,z164,z6]),(0,[z1,z2,z3,z455,z5,z6]),(0,[z1,z2,z3,z455,z5,z42]),(0,[z1,z2,z3,z5,z6,z713])],[(0,[z46,z1,z226,z3,z196,z5]),(0,[z46,z1,z2,z313,z21,z5]),(0,[z1,z2,z174,z4,z5,z6]),(0,[z1,z3,z4,z716,z5,z6]),(0,[z1,z2,z3,z4,z1150,z6])],[(0,[z1,z2,z3,z4,z5,z1151]),(0,[z1,z2,z3,z4,z762,z6]),(0,[z1,z2,z3,z1152,z4,z6]),(0,[z1,z1153,z2,z3,z4,z5]),(0,[z159,z1,z2,z3,z43,z6])],[(0,[z1,z2,z3,z4,z5,z268]),(0,[z1,z974,z3,z4,z5,z6]),(0,[z53,z1,z54,z4,z5,z166])],[(0,[z1,z2,z1154,z3,z5,z6]),(0,[z1,z2,z3,z1155,z4,z5]),(0,[z46,z2,z3,z4,z449,z5])]],
   [[(0,[z103,z2,z18,z4,z5,z179]),(0,[z1,z2,z1136,z4,z5,z6]),(0,[z46,z1,z759,z3,z4,z5]),(0,[z53,z353,z54,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1156]),(0,[z1,z2,z3,z4,z5,z1157]),(0,[z1,z265,z3,z148,z5,z6])],[(0,[z1,z2,z158,z4,z5,z6]),(0,[z73,z13,z2,z3,z150,z5]),(1,[z1,z195,z3,z196,z5]),(0,[z537,z1,z2,z158,z4,z5]),(0,[z46,z27,z2,z3,z4,z5]),(0,[z1,z195,z158,z4,z5,z6]),(0,[z13,z1,z2,z3,z1068,z5]),(0,[z1,z2,z3,z4,z1158,z5]),(0,[z1,z2,z3,z38,z5,z713])],[(0,[z1,z1019,z3,z4,z5,z6]),(0,[z1,z2,z193,z21,z5,z6]),(0,[z1,z2,z248,z4,z176,z6])],[(0,[z1,z2,z3,z1159,z4,z6]),(0,[z1,z1160,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1161]),(0,[z1,z2,z3,z52,z5,z95]),(0,[z1,z2,z391,z4,z176,z6]),(0,[z46,z13,z2,z158,z4,z5]),(0,[z46,z2,z3,z4,z5,z698]),(0,[z1,z3,z4,z805,z5,z6]),(0,[z1,z2,z3,z26,z66,z79])],[(0,[z1,z2,z3,z1162,z5,z6]),(0,[z1,z2,z3,z1163,z4,z5]),(0,[z73,z2,z3,z150,z5,z6]),(0,[z1,z1164,z3,z4,z5,z6]),(0,[z1,z2,z1165,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z1076]),(0,[z1,z2,z129,z20,z35,z6]),(0,[z1,z2,z3,z43,z664,z6])],[(0,[z459,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z218,z5,z6]),(0,[z46,z1,z2,z3,z43,z153]),(0,[z1,z195,z3,z218,z5,z6]),(0,[z1,z2,z158,z4,z76,z6]),(0,[z13,z1,z2,z3,z43,z153]),(0,[z1,z2,z3,z4,z5,z98])],[(0,[z186,z239,z3,z4,z5,z6]),(0,[z46,z86,z2,z61,z4,z5]),(0,[z40,z2,z3,z4,z19,z163]),(0,[z1,z2,z3,z4,z164,z163]),(0,[z46,z1,z2,z158,z4,z76]),(0,[z46,z1,z68,z69,z4,z5]),(0,[z13,z1,z68,z69,z4,z5]),(0,[z1,z2,z3,z1166,z5,z6]),(0,[z1,z1167,z2,z3,z4,z5]),(0,[z1,z2,z3,z406,z4,z1017])],[(0,[z1,z3,z4,z1168,z5,z6]),(0,[z1,z2,z3,z4,z5,z1169]),(0,[z1,z2,z3,z4,z5,z1170]),(0,[z1,z2,z3,z4,z5,z1171])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 523) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 523).take 528) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1051).take 169) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1220)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [523, 528, 169] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 101).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 101).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 204).take 52).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [101, 103, 52] = true :=
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

end PEqualNP.Outside.L_meta_40237

theorem PEqualNP.Outside.L_meta_40237 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4274579648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4274579648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40237.solve