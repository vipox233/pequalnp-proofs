import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40319

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
  Nat.testBit (4276808936 * 2 ^ 32 + 4274580672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x1022660dc0e33cc4#64 ++ 0x21022660dc0e33cc#64 ++ 0xf067ee1fc1e77cc7#64 ++ 0xdf067ee1fc1e77cc#64 : BitVec 256),
   (0x008900a2820d0558#64 ++ 0x4008900a2820d055#64 ++ 0x719913e3863f8fff#64 ++ 0xb719913e3863f8ff#64 : BitVec 256),
   (0x061618545830d0a2#64 ++ 0x8061618545830d0a#64 ++ 0xde1e1c7c7838f0ff#64 ++ 0x7de1e1c7c7838f0f#64 : BitVec 256),
   (0x0b601f002d40ea03#64 ++ 0x00b601f002d40ea0#64 ++ 0xbfe01f807fc0ff0e#64 ++ 0xfbfe01f807fc0ff0#64 : BitVec 256),
   (0x2ddfa00077be000c#64 ++ 0x02ddfa00077be000#64 ++ 0xafffe0007fff000d#64 ++ 0xfafffe0007fff000#64 : BitVec 256),
   (0x4ffddffb00000000#64 ++ 0x04ffddffb0000000#64 ++ 0x4fffffff80000003#64 ++ 0xf4fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [11, 10]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x719913e3863f8fff 0xb719913e3863f8ff

def z1 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xde1e1c7c7838f0ff 0x7de1e1c7c7838f0f

def z2 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xbfe01f807fc0ff0e 0xfbfe01f807fc0ff0

def z3 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf067ee1fc1e77cc7 0xdf067ee1fc1e77cc

def z4 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xafffe0007fff000d 0xfafffe0007fff000

def z5 : W := mkw 0x4ffddffb020c0118 0x44ffddffb020c011 0x4fffffff8618833b 0xf4fffffff8618833

def z6 : W := mkw 0x42a95ffb00000000 0x042a95ffb0000000 0x41991fff80000003 0xb41991fff8000000

def z7 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4fffffff80000003 0xf4fffffff8000000

def z8 : W := mkw 0x29c9a000278e000c 0x029c9a000278e000 0xafe1e0007fc7000c 0xfafe1e0007fc7000

def z9 : W := mkw 0x0020070000402a01 0x00020070000402a0 0x0000038000000f00 0x00000038000000f0

def z10 : W := mkw 0x4ffddffb1810c022 0x84ffddffb1810c02 0x4fffffffb818803b 0xf4fffffffb818803

def z11 : W := mkw 0x06361e545870f8a2 0x806361e545870f8a 0xfe7e1e7c79f8fcff 0xffe7e1e7c79f8fcf

def z12 : W := mkw 0x000000002d40ea03 0x0000000002d40ea0 0xb00000007fc0ff0c 0x0b00000007fc0ff0

def z13 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0xb000000041e77cc4 0x0b000000041e77cc

def z14 : W := mkw 0x0416000050300000 0x0041600005030000 0x8e06000078000000 0x48e0600007800000

def z15 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0x8e060c1c78007000 0x48e060c1c7800700

def z16 : W := mkw 0x0f761f547d70faa3 0x80f761f547d70faa 0xfffe1ffc7ff8ffff 0xffffe1ffc7ff8fff

def z17 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0x31e01f8007c0ff02 0x831e01f8007c0ff0

def z18 : W := mkw 0x0bc919a2af0dc75b 0x40bc919a2af0dc75 0x7f9913e3be3f8fff 0xb7f9913e3be3f8ff

def z19 : W := mkw 0x0000000000000000 0x0000000000000000 0x3180138006008f0e 0xb3180138006008f0

def z20 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xff9e1ffc7e38ffff 0xfff9e1ffc7e38fff

def z21 : W := mkw 0x0f761f547d70faa3 0x80f761f547d70faa 0x8e660c1c79c07000 0x48e660c1c79c0700

def z22 : W := mkw 0x1020660980c32c44 0x21020660980c32c4 0x2061e20381c70c00 0x82061e20381c70c0

def z23 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x401fe07f80000001 0x0401fe07f8000000

def z24 : W := mkw 0x0f761f547d70faa3 0x80f761f547d70faa 0xde7e1c7c79f8f0ff 0x7de7e1c7c79f8f0f

def z25 : W := mkw 0x2ddda000278e000c 0x02ddda000278e000 0x2fffe00007c70001 0xf2fffe00007c7000

def z26 : W := mkw 0x1002600dc0a314c4 0x21002600dc0a314c 0xe067e01fc1e700c5 0xde067e01fc1e700c

def z27 : W := mkw 0x4dddc0fb00000000 0x04dddc0fb0000000 0x4fffe07f80000001 0xf4fffe07f8000000

def z28 : W := mkw 0x008900a200000000 0x0008900a20000000 0x719913e386008f0f 0xb719913e386008f0

def z29 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z30 : W := mkw 0x00000000820d0558 0x400000000820d055 0x00000000003f00f0 0x000000000003f00f

def z31 : W := mkw 0x0020460900000000 0x0002046090000000 0x4067ee1f80000003 0xd4067ee1f8000000

def z32 : W := mkw 0x2dffe60977be000c 0x02dffe60977be000 0xefffee1fffff000f 0xfefffee1fffff000

def z33 : W := mkw 0x061418501810c022 0x8061418501810c02 0x0e00000038000000 0x00e0000003800000

def z34 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xce1e0c7c783870f1 0x4ce1e0c7c783870f

def z35 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x0ffefdfc00000000 0x60ffefdfc0000000

def z36 : W := mkw 0x008900a2020c0118 0x4008900a2020c011 0x019811e006188338 0x2019811e00618833

def z37 : W := mkw 0x5f76ff5dc0e33cc4 0x25f76ff5dc0e33cc 0xfe67ee1fc1e77cc7 0xdfe67ee1fc1e77cc

def z38 : W := mkw 0x4dfdc7fb00000000 0x04dfdc7fb0000000 0x41ffe3ff80000001 0x841ffe3ff8000000

def z39 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x219913e3861f8f38 0xa219913e3861f8f3

def z40 : W := mkw 0x061418501810c022 0x8061418501810c02 0x0e18106038188038 0x20e1810603818803

def z41 : W := mkw 0x0020460900000000 0x0002046090000000 0x40000e1f80000002 0x040000e1f8000000

def z42 : W := mkw 0x0416000050300000 0x0041600005030000 0x8e1e00007838000d 0x78e1e00007838000

def z43 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x519813e386188ffa 0x2519813e386188ff

def z44 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4f981fff80000002 0x24f981fff8000000

def z45 : W := mkw 0x0002000440201080 0x0000200044020108 0xd0060c1c402070c7 0x5d0060c1c402070c

def z46 : W := mkw 0x16367e5dd8f3fce6 0xa16367e5dd8f3fce 0xfe7ffe7ff9fffcff 0xffe7ffe7ff9fffcf

def z47 : W := mkw 0x0020060000402800 0x0002006000040280 0xb0600e0041c07c06 0xdb0600e0041c07c0

def z48 : W := mkw 0x4fddd9fb00000000 0x04fddd9fb0000000 0x4f9ff1ff80000001 0x24f9ff1ff8000000

def z49 : W := mkw 0x1020460d80413cc0 0x21020460d80413cc 0x50000e1f80007cc2 0x050000e1f80007cc

def z50 : W := mkw 0x2ddd8000371c0008 0x02ddd8000371c000 0x0f9800003e180008 0x20f9800003e18000

def z51 : W := mkw 0x3dffe60df7ff3ccc 0x23dffe60df7ff3cc 0xffffee1fffff7ccf 0xfffffee1fffff7cc

def z52 : W := mkw 0x0b601f0025000000 0x00b601f002500000 0xafe01f807fc0000e 0xfafe01f807fc0000

def z53 : W := mkw 0x10ab660dc2ef3ccc 0x210ab660dc2ef3cc 0xf1ffee1fc7ff7ccf 0xff1ffee1fc7ff7cc

def z54 : W := mkw 0x2d56a00077be000c 0x02d56a00077be000 0xae66e0007fff000c 0x4ae66e0007fff000

def z55 : W := mkw 0x0614185000000000 0x0061418500000000 0x0e18106000000000 0x20e1810600000000

def z56 : W := mkw 0x0002200040a20004 0x00002200040a2000 0xa067e00041e70005 0xda067e00041e7000

def z57 : W := mkw 0x2416200077be000c 0x02416200077be000 0xae1e00007fff000d 0x7ae1e00007fff000

def z58 : W := mkw 0x4fdd99f200000000 0x04fdd99f20000000 0x0f9811e000000000 0x20f9811e00000000

def z59 : W := mkw 0x0000000080010440 0x0000000008001044 0x7001020380270cc7 0x97001020380270cc

def z60 : W := mkw 0x10ab66afc2ef3ddc 0x610ab66afc2ef3dd 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z61 : W := mkw 0x04160054503010a0 0x804160054503010a 0x401e007c003800f1 0x0401e007c003800f

def z62 : W := mkw 0x0960070025402a01 0x00960070025402a0 0x21e0038007c00f00 0x821e0038007c00f0

def z63 : W := mkw 0x0614185000000000 0x0061418500000000 0x4e1e1c7c00000003 0x74e1e1c7c0000000

def z64 : W := mkw 0x49e9c7ab00000000 0x049e9c7ab0000000 0x01e1e38380000000 0x801e1e3838000000

def z65 : W := mkw 0x02201f000840ea03 0x002201f000840ea0 0x10001f800000ff02 0x010001f800000ff0

def z66 : W := mkw 0x4ffddffb0840ea03 0x04ffddffb0840ea0 0x5fffffff8000ff03 0xf5fffffff8000ff0

def z67 : W := mkw 0x0000400900000000 0x0000040090000000 0x4007e01f80000001 0x04007e01f8000000

def z68 : W := mkw 0x008900a200000000 0x0008900a20000000 0x419913e380000003 0xb419913e38000000

def z69 : W := mkw 0x4ffddffb820d0558 0x44ffddffb820d055 0x7fffffff863f8fff 0xf7fffffff863f8ff

def z70 : W := mkw 0x0000000400001080 0x0000000040000108 0x50000c1c000070c2 0x050000c1c000070c

def z71 : W := mkw 0x16367e5d58f2f8a6 0xa16367e5d58f2f8a 0x8e66ec1c79c07000 0x48e66ec1c79c0700

def z72 : W := mkw 0x0b4019002d00c203 0x00b4019002d00c20 0x0f8011803e008308 0x20f8011803e00830

def z73 : W := mkw 0x249fa00052be000c 0x0249fa00052be000 0x001fe000003f0001 0x0001fe000003f000

def z74 : W := mkw 0x2fffbf007ffeea0f 0x02fffbf007ffeea0 0xbfffff807fffff0f 0xfbfffff807fffff0

def z75 : W := mkw 0x2fffbf0077be000c 0x02fffbf0077be000 0xafffff807fff000f 0xfafffff807fff000

def z76 : W := mkw 0x6ffffffb77be000c 0x06ffffffb77be000 0xefffffffffff000f 0xfefffffffffff000

def z77 : W := mkw 0x0000000080010440 0x0000000008001044 0x5000020380000cc2 0x05000020380000cc

def z78 : W := mkw 0x6ffffffbf7bf055c 0x46ffffffbf7bf055 0xffffffffffff8fff 0xfffffffffffff8ff

def z79 : W := mkw 0x06161854da3dd5fa 0xc06161854da3dd5f 0xfe1e1c7c7e3fffff 0x7fe1e1c7c7e3ffff

def z80 : W := mkw 0x49e9c7ab00000000 0x049e9c7ab0000000 0x41e7ef9f80000003 0xd41e7ef9f8000000

def z81 : W := mkw 0x4ffddffb00402800 0x04ffddffb0040280 0xffffffffc1c07c07 0xfffffffffc1c07c0

def z82 : W := mkw 0x1b627f0dede3fec7 0x21b627f0dede3fec 0xffe7ff9fffe7ffcf 0xfffe7ff9fffe7ffc

def z83 : W := mkw 0x0ddd800025000000 0x00ddd80002500000 0xafffe0007fc0000d 0xfafffe0007fc0000

def z84 : W := mkw 0x0616185050300000 0x0061618505030000 0xce1e1c7c7838000f 0x7ce1e1c7c7838000

def z85 : W := mkw 0x09e907a2a74d2f59 0x409e907a2a74d2f5 0x71f913e387ff8fff 0xb71f913e387ff8ff

def z86 : W := mkw 0x4fffdfff5830d0a2 0x84fffdfff5830d0a 0xdffffffff838f0ff 0xfdffffffff838f0f

def z87 : W := mkw 0x269fb8545abed0ae 0x8269fb8545abed0a 0xde1ffc7c783ff0ff 0x7de1ffc7c783ff0f

def z88 : W := mkw 0x10222604c0e33cc4 0x210222604c0e33cc 0xb0600e0041e77cc6 0xdb0600e0041e77cc

def z89 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x2181038386070f00 0x82181038386070f0

def z90 : W := mkw 0x069f18f6da3dd5fa 0xc069f18f6da3dd5f 0xff9f1ffffe3fffff 0xfff9f1ffffe3ffff

def z91 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0x9e061c1c7800f00e 0x79e061c1c7800f00

def z92 : W := mkw 0x4f74dffb00000000 0x04f74dffb0000000 0x4e66ffff80000002 0x44e66ffff8000000

def z93 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x0e66ec1c00000000 0x40e66ec1c0000000

def z94 : W := mkw 0x049d800000000000 0x0049d80000000000 0x001fe00000000001 0x0001fe0000000000

def z95 : W := mkw 0x6ffddffb371c0008 0x06ffddffb371c000 0x4fffffffbe18000b 0xf4fffffffbe18000

def z96 : W := mkw 0x008900a200000000 0x0008900a20000000 0x019811e000000000 0x2019811e00000000

def z97 : W := mkw 0x0416200050b20004 0x00416200050b2000 0xae7fe00079ff000d 0xfae7fe00079ff000

def z98 : W := mkw 0x29c9a000278e000c 0x029c9a000278e000 0x21e1e00007c70000 0x821e1e00007c7000

def z99 : W := mkw 0x46bddffb00000000 0x046bddffb0000000 0x401fffff80000003 0x0401fffff8000000

def z100 : W := mkw 0x4fffdfff7d70faa3 0x84fffdfff7d70faa 0xfffffffffff8ffff 0xffffffffffff8fff

def z101 : W := mkw 0x16bf7effdafffdfe 0xe16bf7effdafffdf 0xffffffffffffffff 0xffffffffffffffff

def z102 : W := mkw 0x0000000000000000 0x0000000000000000 0x2180038006000f00 0x82180038006000f0

def z103 : W := mkw 0x29c9a000278e000c 0x029c9a000278e000 0x21f9e00007ff000d 0xb21f9e00007ff000

def z104 : W := mkw 0x49e9c7ab00000000 0x049e9c7ab0000000 0x41f9f3e380000003 0xb41f9f3e38000000

def z105 : W := mkw 0x1022660d40e23884 0x21022660d40e2388 0x8066ec1c41c07000 0x48066ec1c41c0700

def z106 : W := mkw 0x2ddfa0a2f7bf055c 0x42ddfa0a2f7bf055 0xfffff3e3ffff8fff 0xffffff3e3ffff8ff

def z107 : W := mkw 0x020218044820d082 0x0020218044820d08 0xde061c1c7820f0cf 0x7de061c1c7820f0c

def z108 : W := mkw 0x34bfe60dd2ff3ccc 0x234bfe60dd2ff3cc 0xf07fee1fc1ff7cc7 0xdf07fee1fc1ff7cc

def z109 : W := mkw 0x5fffffffc0e33cc4 0x25fffffffc0e33cc 0xffffffffc1e77cc7 0xfffffffffc1e77cc

def z110 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000000003880fc 0x010000000003880f

def z111 : W := mkw 0x0be91f002f4cea0b 0x00be91f002f4cea0 0xbff91f807fffff0f 0xfbff91f807fffff0

def z112 : W := mkw 0x4fdd99f2020c0118 0x44fdd99f2020c011 0x0f9811e006188338 0x20f9811e00618833

def z113 : W := mkw 0x12205f0d8841fec3 0x212205f0d8841fec 0x50001f9f8000ffc2 0x050001f9f8000ffc

def z114 : W := mkw 0x4ffddffb2d00c203 0x04ffddffb2d00c20 0x4fffffffbe00830b 0xf4fffffffbe00830

def z115 : W := mkw 0x0000000000000000 0x0000000000000000 0x40180060003800f1 0x040180060003800f

def z116 : W := mkw 0x2f76bf007df2ea07 0x02f76bf007df2ea0 0xbfe6ff807fc0ff0e 0xfbfe6ff807fc0ff0

def z117 : W := mkw 0x061618005830c002 0x0061618005830c00 0x9e1e1c007838f00f 0x79e1e1c007838f00

def z118 : W := mkw 0x02201f0000000000 0x002201f000000000 0x00001f8000000002 0x000001f800000000

def z119 : W := mkw 0x4fdd99f200000000 0x04fdd99f20000000 0x0ffff1e000000001 0xf0ffff1e00000000

def z120 : W := mkw 0x2ddd8000371c0008 0x02ddd8000371c000 0x0fffe0003e180009 0xf0fffe0003e18000

def z121 : W := mkw 0x1b627f0dede3fec7 0x21b627f0dede3fec 0xfe67ee1ff9e77cc7 0xdfe67ee1ff9e77cc

def z122 : W := mkw 0x000000a280010550 0x4000000a28001055 0x501813e380388fff 0x3501813e380388ff

def z123 : W := mkw 0x000200045830d0a2 0x8000200045830d0a 0x900000007838f0fc 0x0900000007838f0f

def z124 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf07ffe7fc1fffcff 0xff07ffe7fc1fffcf

def z125 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x40190063803f00f1 0x040190063803f00f

def z126 : W := mkw 0x061418540800d0a2 0x8061418540800d0a 0x5e1e1c7c0000f0f3 0x75e1e1c7c0000f0f

def z127 : W := mkw 0x4f54995000000000 0x04f5499500000000 0x0e00000000000000 0x00e0000000000000

def z128 : W := mkw 0x400040fb00000000 0x0400040fb0000000 0x4000007f80000000 0x04000007f8000000

def z129 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x4e67ee1f80000003 0xd4e67ee1f8000000

def z130 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x7181038386270fc7 0x97181038386270fc

def z131 : W := mkw 0x0960070025402a01 0x00960070025402a0 0xb1e00f8047c07f06 0xdb1e00f8047c07f0

def z132 : W := mkw 0x4fffdffb50300000 0x04fffdffb5030000 0xcffffffff838000f 0xfcffffffff838000

def z133 : W := mkw 0x0416000050300000 0x0041600005030000 0xde1e1060783880ff 0x7de1e1060783880f

def z134 : W := mkw 0x0940000025000000 0x0094000002500000 0xbfe013807fc08f0e 0xfbfe013807fc08f0

def z135 : W := mkw 0x469dd8fb00000000 0x0469dd8fb0000000 0x4e1ffc7f80000003 0x74e1ffc7f8000000

def z136 : W := mkw 0x0960070025402a01 0x00960070025402a0 0xafe003807fc00f0c 0xfafe003807fc00f0

def z137 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fe0000000000000 0xf0fe000000000000

def z138 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e0000007800000c 0x78e0000007800000

def z139 : W := mkw 0x249fa00052be000c 0x0249fa00052be000 0x8e1fe000783f000d 0x78e1fe000783f000

def z140 : W := mkw 0x1416605dd0b314e4 0xa1416605dd0b314e 0x401fe07f803f00f1 0x0401fe07f803f00f

def z141 : W := mkw 0x008b20a2c2af055c 0x4008b20a2c2af055 0xf1fff3e3c7ff8fff 0xff1fff3e3c7ff8ff

def z142 : W := mkw 0x0940000025000000 0x0094000002500000 0x8e60000079c00000 0x48e60000079c0000

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0x4001020380000003 0x9400102038000000

def z144 : W := mkw 0x2d56a00075b20004 0x02d56a00075b2000 0x8e66e00079c00000 0x48e66e00079c0000

def z145 : W := mkw 0x0002000040200000 0x0000200004020000 0x8006000040200005 0x5800600004020000

def z146 : W := mkw 0x0b601f0000000000 0x00b601f000000000 0x0fe01f8000000002 0xf0fe01f800000000

def z147 : W := mkw 0x061418541810d0a2 0x8061418541810d0a 0x5e181c7c3818f0fa 0x25e181c7c3818f0f

def z148 : W := mkw 0x061418501810c022 0x8061418501810c02 0x5e181060383880ff 0x35e181060383880f

def z149 : W := mkw 0x00890000020c0008 0x000890000020c000 0x21990000063f000d 0xb21990000063f000

def z150 : W := mkw 0x10022004c0a314c4 0x210022004c0a314c 0x00000000002700c0 0x000000000002700c

def z151 : W := mkw 0x2002200077be000c 0x02002200077be000 0xa00000007fff000c 0x0a00000007fff000

def z152 : W := mkw 0x020018000800c002 0x0020018000800c00 0x9e001c007800f00e 0x79e001c007800f00

def z153 : W := mkw 0x1020660980c32c44 0x21020660980c32c4 0xb061ee03c1c77c06 0xdb061ee03c1c77c0

def z154 : W := mkw 0x2fdfb8547fbed0ae 0x82fdfb8547fbed0a 0xfffffc7c7ffff0ff 0xffffffc7c7ffff0f

def z155 : W := mkw 0x0942200065a20004 0x00942200065a2000 0xafe7e0007fe7000d 0xfafe7e0007fe7000

def z156 : W := mkw 0x0dfdc60900000000 0x00dfdc6090000000 0x4fffee1f80000003 0xf4fffee1f8000000

def z157 : W := mkw 0x6fdfb9f277be000c 0x06fdfb9f277be000 0xaffff1e07fff000d 0xfaffff1e07fff000

def z158 : W := mkw 0x2b623f007ffeea0f 0x02b623f007ffeea0 0xbfe01f807fffff0e 0xfbfe01f807fffff0

def z159 : W := mkw 0x0022060440603880 0x0002206044060388 0xf0660e1c41e07cc7 0xdf0660e1c41e07cc

def z160 : W := mkw 0x00000000820d0558 0x400000000820d055 0x31801380063f8ffe 0xb31801380063f8ff

def z161 : W := mkw 0x0b605f092d40ea03 0x00b605f092d40ea0 0xffe7ff9fffc0ff0f 0xfffe7ff9fffc0ff0

def z162 : W := mkw 0x0f5619547d30d2a3 0x80f5619547d30d2a 0xdf9e1dfc7e38f3ff 0x7df9e1dfc7e38f3f

def z163 : W := mkw 0x4fdd99f22d00c203 0x04fdd99f22d00c20 0x0f9811e03e008308 0x20f9811e03e00830

def z164 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xde060c1c782070c7 0x5de060c1c782070c

def z165 : W := mkw 0x0b601f0000000000 0x00b601f000000000 0x3fe01f8006008f0e 0xf3fe01f8006008f0

def z166 : W := mkw 0x0f761f545830d0a2 0x80f761f545830d0a 0xdffe1ffc7838f0ff 0xfdffe1ffc7838f0f

def z167 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xbffff3807fff8f0f 0xfbffff3807fff8f0

def z168 : W := mkw 0x0be91fa2af4def5b 0x40be91fa2af4def5 0xfff91fe3ffffffff 0xffff91fe3fffffff

def z169 : W := mkw 0x6ffdfffb278e000c 0x06ffdfffb278e000 0x6fffffff87c70003 0xf6fffffff87c7000

def z170 : W := mkw 0x42205ffb0840ea03 0x042205ffb0840ea0 0x50001fff8000ff02 0x050001fff8000ff0

def z171 : W := mkw 0x0000000000402800 0x0000000000040280 0xb000000041c07c04 0x0b000000041c07c0

def z172 : W := mkw 0x0002200040a20004 0x00002200040a2000 0xa000000041e70004 0x0a000000041e7000

def z173 : W := mkw 0x0b601f0000000000 0x00b601f000000000 0x0e600c0000000000 0x40e600c000000000

def z174 : W := mkw 0x3dffe6aff7ff3ddc 0x63dffe6aff7ff3dd 0xffffffffffffffff 0xffffffffffffffff

def z175 : W := mkw 0x2ddd80a2371c0118 0x42ddd80a2371c011 0x0f9811e03e188338 0x20f9811e03e18833

def z176 : W := mkw 0x0ddd80a200000000 0x00ddd80a20000000 0x4ffff3e380000003 0xf4ffff3e38000000

def z177 : W := mkw 0x0940000025000000 0x0094000002500000 0xafe000007fc0000c 0xfafe000007fc0000

def z178 : W := mkw 0x000000a280010550 0x4000000a28001055 0x700113e380278ff7 0x9700113e380278ff

def z179 : W := mkw 0x0200180000000000 0x0020018000000000 0x0e001c0000000002 0x70e001c000000000

def z180 : W := mkw 0x4dfdc7ab00000000 0x04dfdc7ab0000000 0x0fffe38380000001 0xf0fffe3838000000

def z181 : W := mkw 0x420019f200000000 0x0420019f20000000 0x000011e000000000 0x0000011e00000000

def z182 : W := mkw 0x0616185440201080 0x0061618544020108 0xde1e1c7c402070c7 0x7de1e1c7c402070c

def z183 : W := mkw 0x42205ffb00000000 0x042205ffb0000000 0x40001fff80000002 0x040001fff8000000

def z184 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0x9e060c1c7838f0fc 0x49e060c1c7838f0f

def z185 : W := mkw 0x249d8000121c0008 0x0249d8000121c000 0x0018000000180000 0x0001800000018000

def z186 : W := mkw 0x0b4019002d40ea03 0x00b4019002d40ea0 0xbf8011807fc0ff0c 0x2bf8011807fc0ff0

def z187 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xbe600e0079c07c06 0xdbe600e0079c07c0

def z188 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0x8e600c0079c07000 0x48e600c0079c0700

def z189 : W := mkw 0x2002200075b20004 0x02002200075b2000 0x8000000079c00000 0x08000000079c0000

def z190 : W := mkw 0x249fa00077be000c 0x0249fa00077be000 0xa01fe0007fff000d 0x0a01fe0007fff000

def z191 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0x1f801f803e00ff0a 0x21f801f803e00ff0

def z192 : W := mkw 0x2ddfa00477be108c 0x02ddfa00477be108 0xffffec1c7fff70cf 0xfffffec1c7fff70c

def z193 : W := mkw 0x249fa00052be000c 0x0249fa00052be000 0xa07fe00041ff0005 0xda07fe00041ff000

def z194 : W := mkw 0x2d56a00075b20004 0x02d56a00075b2000 0xae67e00079e70005 0xdae67e00079e7000

def z195 : W := mkw 0x000000a280010550 0x4000000a28001055 0x500013e380008ff2 0x0500013e380008ff

def z196 : W := mkw 0x020018540800d0a2 0x8020018540800d0a 0x50181c7c0038f0ff 0x350181c7c0038f0f

def z197 : W := mkw 0x0000000000000000 0x0000000000000000 0x719813e006388fff 0xb719813e006388ff

def z198 : W := mkw 0x52205fff80413cc0 0x252205fff80413cc 0x50001fff80007cc2 0x050001fff80007cc

def z199 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x0001000380070000 0x0000100038007000

def z200 : W := mkw 0x000200045830d0a2 0x8000200045830d0a 0x8000000078007000 0x0800000007800700

def z201 : W := mkw 0x1002600d40a21084 0x21002600d40a2108 0x0006e01c00000000 0x00006e01c0000000

def z202 : W := mkw 0x00000000820d0558 0x400000000820d055 0x30000000063f8ffc 0x030000000063f8ff

def z203 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4e7fec7f80000001 0x44e7fec7f8000000

def z204 : W := mkw 0x1000000480413cc0 0x21000000480413cc 0x1000000000007cc0 0x01000000000007cc

def z205 : W := mkw 0x10a946af824d3dd8 0x610a946af824d3dd 0x71991fff863fffff 0xb71991fff863ffff

def z206 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x0fe7ef9f80000000 0xc0fe7ef9f8000000

def z207 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0x6067e21f81e70cc1 0x86067e21f81e70cc

def z208 : W := mkw 0x020218545830d0a2 0x8020218545830d0a 0xd0001c7c7838f0fe 0x0d0001c7c7838f0f

def z209 : W := mkw 0x42a95ffb820d0558 0x442a95ffb820d055 0x71991fff863f8fff 0xb71991fff863f8ff

def z210 : W := mkw 0x008900a2020c0118 0x4008900a2020c011 0x0180018006000300 0x0018001800600030

def z211 : W := mkw 0x16367e5d58f2f8a6 0xa16367e5d58f2f8a 0xde7efc7c79f8f0ff 0x7de7efc7c79f8f0f

def z212 : W := mkw 0x2ddfa0a2f7bf055c 0x42ddfa0a2f7bf055 0xafffe383ffff0f0d 0xfafffe383ffff0f0

def z213 : W := mkw 0x0f761f547d70faa3 0x80f761f547d70faa 0xbfe61f9c7fc0ff0e 0xfbfe61f9c7fc0ff0

def z214 : W := mkw 0x0020060000402800 0x0002006000040280 0x80600c0041c07000 0x480600c0041c0700

def z215 : W := mkw 0x00890000020c0008 0x000890000020c000 0x0198000006180008 0x2019800000618000

def z216 : W := mkw 0x10022004ede3fec7 0x210022004ede3fec 0xb00000007fe7ffcc 0x0b00000007fe7ffc

def z217 : W := mkw 0x2f76bf007df2ea07 0x02f76bf007df2ea0 0x8e66ec0079c07000 0x48e66ec0079c0700

def z218 : W := mkw 0x1022660dc0a314c4 0x21022660dc0a314c 0x4067ee1f802700c3 0xd4067ee1f802700c

def z219 : W := mkw 0x008900a280010550 0x4008900a28001055 0x519913e380008ff3 0xb519913e380008ff

def z220 : W := mkw 0x2fdfb8f6ffbfd5fe 0xc2fdfb8f6ffbfd5f 0xffffffffffffffff 0xffffffffffffffff

def z221 : W := mkw 0x020018540800d0a2 0x8020018540800d0a 0x50001c7c0000f0f2 0x050001c7c0000f0f

def z222 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z223 : W := mkw 0x0000000000000000 0x0000000000000000 0x50181060003880ff 0x350181060003880f

def z224 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xa067ee1fc1c77c00 0xca067ee1fc1c77c0

def z225 : W := mkw 0x4414c05900000000 0x04414c0590000000 0x0006e01c00000000 0x00006e01c0000000

def z226 : W := mkw 0x061418501810c022 0x8061418501810c02 0x4e1e1c7c3818803b 0x74e1e1c7c3818803

def z227 : W := mkw 0x4089c0ab00000000 0x04089c0ab0000000 0x0001e00380000000 0x00001e0038000000

def z228 : W := mkw 0x200220007ffeea0f 0x0200220007ffeea0 0xb00000007fffff0c 0x0b00000007fffff0

def z229 : W := mkw 0x4ffddfff0800d0a2 0x84ffddfff0800d0a 0x5fffffff8000f0f3 0xf5fffffff8000f0f

def z230 : W := mkw 0x1002600dc0a314c4 0x21002600dc0a314c 0x4007e01f802700c1 0x04007e01f802700c

def z231 : W := mkw 0x061418500800c002 0x0061418500800c00 0xde1e1c7c7800f00f 0x7de1e1c7c7800f00

def z232 : W := mkw 0x3ddfa004f7ff3ccc 0x23ddfa004f7ff3cc 0xbfffe0007fff7ccd 0xfbfffe0007fff7cc

def z233 : W := mkw 0x049f00f6d23d15f8 0xc049f00f6d23d15f 0x401f007f803f00f1 0x0401f007f803f00f

def z234 : W := mkw 0x008900a200000000 0x0008900a20000000 0x4019006380000001 0x0401900638000000

def z235 : W := mkw 0x402047ab00000000 0x0402047ab0000000 0x0000038380000000 0x0000003838000000

def z236 : W := mkw 0x00890000020c0008 0x000890000020c000 0x00190000003f0001 0x000190000003f000

def z237 : W := mkw 0x42205fff0800d0a2 0x842205fff0800d0a 0x50001fff8000f0f2 0x050001fff8000f0f

def z238 : W := mkw 0x2ddfa0047fbed0ae 0x82ddfa0047fbed0a 0xbfffe0007ffff0fd 0xfbfffe0007ffff0f

def z239 : W := mkw 0x44bdc6fb00000000 0x044bdc6fb0000000 0x407fee7f80000003 0xd407fee7f8000000

def z240 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0xcffffffff9c07003 0xfcffffffff9c0700

def z241 : W := mkw 0x008b200042ae000c 0x0008b200042ae000 0xa1ffe00047ff000d 0xfa1ffe00047ff000

def z242 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x319811e0063f8ffc 0x2319811e0063f8ff

def z243 : W := mkw 0x5fffffff40e23884 0x25fffffff40e2388 0xcfffffffc1c07003 0xfcfffffffc1c0700

def z244 : W := mkw 0x1002200440e23884 0x21002200440e2388 0x8000000041c07000 0x08000000041c0700

def z245 : W := mkw 0x4ffddf5900000000 0x04ffddf590000000 0x0fffec1c00000001 0xf0fffec1c0000000

def z246 : W := mkw 0x4ffddffb25000000 0x04ffddffb2500000 0xefffffffffc0000f 0xfefffffffffc0000

def z247 : W := mkw 0x2002200052be000c 0x02002200052be000 0x00000000003f0000 0x000000000003f000

def z248 : W := mkw 0x4ffffffb40a20004 0x04ffffffb40a2000 0xefffffffc1e70007 0xfefffffffc1e7000

def z249 : W := mkw 0x020018f68801d5f2 0xc020018f68801d5f 0x50001fff8000fff2 0x050001fff8000fff

def z250 : W := mkw 0x2d56a00075b20004 0x02d56a00075b2000 0xafe6e0007fc0000c 0xfafe6e0007fc0000

def z251 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf0000e1fc1e77cc6 0x0f0000e1fc1e77cc

def z252 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018106000188038 0x2001810600018803

def z253 : W := mkw 0x1616785dd8b3d4e6 0xa1616785dd8b3d4e 0xde1ffc7ff83ff0ff 0x7de1ffc7ff83ff0f

def z254 : W := mkw 0x0020460900000000 0x0002046090000000 0x0066ec1c00000000 0x40066ec1c0000000

def z255 : W := mkw 0x0022660940a20004 0x00022660940a2000 0xe067ee1fc1e70007 0xde067ee1fc1e7000

def z256 : W := mkw 0x008900a280010440 0x0008900a28001044 0x719913e380270cc7 0xb719913e380270cc

def z257 : W := mkw 0x06161854d831d4e2 0x806161854d831d4e 0xfe1f1e7ff83ffcff 0xffe1f1e7ff83ffcf

def z258 : W := mkw 0x0ddd800000000000 0x00ddd80000000000 0x0fffe00000000001 0xf0fffe0000000000

def z259 : W := mkw 0x00890000020c0008 0x000890000020c000 0x2181000006070000 0x8218100000607000

def z260 : W := mkw 0x00a946ab00000000 0x000a946ab0000000 0x41ffffff80000003 0xf41ffffff8000000

def z261 : W := mkw 0x0f741f503d50ea23 0x80f741f503d50ea2 0xbff81fe07fd8ff3e 0xfbff81fe07fd8ff3

def z262 : W := mkw 0x0960060025402800 0x0096006002540280 0xbfe00e007fc07c0e 0xfbfe00e007fc07c0

def z263 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0x8e7fe00079ff0001 0x48e7fe00079ff000

def z264 : W := mkw 0x59ebe7afc0e33cc4 0x259ebe7afc0e33cc 0xf1e7ef9fc1e77cc7 0xdf1e7ef9fc1e77cc

def z265 : W := mkw 0x0ffd9f002d40ea03 0x00ffd9f002d40ea0 0xbfffff807fc0ff0f 0xfbfffff807fc0ff0

def z266 : W := mkw 0x2ddfa0a277be011c 0x42ddfa0a277be011 0xaffff1e07fff833d 0xfaffff1e07fff833

def z267 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x3181138386078f0e 0xb3181138386078f0

def z268 : W := mkw 0x0002200440a21084 0x00002200440a2108 0xf067ec1c41e770c7 0xdf067ec1c41e770c

def z269 : W := mkw 0x0414005000000000 0x0041400500000000 0x401e007c00000001 0x0401e007c0000000

def z270 : W := mkw 0x4ffddffb820d0558 0x44ffddffb820d055 0x6fffffff86070f03 0xf6fffffff86070f0

def z271 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x619913e386070f03 0xb619913e386070f0

def z272 : W := mkw 0x4ffd9ff22d40ea03 0x04ffd9ff22d40ea0 0xbff81fe07fc0ff0e 0xfbff81fe07fc0ff0

def z273 : W := mkw 0x000200045830d0a2 0x8000200045830d0a 0xd01810607838f0ff 0x3d01810607838f0f

def z274 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x50191063803f80ff 0x350191063803f80f

def z275 : W := mkw 0x002006002d40ea03 0x0002006002d40ea0 0xb0600e007fc0ff0e 0xdb0600e007fc0ff0

def z276 : W := mkw 0x449dc0fb820d0558 0x4449dc0fb820d055 0x719ff3ff863f8fff 0xb719ff3ff863f8ff

def z277 : W := mkw 0x5fffffffede3fec7 0x25fffffffede3fec 0xffffffffffe7ffcf 0xfffffffffffe7ffc

def z278 : W := mkw 0x0b623f006de2ea07 0x00b623f006de2ea0 0xbfe7ff807fe7ff0f 0xfbfe7ff807fe7ff0

def z279 : W := mkw 0x0020060000402800 0x0002006000040280 0xb1e01f8047c0ff0e 0xfb1e01f8047c0ff0

def z280 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0x8fe01f8079c07002 0xf8fe01f8079c0700

def z281 : W := mkw 0x049f00f6d23d15f8 0xc049f00f6d23d15f 0x719f13ff863f8fff 0xb719f13ff863f8ff

def z282 : W := mkw 0x0002000050300000 0x0000200005030000 0x800000007838000c 0x0800000007838000

def z283 : W := mkw 0x5fffffffc0a314c4 0x25fffffffc0a314c 0x4fffffff802700c3 0xf4fffffff802700c

def z284 : W := mkw 0x008900a2020c0118 0x4008900a2020c011 0x219911e0063f833d 0xb219911e0063f833

def z285 : W := mkw 0x00a946ab820d0558 0x400a946ab820d055 0x71ffffff863f8fff 0xf71ffffff863f8ff

def z286 : W := mkw 0x008900a2020c0118 0x4008900a2020c011 0x519811e0063883ff 0x3519811e0063883f

def z287 : W := mkw 0x6ffffffb52be000c 0x06ffffffb52be000 0x4fffffff803f0003 0xf4fffffff803f000

def z288 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x5fffffff803880ff 0xf5fffffff803880f

def z289 : W := mkw 0x4fffdfffda3dd5fa 0xc4fffdfffda3dd5f 0xfffffffffe3fffff 0xffffffffffe3ffff

def z290 : W := mkw 0x42205f5900000000 0x042205f590000000 0x00000c1c00000000 0x000000c1c0000000

def z291 : W := mkw 0x4fffdfff40201080 0x04fffdfff4020108 0xdfffffffc02070c7 0xfdfffffffc02070c

def z292 : W := mkw 0x02a91fa28a4def5b 0x402a91fa28a4def5 0x71991fe3863fffff 0xb71991fe3863ffff

def z293 : W := mkw 0x008900a2020c0118 0x4008900a2020c011 0x419913e38618833b 0xb419913e38618833

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0x50001060000080f2 0x050001060000080f

def z295 : W := mkw 0x000000a280010550 0x4000000a28001055 0x40000063800000f0 0x040000063800000f

def z296 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xd066ee1fc1c07cc2 0x4d066ee1fc1c07cc

def z297 : W := mkw 0x1022660d40e23884 0x21022660d40e2388 0xc067ee1fc1c07003 0xdc067ee1fc1c0700

def z298 : W := mkw 0x4f74df592d40ea03 0x04f74df592d40ea0 0x8e66ec1c79c07000 0x48e66ec1c79c0700

def z299 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000000002000c7 0x150000000002000c

def z300 : W := mkw 0x1020460d00403880 0x21020460d0040388 0x00000c1c00007000 0x000000c1c0000700

def z301 : W := mkw 0x1436660dd0f33cc4 0x21436660dd0f33cc 0xfe7fee1ff9ff7ccf 0xffe7fee1ff9ff7cc

def z302 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x21990383863f0f0d 0xb21990383863f0f0

def z303 : W := mkw 0x00890000020c0008 0x000890000020c000 0x31991380063f8f0f 0xb31991380063f8f0

def z304 : W := mkw 0x041600545830d0a2 0x8041600545830d0a 0xd01e007c7838f0fd 0x0d01e007c7838f0f

def z305 : W := mkw 0x028918a28a0dc55a 0x4028918a28a0dc55 0xff991fe3fe3fffff 0xfff991fe3fe3ffff

def z306 : W := mkw 0x49c981a200000000 0x049c981a20000000 0x0180018000000000 0x0018001800000000

def z307 : W := mkw 0x008b00a6da3dd5fa 0xc008b00a6da3dd5f 0xf19913e3fe3fffff 0xbf19913e3fe3ffff

def z308 : W := mkw 0x4ffd9ff200000000 0x04ffd9ff20000000 0x0ff81fe000000002 0xf0ff81fe00000000

def z309 : W := mkw 0x42205ffb00000000 0x042205ffb0000000 0x4067ffff80000003 0xd4067ffff8000000

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0x90000c0040007006 0x590000c004000700

def z311 : W := mkw 0x2942200077be000c 0x02942200077be000 0xafe000007fff000c 0xfafe000007fff000

def z312 : W := mkw 0x0000000080010440 0x0000000008001044 0x2001020380070c00 0x82001020380070c0

def z313 : W := mkw 0x4ffddffb0800c002 0x04ffddffb0800c00 0xdffffffff800f00f 0xfdffffffff800f00

def z314 : W := mkw 0x12205e5d8841fce2 0xa12205e5d8841fce 0x50001e7f8000fcf2 0x050001e7f8000fcf

def z315 : W := mkw 0x0f741f5000000000 0x00f741f500000000 0x4ffe1ffc00000003 0xf4ffe1ffc0000000

def z316 : W := mkw 0x2fdd99003f1cc20b 0x02fdd99003f1cc20 0x0f9811803e188308 0x20f9811803e18830

def z317 : W := mkw 0x0b4019002d00c203 0x00b4019002d00c20 0xafe011807fc0830c 0xfafe011807fc0830

def z318 : W := mkw 0x1002600dc0a314c4 0x21002600dc0a314c 0x7007e21f80270cc7 0x97007e21f80270cc

def z319 : W := mkw 0x16163854d8f3fce6 0xa16163854d8f3fce 0xfe1e1c7c79fffcff 0x7fe1e1c7c79fffcf

def z320 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xfff81fe07ff8ffff 0xffff81fe07ff8fff

def z321 : W := mkw 0x6ffffffb75b20004 0x06ffffffb75b2000 0xcffffffff9c00003 0xfcffffffff9c0000

def z322 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x0ff9f3e380000000 0xa0ff9f3e38000000

def z323 : W := mkw 0x12227e5dc8e3fce6 0xa12227e5dc8e3fce 0xf067fe7fc1e7fcf7 0xdf067fe7fc1e7fcf

def z324 : W := mkw 0x000200045830d0a2 0x8000200045830d0a 0xd0060c1c7838f0ff 0x5d0060c1c7838f0f

def z325 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0x9e601c0079c0f00e 0x79e601c0079c0f00

def z326 : W := mkw 0x49e9c7ab25402a01 0x049e9c7ab25402a0 0x21e1e38387c00f00 0x821e1e38387c00f0

def z327 : W := mkw 0x29c98000270c0008 0x029c98000270c000 0x0180000006000000 0x0018000000600000

def z328 : W := mkw 0x00890000020c0008 0x000890000020c000 0x71991060063f80ff 0xb71991060063f80f

def z329 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x61990063863f00fd 0xb61990063863f00f

def z330 : W := mkw 0x0616385458b2d0a6 0x80616385458b2d0a 0xfe7ffc7c79fff0ff 0xffe7ffc7c79fff0f

def z331 : W := mkw 0x4960c70900000000 0x04960c7090000000 0x0060e00000000000 0x00060e0000000000

def z332 : W := mkw 0x020018540800d0a2 0x8020018540800d0a 0x00000c1c00007000 0x000000c1c0000700

def z333 : W := mkw 0x4b605ffb2d40ea03 0x04b605ffb2d40ea0 0xffe01fffffc0ff0e 0xfffe01fffffc0ff0

def z334 : W := mkw 0x0960070025402a01 0x00960070025402a0 0x31e0138007c08f0e 0xb31e0138007c08f0

def z335 : W := mkw 0x0002200040a20004 0x00002200040a2000 0x8066e00041c00000 0x48066e00041c0000

def z336 : W := mkw 0x12227f0dc8e3fec7 0x212227f0dc8e3fec 0xf067ff9fc1e7ffc7 0xdf067ff9fc1e7ffc

def z337 : W := mkw 0x4ffddffbaf4def5b 0x44ffddffbaf4def5 0xffffffffffffffff 0xffffffffffffffff

def z338 : W := mkw 0x09c90000270c0008 0x009c90000270c000 0xaff900007fff000d 0xfaff900007fff000

def z339 : W := mkw 0x2ddfa0a277be000c 0x02ddfa0a277be000 0xeffff3e3ffff000f 0xfeffff3e3ffff000

def z340 : W := mkw 0x29cba00067ae000c 0x029cba00067ae000 0xa1e7e00047e70005 0xda1e7e00047e7000

def z341 : W := mkw 0x1022660dd8f3fce6 0xa1022660dd8f3fce 0xf067ee1ff9fffcff 0xdf067ee1ff9fffcf

def z342 : W := mkw 0x69e9e7ab278e000c 0x069e9e7ab278e000 0x21e1e38387c70000 0x821e1e38387c7000

def z343 : W := mkw 0x0960070025402a01 0x00960070025402a0 0x0060000001c00000 0x00060000001c0000

def z344 : W := mkw 0x00000000020c0118 0x400000000020c011 0x0000000006188338 0x0000000000618833

def z345 : W := mkw 0x0002200040a20004 0x00002200040a2000 0x0007e00000270001 0x00007e0000027000

def z346 : W := mkw 0x1000400d800114c0 0x21000400d800114c 0x4000001f800000c0 0x04000001f800000c

def z347 : W := mkw 0x2ddd80a2b71d0558 0x42ddd80a2b71d055 0x7f9913e3be3f8fff 0xb7f9913e3be3f8ff

def z348 : W := mkw 0x2ddda000379e000c 0x02ddda000379e000 0x2ff9e0003fdf0008 0xa2ff9e0003fdf000

def z349 : W := mkw 0x10022004d8f3fce6 0xa10022004d8f3fce 0xb000000079fffcfc 0x0b000000079fffcf

def z350 : W := mkw 0x020018500800c022 0x8020018500800c02 0x0000106000008030 0x0000010600000803

def z351 : W := mkw 0x1020660d80c33cc4 0x21020660d80c33cc 0x7061ee1f81c77cc2 0x87061ee1f81c77cc

def z352 : W := mkw 0x0020060080412c40 0x00020060080412c4 0xf0610e03c1e77cc7 0xdf0610e03c1e77cc

def z353 : W := mkw 0x2dffa60077fe280c 0x02dffa60077fe280 0xbfffee007fff7c0f 0xfbfffee007fff7c0

def z354 : W := mkw 0x020218045830d0a2 0x8020218045830d0a 0x9e001c007838f0fe 0x79e001c007838f0f

def z355 : W := mkw 0x00890000820d0448 0x000890000820d044 0x71990203863f0ccf 0xb71990203863f0cc

def z356 : W := mkw 0x0be91fa22f4ceb1b 0x40be91fa22f4ceb1 0xbff81fe07fd8ff3e 0xfbff81fe07fd8ff3

def z357 : W := mkw 0x02201f540840faa3 0x802201f540840faa 0x50001ffc0000fff2 0x050001ffc0000fff

def z358 : W := mkw 0x3dffe609f7ff2c4c 0x23dffe609f7ff2c4 0xafffe203ffff0c0d 0xfafffe203ffff0c0

def z359 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x70190063863f8ffd 0x070190063863f8ff

def z360 : W := mkw 0x008900a2af4def5b 0x4008900a2af4def5 0xf19913e3ffffffff 0xbf19913e3fffffff

def z361 : W := mkw 0x0002000440201080 0x0000200044020108 0x90000000402070c4 0x090000000402070c

def z362 : W := mkw 0x3ffffe5dfffffcee 0xa3ffffe5dfffffce 0xfffffe7ffffffcff 0xffffffe7ffffffcf

def z363 : W := mkw 0x0b601f000840ea03 0x00b601f000840ea0 0x1fe01f800000ff02 0xf1fe01f800000ff0

def z364 : W := mkw 0x0414005010100020 0x8041400501010002 0x0018006000180030 0x0001800600018003

def z365 : W := mkw 0x00020004503010a0 0x800020004503010a 0x00000000003800f0 0x000000000003800f

def z366 : W := mkw 0x069f18f6da3dd5fa 0xc069f18f6da3dd5f 0xde1f1c7ff83ff0ff 0x7de1f1c7ff83ff0f

def z367 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0x9e601f8079c0ff02 0x49e601f8079c0ff0

def z368 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0xf0010203c1e77cc7 0x9f0010203c1e77cc

def z369 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0x0f9fe0003e3f0009 0x20f9fe0003e3f000

def z370 : W := mkw 0x000000a280010550 0x4000000a28001055 0x718013e386008ffe 0xb718013e386008ff

def z371 : W := mkw 0x4fffdfff503010a0 0x84fffdfff503010a 0x4fffffff803800f3 0xf4fffffff803800f

def z372 : W := mkw 0x30022004f7ff3ccc 0x230022004f7ff3cc 0xb00000007fff7ccc 0x0b00000007fff7cc

def z373 : W := mkw 0x5f76ff5d40e23884 0x25f76ff5d40e2388 0x8e66ec1c41c07000 0x48e66ec1c41c0700

def z374 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0xb067e00041e77cc5 0xdb067e00041e77cc

def z375 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x419ff3ff80000003 0xb419ff3ff8000000

def z376 : W := mkw 0x4ffddffb25402a01 0x04ffddffb25402a0 0x6fffffff87c00f03 0xf6fffffff87c00f0

def z377 : W := mkw 0x1022460dc0613cc0 0x21022460dc0613cc 0xd0060e1fc0207cc7 0x5d0060e1fc0207cc

def z378 : W := mkw 0x4b605ffb00000000 0x04b605ffb0000000 0x4fe01fff80000002 0xf4fe01fff8000000

def z379 : W := mkw 0x2fdf98547f3cd0aa 0x82fdf98547f3cd0a 0xdf9e1c7c7e38f0ff 0x7df9e1c7c7e38f0f

def z380 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xce1e1c7c78007003 0x7ce1e1c7c7800700

def z381 : W := mkw 0x00000000020c0008 0x000000000020c000 0x20000000063f000c 0x020000000063f000

def z382 : W := mkw 0x0000000080010440 0x0000000008001044 0x70191263803f8cff 0xb70191263803f8cf

def z383 : W := mkw 0x3ddfe00df7bf14cc 0x23ddfe00df7bf14c 0xefffe01fffff00cd 0xfefffe01fffff00c

def z384 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0x8e1e1c7c7818f038 0x68e1e1c7c7818f03

def z385 : W := mkw 0x54bfe6ffc0e33cc4 0x254bfe6ffc0e33cc 0xf07fee7fc1e77cc7 0xdf07fee7fc1e77cc

def z386 : W := mkw 0x249fa00052be000c 0x0249fa00052be000 0x219fe000063f000d 0xb219fe000063f000

def z387 : W := mkw 0x10ab66afc0e33cc4 0x210ab66afc0e33cc 0xf1ffffffc1e77cc7 0xff1ffffffc1e77cc

def z388 : W := mkw 0x1b605f0dad41fec3 0x21b605f0dad41fec 0xffe01f9fffc0ffce 0xfffe01f9fffc0ffc

def z389 : W := mkw 0x3d76e60df5f33cc4 0x23d76e60df5f33cc 0xfe67ee1ff9e77cc7 0xdfe67ee1ff9e77cc

def z390 : W := mkw 0x208b200077be000c 0x0208b200077be000 0xa19900007fff000d 0xba19900007fff000

def z391 : W := mkw 0x0020060000402800 0x0002006000040280 0x10000e0000007c02 0x010000e0000007c0

def z392 : W := mkw 0x069d18f21a1cc13a 0xc069d18f21a1cc13 0x0f9811e03e188338 0x20f9811e03e18833

def z393 : W := mkw 0x6ddfe0fb77be000c 0x06ddfe0fb77be000 0xefffe07fffff000d 0xfefffe07fffff000

def z394 : W := mkw 0x6fffffff7fbed0ae 0x86fffffff7fbed0a 0xfffffffffffff0ff 0xffffffffffffff0f

def z395 : W := mkw 0x200220047fbed0ae 0x8200220047fbed0a 0xb00000007ffff0fc 0x0b00000007ffff0f

def z396 : W := mkw 0x46345ffb00000000 0x046345ffb0000000 0x4e1e1fff80000003 0x74e1e1fff8000000

def z397 : W := mkw 0x0ddfa00040a20004 0x00ddfa00040a2000 0xafffe00041e70005 0xfafffe00041e7000

def z398 : W := mkw 0x0d54800000000000 0x00d5480000000000 0x0e66e00000000000 0x40e66e0000000000

def z399 : W := mkw 0x449d80f200000000 0x0449d80f20000000 0x0018006000000000 0x0001800600000000

def z400 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xafe7e0007fc70000 0xcafe7e0007fc7000

def z401 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xc067ec1fc1e770c1 0x4c067ec1fc1e770c

def z402 : W := mkw 0x4f74df592d40ea03 0x04f74df592d40ea0 0xbfe6ff9c7fc0ff0e 0xfbfe6ff9c7fc0ff0

def z403 : W := mkw 0x3fffff0dfffffecf 0x23fffff0dfffffec 0xffffff9fffffffcf 0xfffffff9fffffffc

def z404 : W := mkw 0x4be9dfab2d40ea03 0x04be9dfab2d40ea0 0xbfe1ff83ffc0ff0e 0xfbfe1ff83ffc0ff0

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0x100010000000800e 0x3100010000000800

def z406 : W := mkw 0x0b601f00ad41ee43 0x00b601f00ad41ee4 0xffe11f83ffe7ffcf 0xfffe11f83ffe7ffc

def z407 : W := mkw 0x0000000080010550 0x4000000008001055 0x1000000000008ff0 0x01000000000008ff

def z408 : W := mkw 0x1020460d80413cc0 0x21020460d80413cc 0x70010e1f80277cc7 0x970010e1f80277cc

def z409 : W := mkw 0x04160054503010a0 0x804160054503010a 0xce1e007c783800fd 0x7ce1e007c783800f

def z410 : W := mkw 0x0000000000000000 0x0000000000000000 0x4018106000000003 0x3401810600000000

def z411 : W := mkw 0x4f76df5d5830d0a2 0x84f76df5d5830d0a 0x8e66ec1c78007000 0x48e66ec1c7800700

def z412 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xafe00c007fc0700c 0xfafe00c007fc0700

def z413 : W := mkw 0x10ab66afc2ef3ddc 0x610ab66afc2ef3dd 0xf07fee7fc1ff7cf7 0xdf07fee7fc1ff7cf

def z414 : W := mkw 0x0020460900000000 0x0002046090000000 0x0061e20380000000 0x80061e2038000000

def z415 : W := mkw 0x6fdd99f2371c0008 0x06fdd99f2371c000 0x0f9811e03e180008 0x20f9811e03e18000

def z416 : W := mkw 0x04160054503010a0 0x804160054503010a 0xd01e0c7c403870f7 0x5d01e0c7c403870f

def z417 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf1e7ff9fc7e7ffcf 0xff1e7ff9fc7e7ffc

def z418 : W := mkw 0x5ffdfffb80c32c44 0x25ffdfffb80c32c4 0x6fffffff81c70c03 0xf6fffffff81c70c0

def z419 : W := mkw 0x041600045830d0a2 0x8041600045830d0a 0x9e1e00007838f0fd 0x79e1e00007838f0f

def z420 : W := mkw 0x02201f000840ea03 0x002201f000840ea0 0x31801f800600ff0e 0xb31801f800600ff0

def z421 : W := mkw 0x2fdfb8507fbec02e 0x82fdfb8507fbec02 0xaffff0607fff803d 0xfaffff0607fff803

def z422 : W := mkw 0x04160054503010a0 0x804160054503010a 0x501e107c003880ff 0x3501e107c003880f

def z423 : W := mkw 0x0614185000000000 0x0061418500000000 0x5e1e1c7c003880ff 0x75e1e1c7c003880f

def z424 : W := mkw 0x16365e5dd871fce2 0xa16365e5dd871fce 0xde1e1e7ff838fcff 0x7de1e1e7ff838fcf

def z425 : W := mkw 0x6f76ff5975b20004 0x06f76ff5975b2000 0x8e66ec1c79c00000 0x48e66ec1c79c0000

def z426 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0x4e1e107c383880f9 0x24e1e107c383880f

def z427 : W := mkw 0x2ddd8000371c0008 0x02ddd8000371c000 0xaff800007fd8000c 0xfaff800007fd8000

def z428 : W := mkw 0x1962660de5e33cc4 0x21962660de5e33cc 0xffe7ee1fffe77ccf 0xfffe7ee1fffe77cc

def z429 : W := mkw 0x0be91fa2af4def5b 0x40be91fa2af4def5 0xbfe11f83ffc7ff0e 0xfbfe11f83ffc7ff0

def z430 : W := mkw 0x0b601f0025402a01 0x00b601f0025402a0 0x2fe01f8007c00f02 0xf2fe01f8007c00f0

def z431 : W := mkw 0x0ddd800000000000 0x00ddd80000000000 0x0f98000000000000 0x20f9800000000000

def z432 : W := mkw 0x0000000000000000 0x0000000000000000 0x001800000038000d 0x3001800000038000

def z433 : W := mkw 0x0000000080010440 0x0000000008001044 0x3000000000270cc4 0x03000000000270cc

def z434 : W := mkw 0x2fdd98503f1cc02a 0x82fdd98503f1cc02 0x0f9810603e188038 0x20f9810603e18803

def z435 : W := mkw 0x3d76e60d75f23884 0x23d76e60d75f2388 0x8e66ec1c79c07000 0x48e66ec1c79c0700

def z436 : W := mkw 0x02201f000840ea03 0x002201f000840ea0 0xb0601f8041c0ff06 0xdb0601f8041c0ff0

def z437 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xafe00f807fc07f00 0xcafe00f807fc07f0

def z438 : W := mkw 0x2ddf8000773c0008 0x02ddf8000773c000 0x8f9e00007e38000d 0x78f9e00007e38000

def z439 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0x501e1c7c0038f0f3 0x0501e1c7c0038f0f

def z440 : W := mkw 0x02201f002d40ea03 0x002201f002d40ea0 0xb0001f807fc0ff0e 0x0b0001f807fc0ff0

def z441 : W := mkw 0x449fc0ff503010a0 0x8449fc0ff503010a 0x401fe07f803800f1 0x0401fe07f803800f

def z442 : W := mkw 0x00022000c0a30444 0x000022000c0a3044 0xf067e203c1e70cc7 0xdf067e203c1e70cc

def z443 : W := mkw 0x1020460d80413cc0 0x21020460d80413cc 0x5067ee1f80007cc3 0xd5067ee1f80007cc

def z444 : W := mkw 0x2fffbf007ffeea0f 0x02fffbf007ffeea0 0xafffec007fff700d 0xfafffec007fff700

def z445 : W := mkw 0x4fdd99f200000000 0x04fdd99f20000000 0x4f9e1dfc00000003 0x74f9e1dfc0000000

def z446 : W := mkw 0x0b40190000000000 0x00b4019000000000 0x0f80118000000000 0x20f8011800000000

def z447 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0x9e1810607838f0fc 0x29e1810607838f0f

def z448 : W := mkw 0x16367e5dd8f3fce6 0xa16367e5dd8f3fce 0xfe67ee1ff9e77cc7 0xdfe67ee1ff9e77cc

def z449 : W := mkw 0x0000000000000000 0x0000000000000000 0x40060c1c00000003 0x540060c1c0000000

def z450 : W := mkw 0x09c9800000000000 0x009c980000000000 0x01e1e00000000000 0x801e1e0000000000

def z451 : W := mkw 0x0b601f002d00c203 0x00b601f002d00c20 0x0fe01f803e00830a 0xf0fe01f803e00830

def z452 : W := mkw 0x00000000820d0558 0x400000000820d055 0x70010203863f8fff 0x970010203863f8ff

def z453 : W := mkw 0x0ddf800050300000 0x00ddf80005030000 0x8fffe0007838000d 0xf8fffe0007838000

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0x218000000600000c 0xb218000000600000

def z455 : W := mkw 0x02201e000840e802 0x002201e000840e80 0xbe601e0079c0fc0e 0xfbe601e0079c0fc0

def z456 : W := mkw 0x16367e5dc0e33cc4 0x216367e5dc0e33cc 0xfe7ffe7fc1e77cc7 0xffe7ffe7fc1e77cc

def z457 : W := mkw 0x0b605f0900000000 0x00b605f090000000 0x4fe7ff9f80000003 0xf4fe7ff9f8000000

def z458 : W := mkw 0x1020660900c22804 0x21020660900c2280 0x0060e00001c00000 0x00060e00001c0000

def z459 : W := mkw 0x5ffddfff80413cc0 0x25ffddfff80413cc 0x5fffffff80007cc3 0xf5fffffff80007cc

def z460 : W := mkw 0x4ffddffb80010440 0x04ffddffb8001044 0x7fffffff80270cc7 0xf7fffffff80270cc

def z461 : W := mkw 0x00000054000010a0 0x800000054000010a 0x4000007c000000f0 0x04000007c000000f

def z462 : W := mkw 0x1000200080c32c44 0x21000200080c32c4 0x2000000001c70c00 0x02000000001c70c0

def z463 : W := mkw 0x008900a200000000 0x0008900a20000000 0x519913e3803880ff 0xb519913e3803880f

def z464 : W := mkw 0x000000000840ea03 0x0000000000840ea0 0x100000000000ff00 0x0100000000000ff0

def z465 : W := mkw 0x1022660dc2ef3ddc 0x61022660dc2ef3dd 0xf067ee1fc7ffffff 0xdf067ee1fc7fffff

def z466 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x419911e3863f83f9 0x2419911e3863f83f

def z467 : W := mkw 0x0000000000000000 0x0000000000000000 0xa060000041c00004 0xda060000041c0000

def z468 : W := mkw 0x09c900a2a70d0558 0x409c900a2a70d055 0xfff913e3ffff8fff 0xffff913e3ffff8ff

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0x2001000000270005 0x9200100000027000

def z470 : W := mkw 0x0020060000000000 0x0002006000000000 0x00600e0000000002 0xd00600e000000000

def z471 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x4e7efc7c00000003 0x74e7efc7c0000000

def z472 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000006008f0c 0x03000000006008f0

def z473 : W := mkw 0x2f56b8547db2d0a6 0x82f56b8547db2d0a 0x8e66ec1c79c07000 0x48e66ec1c79c0700

def z474 : W := mkw 0x29c9a0a2a78f055c 0x429c9a0a2a78f055 0x71f9f3e387ff8fff 0xb71f9f3e387ff8ff

def z475 : W := mkw 0x2be9bf002fceea0f 0x02be9bf002fceea0 0xbfe1ff807fc7ff0e 0xfbfe1ff807fc7ff0

def z476 : W := mkw 0x2fdfb9007fbec20f 0x02fdfb9007fbec20 0xaffff1807fff830d 0xfaffff1807fff830

def z477 : W := mkw 0x02201fa28841ef53 0x402201fa28841ef5 0x50001fe38000fff2 0x050001fe38000fff

def z478 : W := mkw 0x000000a200000000 0x0000000a20000000 0x400013e380000002 0x0400013e38000000

def z479 : W := mkw 0x0f761f007d70ea03 0x00f761f007d70ea0 0xbffe1f807ff8ff0f 0xfbffe1f807ff8ff0

def z480 : W := mkw 0x2ddfa00075b20004 0x02ddfa00075b2000 0x8fffe00079c00001 0xf8fffe00079c0000

def z481 : W := mkw 0x0000000000000000 0x0000000000000000 0x0067e00000000001 0xd0067e0000000000

def z482 : W := mkw 0x069d18f29a1dc57a 0xc069d18f29a1dc57 0x7f9913e3be3f8fff 0xb7f9913e3be3f8ff

def z483 : W := mkw 0x020018002d40ea03 0x0020018002d40ea0 0xbe001c007fc0ff0e 0x7be001c007fc0ff0

def z484 : W := mkw 0x06345e5900000000 0x006345e590000000 0x4e7ffe7f80000003 0xf4e7ffe7f8000000

def z485 : W := mkw 0x00020004da3dd5fa 0xc00020004da3dd5f 0xb00000007e3ffffc 0x0b00000007e3ffff

def z486 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x70190263803f0cf7 0x970190263803f0cf

def z487 : W := mkw 0x42205ffb80010550 0x442205ffb8001055 0x50001fff80008ff2 0x050001fff80008ff

def z488 : W := mkw 0x2ddfa000f7bf055c 0x42ddfa000f7bf055 0xbfffe0007fff8ffd 0xfbfffe0007fff8ff

def z489 : W := mkw 0x0002000440201080 0x0000200044020108 0x4006001c002000c1 0x04006001c002000c

def z490 : W := mkw 0x0ddd80a2820d0558 0x40ddd80a2820d055 0x7ffff3e3863f8fff 0xf7ffff3e3863f8ff

def z491 : W := mkw 0x0002000440201080 0x0000200044020108 0x80060c1c40007000 0x480060c1c4000700

def z492 : W := mkw 0x2d54800035100000 0x02d5480003510000 0x0e00000038000000 0x00e0000003800000

def z493 : W := mkw 0x000000000800c002 0x0000000000800c00 0x900000007800f00c 0x0900000007800f00

def z494 : W := mkw 0x0089000000000000 0x0008900000000000 0x0199000000000001 0xb019900000000000

def z495 : W := mkw 0x000200047d70faa3 0x8000200047d70faa 0xb00000007ff8fffc 0x0b00000007ff8fff

def z496 : W := mkw 0x20002000278e000c 0x020002000278e000 0x2000000007c70000 0x02000000007c7000

def z497 : W := mkw 0x1b627f0d6de2fa87 0x21b627f0d6de2fa8 0x8e66ec1c79c07000 0x48e66ec1c79c0700

def z498 : W := mkw 0x0b601f00af4def5b 0x40b601f00af4def5 0xbfe01f807ffffffe 0xfbfe01f807ffffff

def z499 : W := mkw 0x1000600980830444 0x2100060098083044 0x0001e00380070000 0x00001e0038007000

def z500 : W := mkw 0x0b621f047d70faa3 0x80b621f047d70faa 0xbfe01f807ff8fffe 0xfbfe01f807ff8fff

def z501 : W := mkw 0x1020660980c32c44 0x21020660980c32c4 0x6067ee1f81c70c03 0xd6067ee1f81c70c0

def z502 : W := mkw 0x096007002d40ea03 0x0096007002d40ea0 0xb1e003807fc0ff0c 0x8b1e003807fc0ff0

def z503 : W := mkw 0x0b601f0000402800 0x00b601f000040280 0xbfe01f8041c07c06 0xfbfe01f8041c07c0

def z504 : W := mkw 0x469fd8ff5830d0a2 0x8469fd8ff5830d0a 0xde1ffc7ff838f0ff 0x7de1ffc7ff838f0f

def z505 : W := mkw 0x1beb7fafefefffdf 0x61beb7fafefefffd 0xffffffffffffffff 0xffffffffffffffff

def z506 : W := mkw 0x0be91fa200000000 0x00be91fa20000000 0x4ff91fe380000003 0xf4ff91fe38000000

def z507 : W := mkw 0x049f00a2d23d0558 0x4049f00a2d23d055 0xff9f13e3fe3f8fff 0xfff9f13e3fe3f8ff

def z508 : W := mkw 0x10022004c2ef3ddc 0x610022004c2ef3dd 0xb000000047fffffc 0x0b000000047fffff

def z509 : W := mkw 0x249fa0a2d2bf055c 0x4249fa0a2d2bf055 0x401fe063803f00f1 0x0401fe063803f00f

def z510 : W := mkw 0x46365fff5830d0a2 0x846365fff5830d0a 0xde1e1ffff838f0ff 0x7de1e1ffff838f0f

def z511 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x7fffffff86008f0f 0xf7fffffff86008f0

def z512 : W := mkw 0x0d56000075300000 0x00d5600007530000 0xaffe00007ff8000d 0xfaffe00007ff8000

def z513 : W := mkw 0x2ddfa00052be000c 0x02ddfa00052be000 0x0fffe000003f0001 0xf0fffe000003f000

def z514 : W := mkw 0x4be9dffb00000000 0x04be9dffb0000000 0x41e1ffff80000002 0x841e1ffff8000000

def z515 : W := mkw 0x2ddfa05477be10ac 0x82ddfa05477be10a 0xefffe07c7fff00fd 0xfefffe07c7fff00f

def z516 : W := mkw 0x0020460900402800 0x0002046090040280 0xf067ee1fc1c07c07 0xdf067ee1fc1c07c0

def z517 : W := mkw 0x069d18f2820d0558 0x4069d18f2820d055 0x7f9f1fff863f8fff 0xf7f9f1fff863f8ff

def z518 : W := mkw 0x6dffe7ab77be000c 0x06dffe7ab77be000 0xafffe383ffff000d 0xfafffe383ffff000

def z519 : W := mkw 0x20000000371c0008 0x020000000371c000 0x000000003e180008 0x0000000003e18000

def z520 : W := mkw 0x1022660d40e23884 0x21022660d40e2388 0xd066ec1c41e070c7 0x5d066ec1c41e070c

def z521 : W := mkw 0x4ffddffb820d0558 0x44ffddffb820d055 0x4fffffff803f00f3 0xf4fffffff803f00f

def z522 : W := mkw 0x0020060000402800 0x0002006000040280 0x2060020001c00c00 0x82060020001c00c0

def z523 : W := mkw 0x04160054503010a0 0x804160054503010a 0x0006001c00000000 0x00006001c0000000

def z524 : W := mkw 0x0614185000000000 0x0061418500000000 0x0e060c1c00000000 0x40e060c1c0000000

def z525 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0xf0060c1c41e77cc7 0x5f0060c1c41e77cc

def z526 : W := mkw 0x0ffd9f0000000000 0x00ffd9f000000000 0x0fffff8000000003 0xf0fffff800000000

def z527 : W := mkw 0x06161854503010a0 0x806161854503010a 0x4e1e1c7c003800f3 0x74e1e1c7c003800f

def z528 : W := mkw 0x1022660d40e23884 0x21022660d40e2388 0xb066ee1c41c07c06 0xdb066ee1c41c07c0

def z529 : W := mkw 0x2089a000028e000c 0x02089a000028e000 0x0001e00000070000 0x00001e0000007000

def z530 : W := mkw 0x008900a2020c0118 0x4008900a2020c011 0x0018006000180030 0x0001800600018003

def z531 : W := mkw 0x020019000800c203 0x0020019000800c20 0x0000118000008300 0x0000011800000830

def z532 : W := mkw 0x02201f000840ea03 0x002201f000840ea0 0x00000c0000007000 0x000000c000000700

def z533 : W := mkw 0x10a966ab82cf2d5c 0x610a966ab82cf2d5 0x21e1e38387c70f00 0x821e1e38387c70f0

def z534 : W := mkw 0x0416000050300000 0x0041600005030000 0x001e000000380001 0x0001e00000038000

def z535 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xb061e203c1e77cc4 0x8b061e203c1e77cc

def z536 : W := mkw 0x29cba00077be000c 0x029cba00077be000 0xa1e1e0007fff000c 0x8a1e1e0007fff000

def z537 : W := mkw 0x29c9a0a2a78f055c 0x429c9a0a2a78f055 0x21e1e38387c70f00 0x821e1e38387c70f0

def z538 : W := mkw 0x1b623f04ede3fec7 0x21b623f04ede3fec 0xbfe01f807fe7ffce 0xfbfe01f807fe7ffc

def z539 : W := mkw 0x0002000440201080 0x0000200044020108 0xd01e1c7c4038f0ff 0x7d01e1c7c4038f0f

def z540 : W := mkw 0x020018000800c002 0x0020018000800c00 0x8e000c0078007000 0x48e000c007800700

def z541 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0x8e1e0c1c7838700d 0x78e1e0c1c7838700

def z542 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0x21ffe00007ff0001 0x821ffe00007ff000

def z543 : W := mkw 0x29e9a70027ce2a0d 0x029e9a70027ce2a0 0x21e1e38007c70f00 0x821e1e38007c70f0

def z544 : W := mkw 0x59e9e7ab80c32c44 0x259e9e7ab80c32c4 0x21e1e38381c70c00 0x821e1e38381c70c0

def z545 : W := mkw 0x1020660980c32c44 0x21020660980c32c4 0x7061e20381e70cc7 0x97061e20381e70cc

def z546 : W := mkw 0x0200185000000000 0x0020018500000000 0x40001c7c00000002 0x040001c7c0000000

def z547 : W := mkw 0x061618505830c022 0x8061618505830c02 0x8e1e10607838803d 0x78e1e10607838803

def z548 : W := mkw 0x549fe0ffc0a314c4 0x2549fe0ffc0a314c 0x401fe07f802700c1 0x0401fe07f802700c

def z549 : W := mkw 0x008900a200000000 0x0008900a20000000 0x0181038380000000 0x8018103838000000

def z550 : W := mkw 0x0b4019002d00c203 0x00b4019002d00c20 0x9f801d807e00f30e 0x79f801d807e00f30

def z551 : W := mkw 0x00a906a2824d2d58 0x400a906a2824d2d5 0xf1f91fe3c7ffffff 0xff1f91fe3c7fffff

def z552 : W := mkw 0x2ffd9f003f5cea0b 0x02ffd9f003f5cea0 0xbff81f807fd8ff0e 0xfbff81f807fd8ff0

def z553 : W := mkw 0x649fe0fb52be000c 0x0649fe0fb52be000 0x401fe07f803f0001 0x0401fe07f803f000

def z554 : W := mkw 0x0ddd8000020c0008 0x00ddd8000020c000 0x2fffe000063f000d 0xf2fffe000063f000

def z555 : W := mkw 0x0414000010100000 0x0041400001010000 0x0e18000038180008 0x20e1800003818000

def z556 : W := mkw 0x020218544820d0a2 0x8020218544820d0a 0xd0061c7c4020f0f7 0x5d0061c7c4020f0f

def z557 : W := mkw 0x020018000800c002 0x0020018000800c00 0x10001c000000f002 0x010001c000000f00

def z558 : W := mkw 0x0b4018002d00c002 0x00b4018002d00c00 0xbfe01c007fc0f00e 0xfbfe01c007fc0f00

def z559 : W := mkw 0x1002600dc0e33cc4 0x21002600dc0e33cc 0xf007e01fc1e77cc5 0x0f007e01fc1e77cc

def z560 : W := mkw 0x4fdf99f65830d0a2 0x84fdf99f65830d0a 0xdf9e1dfc7838f0ff 0x7df9e1dfc7838f0f

def z561 : W := mkw 0x4ffddffb020c0008 0x04ffddffb020c000 0x6fffffff863f000f 0xf6fffffff863f000

def z562 : W := mkw 0x000000002d00c203 0x0000000002d00c20 0x000000003e008308 0x0000000003e00830

def z563 : W := mkw 0x1002600dc0a314c4 0x21002600dc0a314c 0xd007ec1fc02770c7 0x5d007ec1fc02770c

def z564 : W := mkw 0x108b60afc2af15dc 0x6108b60afc2af15d 0x401fe07f803f00f1 0x0401fe07f803f00f

def z565 : W := mkw 0x049f0000523c0008 0x0049f0000523c000 0xaf9f00007e3f000d 0xfaf9f00007e3f000

def z566 : W := mkw 0x1022660dede3fec7 0x21022660dede3fec 0xf067ee1fffe7ffcf 0xdf067ee1fffe7ffc

def z567 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180118006008308 0x2018011800600830

def z568 : W := mkw 0x20022000f7bf055c 0x420022000f7bf055 0xb00000007fff8ffc 0x0b00000007fff8ff

def z569 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xfffff0607fff80ff 0xffffff0607fff80f

def z570 : W := mkw 0x0b601fa2ad41ef53 0x40b601fa2ad41ef5 0xffe01fe3ffc0fffe 0xfffe01fe3ffc0fff

def z571 : W := mkw 0x0940000025000000 0x0094000002500000 0x21e0000007c00000 0x821e0000007c0000

def z572 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x0fe6ff9c00000002 0xf0fe6ff9c0000000

def z573 : W := mkw 0x020018000800c002 0x0020018000800c00 0xbf801f807e00ff0e 0xfbf801f807e00ff0

def z574 : W := mkw 0x4be9dfab00000000 0x04be9dfab0000000 0x0fe1ff8380000002 0xf0fe1ff838000000

def z575 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0x2fe013803fc08f08 0xa2fe013803fc08f0

def z576 : W := mkw 0x008900a2020c0118 0x4008900a2020c011 0x319813e006188f3e 0xb319813e006188f3

def z577 : W := mkw 0x020018540800d0a2 0x8020018540800d0a 0xde001c7c7800f0fe 0x7de001c7c7800f0f

def z578 : W := mkw 0x4f76df5d5830d0a2 0x84f76df5d5830d0a 0xde7efc7c7838f0ff 0x7de7efc7c7838f0f

def z579 : W := mkw 0x7ffffffff7ff3ccc 0x27ffffffff7ff3cc 0xffffffffffff7ccf 0xfffffffffffff7cc

def z580 : W := mkw 0x00890000820d0558 0x400890000820d055 0x31990000063f8ffd 0xb31990000063f8ff

def z581 : W := mkw 0x00020004c02114c0 0x000020004c02114c 0xf0070e1fc0277cc7 0xdf0070e1fc0277cc

def z582 : W := mkw 0x09e907a2a74d2f59 0x409e907a2a74d2f5 0x21e1038387c70f00 0x821e1038387c70f0

def z583 : W := mkw 0x061418501810c022 0x8061418501810c02 0x9e181c607818f03e 0x79e181c607818f03

def z584 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x419913e3803f00f3 0xb419913e3803f00f

def z585 : W := mkw 0x5fffffffd8f3fce6 0xa5fffffffd8f3fce 0xfffffffff9fffcff 0xffffffffff9fffcf

def z586 : W := mkw 0x020018000800c002 0x0020018000800c00 0xde181c607838f0ff 0x7de181c607838f0f

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000020000000c06 0x93000020000000c0

def z588 : W := mkw 0x2ddfa0a2f7bf055c 0x42ddfa0a2f7bf055 0xefffe063ffff00fd 0xfefffe063ffff00f

def z589 : W := mkw 0x00000000820d0558 0x400000000820d055 0x2000000006070f00 0x02000000006070f0

def z590 : W := mkw 0x0b4019002d00c203 0x00b4019002d00c20 0x3f8013803e008f0e 0xb3f8013803e008f0

def z591 : W := mkw 0x12227e0dc8e3fcc6 0x212227e0dc8e3fcc 0xfe67fe1ff9e7fccf 0xffe67fe1ff9e7fcc

def z592 : W := mkw 0x1962670de5e33ec5 0x21962670de5e33ec 0xf1e7ef9fc7e77fc7 0xdf1e7ef9fc7e77fc

def z593 : W := mkw 0x094000002d40ea03 0x0094000002d40ea0 0xbfe000007fc0ff0c 0xfbfe000007fc0ff0

def z594 : W := mkw 0x0b4019002d00c203 0x00b4019002d00c20 0x0e00000038000000 0x00e0000003800000

def z595 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xaf9800007fff000c 0x2af9800007fff000

def z596 : W := mkw 0x069f18f65a3cd1ba 0xc069f18f65a3cd1b 0xdf9e1dfc7e38f3ff 0x7df9e1dfc7e38f3f

def z597 : W := mkw 0x0000200000820004 0x0000020000082000 0x2061e00001c70000 0x82061e00001c7000

def z598 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x501913e3803f8ff3 0x0501913e3803f8ff

def z599 : W := mkw 0x0020460980010440 0x0002046098001044 0x7067ee1f80270cc7 0xd7067ee1f80270cc

def z600 : W := mkw 0x6fffff5977be000c 0x06fffff5977be000 0xafffec1c7fff000d 0xfafffec1c7fff000

def z601 : W := mkw 0x2940a00025820004 0x02940a0002582000 0x0060e00001c00000 0x00060e00001c0000

def z602 : W := mkw 0x108b20a6c2ef3ddc 0x6108b20a6c2ef3dd 0xf19913e3c7ffffff 0xbf19913e3c7fffff

def z603 : W := mkw 0x0000000025402a01 0x00000000025402a0 0x2000000007c00f00 0x02000000007c00f0

def z604 : W := mkw 0x52227fffc0e33cc4 0x252227fffc0e33cc 0xf067ffffc1e77cc7 0xdf067ffffc1e77cc

def z605 : W := mkw 0x0fdf98545830d0a2 0x80fdf98545830d0a 0xdffffc7c7838f0ff 0xfdffffc7c7838f0f

def z606 : W := mkw 0x4fdd99f200000000 0x04fdd99f20000000 0x4f9913e380000003 0xb4f9913e38000000

def z607 : W := mkw 0x10a966ab82cf2d5c 0x610a966ab82cf2d5 0x71f9f3e387ff8fff 0xb71f9f3e387ff8ff

def z608 : W := mkw 0x0be91fa2820d0558 0x40be91fa2820d055 0x7ff91fe3863f8fff 0xf7ff91fe3863f8ff

def z609 : W := mkw 0x061618547d70faa3 0x8061618547d70faa 0xfe1e1c7c7ff8ffff 0x7fe1e1c7c7ff8fff

def z610 : W := mkw 0x4fffdfff5830d0a2 0x84fffdfff5830d0a 0xcffffffff8007003 0xfcffffffff800700

def z611 : W := mkw 0x2fffbfa2ffffef5f 0x42fffbfa2ffffef5 0xffffffe3ffffffff 0xfffffffe3fffffff

def z612 : W := mkw 0x0416000450301080 0x0041600045030108 0xde1e0c1c783870cf 0x7de1e0c1c783870c

def z613 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xbe600c007fc0ff0c 0x4be600c007fc0ff0

def z614 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x718113e386078ff2 0x8718113e386078ff

def z615 : W := mkw 0x0000000080010440 0x0000000008001044 0x40010003802700c1 0x040010003802700c

def z616 : W := mkw 0x4ffddffb80010550 0x44ffddffb8001055 0x5fffffff80008ff3 0xf5fffffff80008ff

def z617 : W := mkw 0x39ebe60de7ef3ccc 0x239ebe60de7ef3cc 0xf1e7ee1fc7e77cc7 0xdf1e7ee1fc7e77cc

def z618 : W := mkw 0x1b627f0dc0e33cc4 0x21b627f0dc0e33cc 0xffe7ff9fc1e77cc7 0xfffe7ff9fc1e77cc

def z619 : W := mkw 0x3dffe60d77fe388c 0x23dffe60d77fe388 0xafffec1c7fff700d 0xfafffec1c7fff700

def z620 : W := mkw 0x1436665dd0f33ce4 0xa1436665dd0f33ce 0xf07fee7fc1ff7cf7 0xdf07fee7fc1ff7cf

def z621 : W := mkw 0x4fdd99f21810c022 0x84fdd99f21810c02 0x0f9811e038188038 0x20f9811e03818803

def z622 : W := mkw 0x069d18f200000000 0x0069d18f20000000 0x4f9f1fff80000003 0xf4f9f1fff8000000

def z623 : W := mkw 0x000000002d40ea03 0x0000000002d40ea0 0x8000000079c07000 0x08000000079c0700

def z624 : W := mkw 0x06365e5d5830d0a2 0x806365e5d5830d0a 0xde7ffe7ff838f0ff 0xfde7ffe7ff838f0f

def z625 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xde061c7c7800f0f2 0x4de061c7c7800f0f

def z626 : W := mkw 0x0000000025000000 0x0000000002500000 0xa00000007fc0000c 0x0a00000007fc0000

def z627 : W := mkw 0x1020460d80413cc0 0x21020460d80413cc 0xf0600e1fc1c07cc6 0xdf0600e1fc1c07cc

def z628 : W := mkw 0x10ab66afc2ef3ddc 0x610ab66afc2ef3dd 0xf1e7ef9fc7e77fc7 0xdf1e7ef9fc7e77fc

def z629 : W := mkw 0x0bc919a22f0cc31b 0x40bc919a22f0cc31 0x0f9811e03e188338 0x20f9811e03e18833

def z630 : W := mkw 0x2ddd8000371c0008 0x02ddd8000371c000 0x2f9900003e3f000d 0xb2f9900003e3f000

def z631 : W := mkw 0x2f56b8547db2d0a6 0x82f56b8547db2d0a 0xde7efc7c79f8f0ff 0x7de7efc7c79f8f0f

def z632 : W := mkw 0x000000001810c022 0x8000000001810c02 0x0000000038188038 0x0000000003818803

def z633 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x31810383863f8ffc 0x831810383863f8ff

def z634 : W := mkw 0x19606709a5c32e45 0x219606709a5c32e4 0x21e1e38387c70f00 0x821e1e38387c70f0

def z635 : W := mkw 0x061618f6d831d5f2 0xc061618f6d831d5f 0xde1e1ffff838ffff 0x7de1e1ffff838fff

def z636 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x619903e3863f0ff1 0x8619903e3863f0ff

def z637 : W := mkw 0x2ddfa0007ffeea0f 0x02ddfa0007ffeea0 0xbfffe0007fffff0d 0xfbfffe0007fffff0

def z638 : W := mkw 0x008900a2020c0008 0x0008900a2020c000 0x619913e3863f000f 0xb619913e3863f000

def z639 : W := mkw 0x00000000820d0558 0x400000000820d055 0x70181060063f8fff 0x370181060063f8ff

def z640 : W := mkw 0x1b627f0d6de2fa87 0x21b627f0d6de2fa8 0xbfe6ff9c7fc0ff0e 0xfbfe6ff9c7fc0ff0

def z641 : W := mkw 0x2416a00050b20004 0x02416a00050b2000 0x0006e00000000000 0x00006e0000000000

def z642 : W := mkw 0x0940000025000000 0x0094000002500000 0x0f8000003e000008 0x20f8000003e00000

def z643 : W := mkw 0x0022260040e22804 0x00022260040e2280 0xb067ee0041e77c07 0xdb067ee0041e77c0

def z644 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0x5007ee1f80277cc3 0x05007ee1f80277cc

def z645 : W := mkw 0x2fdfb8547fbed0ae 0x82fdfb8547fbed0a 0xafffec1c7fff700d 0xfafffec1c7fff700

def z646 : W := mkw 0x069f18545a3cd0aa 0x8069f18545a3cd0a 0xff9f1c7c7e3ff0ff 0xfff9f1c7c7e3ff0f

def z647 : W := mkw 0x0f741f502d40ea03 0x00f741f502d40ea0 0xfffe1ffc7fc0ff0f 0xffffe1ffc7fc0ff0

def z648 : W := mkw 0x249fa0a2d2bf055c 0x4249fa0a2d2bf055 0x719ff3e3863f8fff 0xb719ff3e3863f8ff

def z649 : W := mkw 0x0b601f000800c002 0x00b601f000800c00 0x9fe01f807800f00e 0xf9fe01f807800f00

def z650 : W := mkw 0x102046af80413dd0 0x6102046af80413dd 0x50001fff8000fff2 0x050001fff8000fff

def z651 : W := mkw 0x208b20a2f7bf055c 0x4208b20a2f7bf055 0xf19913e3ffff8fff 0xbf19913e3ffff8ff

def z652 : W := mkw 0x0fff1ff6ff7dfffb 0xc0fff1ff6ff7dfff 0xffff1fffffffffff 0xfffff1ffffffffff

def z653 : W := mkw 0x0000000080010440 0x0000000008001044 0x7181138386278fcf 0xb7181138386278fc

def z654 : W := mkw 0x102266afc0e33dd4 0x6102266afc0e33dd 0xf067ffffc1e7fff7 0xdf067ffffc1e7fff

def z655 : W := mkw 0x0f5618547d30d0a2 0x80f5618547d30d0a 0xfffe1c7c7ff8f0ff 0xffffe1c7c7ff8f0f

def z656 : W := mkw 0x2ddfa000f7bf044c 0x02ddfa000f7bf044 0xffffe203ffff0ccf 0xfffffe203ffff0cc

def z657 : W := mkw 0x000000002d40ea03 0x0000000002d40ea0 0xb18013807fc0ff0e 0xbb18013807fc0ff0

def z658 : W := mkw 0x249fa05452be10ac 0x8249fa05452be10a 0x401fe07c003f00f1 0x0401fe07c003f00f

def z659 : W := mkw 0x0022460d40201080 0x00022460d4020108 0xd067ee1fc02070c7 0xdd067ee1fc02070c

def z660 : W := mkw 0x49e9c7ab820d0558 0x449e9c7ab820d055 0x21e1e38386070f00 0x821e1e38386070f0

def z661 : W := mkw 0x2dffa70077fe2a0d 0x02dffa70077fe2a0 0xafffe3807fff0f0d 0xfafffe3807fff0f0

def z662 : W := mkw 0x0960070000000000 0x0096007000000000 0x01e0038000000000 0x801e003800000000

def z663 : W := mkw 0x02201f000840ea03 0x002201f000840ea0 0x9e001f807800ff0e 0x79e001f807800ff0

def z664 : W := mkw 0x2fdfb85077be000c 0x02fdfb85077be000 0xeffffc7c7fff000f 0xfeffffc7c7fff000

def z665 : W := mkw 0x2002200077be000c 0x02002200077be000 0xa067e0007fff000d 0xda067e0007fff000

def z666 : W := mkw 0x2fffbf547ffefaaf 0x82fffbf547ffefaa 0xfffffffc7fffffff 0xffffffffc7ffffff

def z667 : W := mkw 0x349fe00dd2bf14cc 0x2349fe00dd2bf14c 0x401fe01f803f00c1 0x0401fe01f803f00c

def z668 : W := mkw 0x008b00a6c22d15d8 0x4008b00a6c22d15d 0xf19f1fffc63fffff 0xff19f1fffc63ffff

def z669 : W := mkw 0x10226609c0e32c44 0x210226609c0e32c4 0xa067e203c1e70c05 0xda067e203c1e70c0

def z670 : W := mkw 0x449dc0fb820d0558 0x4449dc0fb820d055 0x401fe07f803f00f1 0x0401fe07f803f00f

def z671 : W := mkw 0x5fffffffc2ef3ddc 0x65fffffffc2ef3dd 0xffffffffc7ffffff 0xfffffffffc7fffff

def z672 : W := mkw 0x0be91fa22d40ea03 0x00be91fa22d40ea0 0xfff91fe3ffc0ff0f 0xffff91fe3ffc0ff0

def z673 : W := mkw 0x39e9e609a7cf2c4c 0x239e9e609a7cf2c4 0x21e1e20387c70c00 0x821e1e20387c70c0

def z674 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0x8fe01d807fc0f308 0x68fe01d807fc0f30

def z675 : W := mkw 0x028918f68a0dd5fa 0xc028918f68a0dd5f 0x71991fff863fffff 0xb71991fff863ffff

def z676 : W := mkw 0x0b601f542d40faa3 0x80b601f542d40faa 0xffe01ffc7fc0fffe 0xfffe01ffc7fc0fff

def z677 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180138000000002 0xb018013800000000

def z678 : W := mkw 0x000000040800d0a2 0x8000000040800d0a 0x100000000000f0f0 0x0100000000000f0f

def z679 : W := mkw 0x6ffffffb7ffeea0f 0x06ffffffb7ffeea0 0xffffffffffffff0f 0xfffffffffffffff0

def z680 : W := mkw 0x000000a200000110 0x4000000a20000011 0x000011e000008330 0x0000011e00000833

def z681 : W := mkw 0x020018000800c002 0x0020018000800c00 0x0e00100038008008 0x20e0010003800800

def z682 : W := mkw 0x1022660d40e23884 0x21022660d40e2388 0xa067ec1c41e77005 0xda067ec1c41e7700

def z683 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xb066ec1c41e77cc4 0x4b066ec1c41e77cc

def z684 : W := mkw 0x2d56a00075b20004 0x02d56a00075b2000 0x8e7ee00079f8000d 0x78e7ee00079f8000

def z685 : W := mkw 0x49e9c7ab820d0558 0x449e9c7ab820d055 0x71f9f3e3863f8fff 0xb71f9f3e3863f8ff

def z686 : W := mkw 0x1dffe60dc0e33cc4 0x21dffe60dc0e33cc 0xffffee1fc1e77cc7 0xfffffee1fc1e77cc

def z687 : W := mkw 0x069f18f65830d0a2 0x8069f18f65830d0a 0xdf9f1ffff838f0ff 0xfdf9f1ffff838f0f

def z688 : W := mkw 0x000000a2820d0558 0x4000000a2820d055 0x700013e3863f8ffe 0x0700013e3863f8ff

def z689 : W := mkw 0x4fdd99f2820d0558 0x44fdd99f2820d055 0x7f9913e3863f8fff 0xb7f9913e3863f8ff

def z690 : W := mkw 0x000000a280010550 0x4000000a28001055 0x0000038380000f00 0x00000038380000f0

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000138000008f02 0x01000138000008f0

def z692 : W := mkw 0x2fdfb8007fbec00e 0x02fdfb8007fbec00 0xbffffc007ffff00f 0xfbffffc007ffff00

def z693 : W := mkw 0x1f767f5dfdf3fee7 0xa1f767f5dfdf3fee 0xffffffffffffffff 0xffffffffffffffff

def z694 : W := mkw 0x261638547fbed0ae 0x8261638547fbed0a 0xfe1e1c7c7ffff0ff 0x7fe1e1c7c7ffff0f

def z695 : W := mkw 0x3022660df7ff3ccc 0x23022660df7ff3cc 0xf067ee1fffff7ccf 0xdf067ee1fffff7cc

def z696 : W := mkw 0x00000000af4def5b 0x400000000af4def5 0xb00000007ffffffc 0x0b00000007ffffff

def z697 : W := mkw 0x0940010025000201 0x0094001002500020 0x0180018006000300 0x0018001800600030

def z698 : W := mkw 0x1b607f09adc3ee47 0x21b607f09adc3ee4 0xbfe1ff83ffc7ff0e 0xfbfe1ff83ffc7ff0

def z699 : W := mkw 0x0414000000000000 0x0041400000000000 0x0e1e000000000001 0x70e1e00000000000

def z700 : W := mkw 0x0f5419503d10c223 0x80f5419503d10c22 0x0f9811e03e188338 0x20f9811e03e18833

def z701 : W := mkw 0x0fdd985000000000 0x00fdd98500000000 0x4ffffc7c00000003 0xf4ffffc7c0000000

def z702 : W := mkw 0x06361f545870faa3 0x806361f545870faa 0xde1e1ffc7838ffff 0x7de1e1ffc7838fff

def z703 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0x8ffee0007fd80008 0x68ffee0007fd8000

def z704 : W := mkw 0x1020460980412c40 0x21020460980412c4 0x0000020380000c00 0x00000020380000c0

def z705 : W := mkw 0x0b621f046d60fa83 0x00b621f046d60fa8 0xffe61f9c7fe0ffcf 0xfffe61f9c7fe0ffc

def z706 : W := mkw 0x108b60afc2af15dc 0x6108b60afc2af15d 0x719ff3ff863f8fff 0xb719ff3ff863f8ff

def z707 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xbfffe2007fff0c0f 0xfbfffe2007fff0c0

def z708 : W := mkw 0x46bddffb00000000 0x046bddffb0000000 0x419fffff80000003 0xb419fffff8000000

def z709 : W := mkw 0x449dc0fb2d40ea03 0x0449dc0fb2d40ea0 0xf01fe07fffc0ff0d 0x0f01fe07fffc0ff0

def z710 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf07ffe7fc1e77cc7 0xff07ffe7fc1e77cc

def z711 : W := mkw 0x2942200077be000c 0x02942200077be000 0xafe7e0007fff000d 0xfafe7e0007fff000

def z712 : W := mkw 0x008940ab00000000 0x0008940ab0000000 0x419ff3ff80000003 0xb419ff3ff8000000

def z713 : W := mkw 0x16347e5998d3ec66 0xa16347e5998d3ec6 0x2e79f263b9df8c38 0xa2e79f263b9df8c3

def z714 : W := mkw 0x29cba00067ae000c 0x029cba00067ae000 0xafe7e0007fe7000d 0xfafe7e0007fe7000

def z715 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xce1e1c7c783870f3 0x7ce1e1c7c783870f

def z716 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xfffff3e07fff8fff 0xffffff3e07fff8ff

def z717 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xde7ffc7c7838f0ff 0xfde7ffc7c7838f0f

def z718 : W := mkw 0x5fdfb9f6c0e33cc4 0x25fdfb9f6c0e33cc 0xbf9811e041e77cc4 0x2bf9811e041e77cc

def z719 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0xff9913e3fe3f8fff 0xfff9913e3fe3f8ff

def z720 : W := mkw 0x469dd8fb0800c002 0x0469dd8fb0800c00 0xde1ffc7ff800f00f 0x7de1ffc7ff800f00

def z721 : W := mkw 0x2ddfa0a277be011c 0x42ddfa0a277be011 0xeffff3e3ffff833f 0xfeffff3e3ffff833

def z722 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xde1f1e7ff838f0ff 0xfde1f1e7ff838f0f

def z723 : W := mkw 0x2ddfa0a277be011c 0x42ddfa0a277be011 0xafffe1807fff030d 0xfafffe1807fff030

def z724 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0xdfffffffc0007007 0xfdfffffffc000700

def z725 : W := mkw 0x469dd8fb1810c022 0x8469dd8fb1810c02 0x4e1ff07fb8188039 0x24e1ff07fb818803

def z726 : W := mkw 0x0020460900000000 0x0002046090000000 0xe067ee1fc1c00007 0xde067ee1fc1c0000

def z727 : W := mkw 0x0616385458b2d0a6 0x80616385458b2d0a 0xfe1e1c7c79fff0ff 0x7fe1e1c7c79fff0f

def z728 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xefffe203ffff000f 0xfefffe203ffff000

def z729 : W := mkw 0x62227ffb77be000c 0x062227ffb77be000 0xe0001fffffff000e 0x0e0001fffffff000

def z730 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4fe7ffff80000002 0xc4fe7ffff8000000

def z731 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xdf9e1dfc7e38f3ff 0x7df9e1dfc7e38f3f

def z732 : W := mkw 0x2ddfa05077be000c 0x02ddfa05077be000 0xefffe07c7fff000d 0xfefffe07c7fff000

def z733 : W := mkw 0x42205ffb0840ea03 0x042205ffb0840ea0 0xf067ffffc1c0ff07 0xdf067ffffc1c0ff0

def z734 : W := mkw 0x4ffddffb0800c002 0x04ffddffb0800c00 0xfffffffffe00ff0f 0xffffffffffe00ff0

def z735 : W := mkw 0x00a946ab00402800 0x000a946ab0040280 0xf1ffffffc7c0ff0f 0xff1ffffffc7c0ff0

def z736 : W := mkw 0x2ddda000379e000c 0x02ddda000379e000 0xaff9e0007fdf000c 0xfaff9e0007fdf000

def z737 : W := mkw 0x42205f5900000000 0x042205f590000000 0x4067ee1f80000003 0xd4067ee1f8000000

def z738 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0xefffffffffc07f03 0xfefffffffffc07f0

def z739 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0xf1f913e3c7ff8fff 0xff1f913e3c7ff8ff

def z740 : W := mkw 0x1b42790deda3d6c7 0x21b42790deda3d6c 0x4f87f19fbe2783c9 0x24f87f19fbe2783c

def z741 : W := mkw 0x49e9c7ab00000000 0x049e9c7ab0000000 0x01e7ef9f80000000 0xc01e7ef9f8000000

def z742 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xbfffe0007fff8f0d 0xfbfffe0007fff8f0

def z743 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xaffee0007fff000c 0x6affee0007fff000

def z744 : W := mkw 0x10022004fdf3fee7 0xa10022004fdf3fee 0xb00000007ffffffc 0x0b00000007ffffff

def z745 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x719813e3863f8ffe 0x2719813e3863f8ff

def z746 : W := mkw 0x2ddfa05477be10ac 0x82ddfa05477be10a 0xafffe01c7fff000d 0xfafffe01c7fff000

def z747 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0x8fffe0007fff0009 0x68fffe0007fff000

def z748 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0xb000000047e7ffcc 0x0b000000047e7ffc

def z749 : W := mkw 0x0020460900000000 0x0002046090000000 0x7067ee1f80000c07 0xd7067ee1f80000c0

def z750 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x419fe07f80000001 0xb419fe07f8000000

def z751 : W := mkw 0x0020460900000000 0x0002046090000000 0x0067ee1f80000000 0xc0067ee1f8000000

def z752 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf07fee1fc1ff7ccf 0xff07fee1fc1ff7cc

def z753 : W := mkw 0x4be9dfab00000000 0x04be9dfab0000000 0x4fe7ff9f80000003 0xf4fe7ff9f8000000

def z754 : W := mkw 0x3dfdc60db75d3cc8 0x23dfdc60db75d3cc 0x5f980e1fbe187cca 0x25f980e1fbe187cc

def z755 : W := mkw 0x0be91fa2af4def5b 0x40be91fa2af4def5 0xce790c63f9ff70f1 0x4ce790c63f9ff70f

def z756 : W := mkw 0x4f74dffb2d40ea03 0x04f74dffb2d40ea0 0xffe6ffffffc0ff0e 0xfffe6ffffffc0ff0

def z757 : W := mkw 0x4ffddffb00402a01 0x04ffddffb00402a0 0x4fffffff80000f03 0xf4fffffff80000f0

def z758 : W := mkw 0x2ddfa0a277be011c 0x42ddfa0a277be011 0xfffff1e07fff83ff 0xffffff1e07fff83f

def z759 : W := mkw 0x49ebc7af5830d0a2 0x849ebc7af5830d0a 0x91e1e383f838f0fc 0x891e1e383f838f0f

def z760 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x5fffffff800080f3 0xf5fffffff800080f

def z761 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xeffff0607fff000f 0xfeffff0607fff000

def z762 : W := mkw 0x4b605f592d40ea03 0x04b605f592d40ea0 0xbfe01f9c7fc0ff0e 0xfbfe01f9c7fc0ff0

def z763 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x401fe07f803800f1 0x0401fe07f803800f

def z764 : W := mkw 0x4f74dffb00000000 0x04f74dffb0000000 0x4e7effff80000003 0x74e7effff8000000

def z765 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x0e67ee1f80000000 0xc0e67ee1f8000000

def z766 : W := mkw 0x29cba00077be000c 0x029cba00077be000 0xafe1e0007fff000c 0xfafe1e0007fff000

def z767 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xafe01f807fc0ff08 0xeafe01f807fc0ff0

def z768 : W := mkw 0x449dc0fb020c0008 0x0449dc0fb020c000 0x619fe07f863f000d 0xb619fe07f863f000

def z769 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xafffe0007fff0001 0xcafffe0007fff000

def z770 : W := mkw 0x4ffddffb0800c002 0x04ffddffb0800c00 0xcffffffff8007003 0xfcffffffff800700

def z771 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0xce7fec7ff9c07001 0x4ce7fec7ff9c0700

def z772 : W := mkw 0x0020460900000000 0x0002046090000000 0xd067ee1fc0007007 0xdd067ee1fc000700

def z773 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z774 : W := mkw 0x10022004c0a314c4 0x210022004c0a314c 0xa000000041e700c4 0x0a000000041e700c

def z775 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x71fff3e3863f8fff 0xf71fff3e3863f8ff

def z776 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4fffec7f80000001 0xf4fffec7f8000000

def z777 : W := mkw 0x4dddc0fb00000000 0x04dddc0fb0000000 0x4e7fe07f80000001 0x44e7fe07f8000000

def z778 : W := mkw 0x49e9c7ab00000000 0x049e9c7ab0000000 0x41e7e39f80000001 0x841e7e39f8000000

def z779 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xfe67ee1ff9e77ccf 0xffe67ee1ff9e77cc

def z780 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0x6fffffffbfc08f0b 0xf6fffffffbfc08f0

def z781 : W := mkw 0x0be95fabaf4def5b 0x40be95fabaf4def5 0xffffffffffffffff 0xffffffffffffffff

def z782 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xbff81fe07fd8ff3e 0xfbff81fe07fd8ff3

def z783 : W := mkw 0x2ddfa10077be020d 0x02ddfa10077be020 0xafffe1807fff030d 0xfafffe1807fff030

def z784 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x319913e3863f8ffc 0xa319913e3863f8ff

def z785 : W := mkw 0x2ddfa05477be10ac 0x82ddfa05477be10a 0xfffff07c7fff80ff 0xffffff07c7fff80f

def z786 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xafffe0007fdf0008 0xeafffe0007fdf000

def z787 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x0fffef9f80000001 0xf0fffef9f8000000

def z788 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0xf018106041fffcff 0x3f018106041fffcf

def z789 : W := mkw 0x1b623f04efefffdf 0x61b623f04efefffd 0xbfe01f807ffffffe 0xfbfe01f807ffffff

def z790 : W := mkw 0x0414405900000000 0x0041440590000000 0x401fe07f80000001 0x0401fe07f8000000

def z791 : W := mkw 0x42205ffb00000000 0x042205ffb0000000 0x4007ffff80000003 0x04007ffff8000000

def z792 : W := mkw 0x2ddda000278e000c 0x02ddda000278e000 0xafffe0007fc7000d 0xfafffe0007fc7000

def z793 : W := mkw 0x4ffddffb0840ea03 0x04ffddffb0840ea0 0xffffffffc1c0ff07 0xfffffffffc1c0ff0

def z794 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xafe00f807fc07f0c 0xfafe00f807fc07f0

def z795 : W := mkw 0x2ddda000379e000c 0x02ddda000379e000 0x2ff9e0003fff000d 0xb2ff9e0003fff000

def z796 : W := mkw 0x061418500800c002 0x0061418500800c00 0xde1e1c7c7838f0ff 0x7de1e1c7c7838f0f

def z797 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0x7067ee1f81e77cc3 0x87067ee1f81e77cc

def z798 : W := mkw 0x4ffddffb10100020 0x84ffddffb1010002 0x4fffffff80180033 0xf4fffffff8018003

def z799 : W := mkw 0x00a946ab00000000 0x000a946ab0000000 0x41e7ef9f80000003 0xd41e7ef9f8000000

def z800 : W := mkw 0x2d56a00077be000c 0x02d56a00077be000 0xafe6e0007fff000c 0xfafe6e0007fff000

def z801 : W := mkw 0x4ffddf5900000000 0x04ffddf590000000 0x4fffee1f80000003 0xf4fffee1f8000000

def z802 : W := mkw 0x4fddd9fb2d00c203 0x04fddd9fb2d00c20 0x4f9ff1ffbe008309 0x24f9ff1ffbe00830

def z803 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xaffff1807fff830d 0xfaffff1807fff830

def z804 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0x8067ec1fc1c77000 0x48067ec1fc1c7700

def z805 : W := mkw 0x02205f0900000000 0x002205f090000000 0x4067ff9f80000003 0xd4067ff9f8000000

def z806 : W := mkw 0x0b605f092d40ea03 0x00b605f092d40ea0 0xffe01f9fffc0ff0e 0xfffe01f9fffc0ff0

def z807 : W := mkw 0x4f74df59820d0558 0x44f74df59820d055 0x3e66ec1c063f8ffc 0x43e66ec1c063f8ff

def z808 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xb067ee1fc1e77cc4 0xcb067ee1fc1e77cc

def z809 : W := mkw 0x069f18f6da3dd5fa 0xc069f18f6da3dd5f 0xaf870f9ffe077f00 0xcaf870f9ffe077f0

def z810 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xefffec1c7fff000f 0xfefffec1c7fff000

def z811 : W := mkw 0x0022660d40a21084 0x00022660d40a2108 0xf067ee1fc1e770c7 0xdf067ee1fc1e770c

def z812 : W := mkw 0x4ffddffb2d00c203 0x04ffddffb2d00c20 0x7fffffffbe008f0f 0xf7fffffffbe008f0

def z813 : W := mkw 0x061418541810d0a2 0x8061418541810d0a 0x5e1e1c7c3818f0fb 0x75e1e1c7c3818f0f

def z814 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0xdffffffff9c0f00f 0xfdffffffff9c0f00

def z815 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xfe7e1c7c79f8f0ff 0xffe7e1c7c79f8f0f

def z816 : W := mkw 0x1020660980c32c44 0x21020660980c32c4 0xf067ee1fc1c77c07 0xdf067ee1fc1c77c0

def z817 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xa067ee1fc1e77c05 0xda067ee1fc1e77c0

def z818 : W := mkw 0x1022660d40e23884 0x21022660d40e2388 0xe067ee1fc1e77007 0xde067ee1fc1e7700

def z819 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x41ffffff80000003 0x841ffffff8000000

def z820 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0xb001000041e77cc5 0x9b001000041e77cc

def z821 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xbffff0007fff800f 0xfbffff0007fff800

def z822 : W := mkw 0x0020460900000000 0x0002046090000000 0x6067ee1f80270007 0xd6067ee1f8027000

def z823 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x419ff1ff80000001 0x2419ff1ff8000000

def z824 : W := mkw 0x4ffddffb1810c022 0x84ffddffb1810c02 0xdffffffff818f03f 0xfdffffffff818f03

def z825 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0xb000000041fffcfc 0x0b000000041fffcf

def z826 : W := mkw 0x4ffddffb2f4cea0b 0x04ffddffb2f4cea0 0xffffffffffffff0f 0xfffffffffffffff0

def z827 : W := mkw 0x06345e591810c022 0x806345e591810c02 0x4e7ffe7fb818803b 0xf4e7ffe7fb818803

def z828 : W := mkw 0x46345ffb00000000 0x046345ffb0000000 0x4e7fffff80000003 0xf4e7fffff8000000

def z829 : W := mkw 0x2ddda000379e000c 0x02ddda000379e000 0x2fffe0003fdf0009 0xf2fffe0003fdf000

def z830 : W := mkw 0x02205e5900000000 0x002205e590000000 0x4067fe7f80000003 0xd4067fe7f8000000

def z831 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0x7fffffff87c0ff03 0xf7fffffff87c0ff0

def z832 : W := mkw 0x400040fb00000000 0x0400040fb0000000 0x4007e07f80000001 0x04007e07f8000000

def z833 : W := mkw 0x4fddd8fb00000000 0x04fddd8fb0000000 0x4ffffc7f80000003 0xf4ffffc7f8000000

def z834 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x419fe3ff80000001 0x8419fe3ff8000000

def z835 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xfe1f1c7c783ff0ff 0xffe1f1c7c783ff0f

def z836 : W := mkw 0x4ffddffb00402800 0x04ffddffb0040280 0xffffffffc7c0ff0f 0xfffffffffc7c0ff0

def z837 : W := mkw 0x061418541810d0a2 0x8061418541810d0a 0xde181c7c7818f0fe 0x7de181c7c7818f0f

def z838 : W := mkw 0x1b623f04fdf3fee7 0xa1b623f04fdf3fee 0xbfe01f807ffffffe 0xfbfe01f807ffffff

def z839 : W := mkw 0x10022004c8e3fcc6 0x210022004c8e3fcc 0xb000000079e7fccc 0x0b000000079e7fcc

def z840 : W := mkw 0x0f745f592d40ea03 0x00f745f592d40ea0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z841 : W := mkw 0x44bdc6fb00402800 0x044bdc6fb0040280 0xf07fee7fc1c07c07 0xdf07fee7fc1c07c0

def z842 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xffe01f807fe0ffcf 0xfffe01f807fe0ffc

def z843 : W := mkw 0x0020460900000000 0x0002046090000000 0x4067ec1f80000001 0x44067ec1f8000000

def z844 : W := mkw 0x4ffddffb2d00c203 0x04ffddffb2d00c20 0x4fffffffb8000003 0xf4fffffffb800000

def z845 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0x2fffe0003fff0009 0xa2fffe0003fff000

def z846 : W := mkw 0x2bc9b8542f8ed0ae 0x82bc9b8542f8ed0a 0x71e1fc7c07c7f0f2 0x871e1fc7c07c7f0f

def z847 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4f9fffff80000003 0x24f9fffff8000000

def z848 : W := mkw 0x0dfdc60925402800 0x00dfdc6092540280 0xffffee1fffc07c0f 0xfffffee1fffc07c0

def z849 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4ffffdff80000001 0x64ffffdff8000000

def z850 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x501ff07f803880ff 0x3501ff07f803880f

def z851 : W := mkw 0x4dfdc7fb00000000 0x04dfdc7fb0000000 0x01e7e39f80000000 0x801e7e39f8000000

def z852 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0xcffffffff800000f 0xfcffffffff800000

def z853 : W := mkw 0x0960070025402a01 0x00960070025402a0 0xbfe00f807fc07f0e 0xfbfe00f807fc07f0

def z854 : W := mkw 0x0000400900000000 0x0000040090000000 0x4067e01f80000001 0xd4067e01f8000000

def z855 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x719913e3863f8ff3 0x8719913e3863f8ff

def z856 : W := mkw 0x26bfbf005afeea0f 0x026bfbf005afeea0 0x101fff80003fff03 0x0101fff80003fff0

def z857 : W := mkw 0x449dc0fb020c0118 0x4449dc0fb020c011 0x419ff1ff86188339 0x2419ff1ff8618833

def z858 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0x9000000041c07cc0 0x09000000041c07cc

def z859 : W := mkw 0x0f745f5900000000 0x00f745f590000000 0x4fffffff80000003 0xf4fffffff8000000

def z860 : W := mkw 0x04160054503010a0 0x804160054503010a 0xde1e0c7c783870ff 0x7de1e0c7c783870f

def z861 : W := mkw 0x10022004c2af15dc 0x610022004c2af15d 0x30000000063f8ffc 0x030000000063f8ff

def z862 : W := mkw 0x002046ab00000000 0x0002046ab0000000 0x4067ffff80000003 0xd4067ffff8000000

def z863 : W := mkw 0x19622704e5e33ec5 0x219622704e5e33ec 0xb1e0038047e77fc4 0x8b1e0038047e77fc

def z864 : W := mkw 0x10022004d0f33cc4 0x210022004d0f33cc 0xb000000079ff7ccc 0x0b000000079ff7cc

def z865 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4fffefff80000001 0xc4fffefff8000000

def z866 : W := mkw 0x2ddfa0a277be000c 0x02ddfa0a277be000 0xafffe383ffff000d 0xfafffe383ffff000

def z867 : W := mkw 0x49e9c7aba74d2f59 0x449e9c7aba74d2f5 0x21e1e38387c70f00 0x821e1e38387c70f0

def z868 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xde1e1c7c7818f0fa 0x6de1e1c7c7818f0f

def z869 : W := mkw 0x4ffddffb0800c002 0x04ffddffb0800c00 0x5fffffff8000f003 0xf5fffffff8000f00

def z870 : W := mkw 0x0020460980412c40 0x00020460980412c4 0xf067ee1fc1e77cc7 0xdf067ee1fc1e77cc

def z871 : W := mkw 0x049dc00900000000 0x0049dc0090000000 0x401fe01f80000001 0x0401fe01f8000000

def z872 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0xa000000041c77c00 0x0a000000041c77c0

def z873 : W := mkw 0x0ddfa00050b20004 0x00ddfa00050b2000 0xafffe00079ff000d 0xfafffe00079ff000

def z874 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x6fffffff86000f03 0xf6fffffff86000f0

def z875 : W := mkw 0x44bdc6fb00000000 0x044bdc6fb0000000 0x41ffffff80000003 0xf41ffffff8000000

def z876 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xbfe11f807fe7ff0f 0xfbfe11f807fe7ff0

def z877 : W := mkw 0x6ffddffb3f5cea0b 0x06ffddffb3f5cea0 0xffffffffffd8ff0f 0xfffffffffffd8ff0

def z878 : W := mkw 0x4ffddffb00402800 0x04ffddffb0040280 0xcfffffffc1c07003 0xfcfffffffc1c0700

def z879 : W := mkw 0x3b623f04fffffecf 0x23b623f04fffffec 0xbfe01f807fffffce 0xfbfe01f807fffffc

def z880 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0x8000000041e770c0 0x08000000041e770c

def z881 : W := mkw 0x4ffddffb2f0cc31b 0x44ffddffb2f0cc31 0x4fffffffbe18833b 0xf4fffffffbe18833

def z882 : W := mkw 0x4ffddffb1810c022 0x84ffddffb1810c02 0x5fffffffb83880ff 0xf5fffffffb83880f

def z883 : W := mkw 0x2d56a0a2f5b30554 0x42d56a0a2f5b3055 0xde66f3e3f9c08ff2 0x4de66f3e3f9c08ff

def z884 : W := mkw 0x6ffddffb121c0008 0x06ffddffb121c000 0x4fffffff80180003 0xf4fffffff8018000

def z885 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xaff9e0007fff000c 0xaaff9e0007fff000

def z886 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x0007e01f80000000 0x00007e01f8000000

def z887 : W := mkw 0x44bdc6fb00000000 0x044bdc6fb0000000 0x407fe27f80000001 0x8407fe27f8000000

def z888 : W := mkw 0x0ddd8000270c0008 0x00ddd8000270c000 0xafffe0007fff000d 0xfafffe0007fff000

def z889 : W := mkw 0x0020460900000000 0x0002046090000000 0x71e7ff9f86008f0f 0xf71e7ff9f86008f0

def z890 : W := mkw 0x2ddfa00075b20004 0x02ddfa00075b2000 0xafffe00079e70005 0xfafffe00079e7000

def z891 : W := mkw 0x4ffddffb25000000 0x04ffddffb2500000 0x6fffffff87c00003 0xf6fffffff87c0000

def z892 : W := mkw 0x10222604c0e33cc4 0x210222604c0e33cc 0xb0000e0041e77cc6 0x0b0000e0041e77cc

def z893 : W := mkw 0x4dddc0fb00000000 0x04dddc0fb0000000 0x4f9fe07f80000001 0x24f9fe07f8000000

def z894 : W := mkw 0x12205e0d8841fcc2 0x212205e0d8841fcc 0x50001e1f8000fcc2 0x050001e1f8000fcc

def z895 : W := mkw 0x12205f5d8841fee3 0xa12205f5d8841fee 0x50001fff8000fff2 0x050001fff8000fff

def z896 : W := mkw 0x4ffddffb25000000 0x04ffddffb2500000 0x4fffffffbe00000b 0xf4fffffffbe00000

def z897 : W := mkw 0x020218044820d082 0x0020218044820d08 0xde1e1c7c7838f0ff 0x7de1e1c7c7838f0f

def z898 : W := mkw 0x0be95fab2d40ea03 0x00be95fab2d40ea0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z899 : W := mkw 0x2ddfa0a277be000c 0x02ddfa0a277be000 0xfffff3e3ffff80ff 0xffffff3e3ffff80f

def z900 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0x1000000000277cc0 0x01000000000277cc

def z901 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0x9e1e1c7c7838f0fc 0x69e1e1c7c7838f0f

def z902 : W := mkw 0x1b423904ede3fec7 0x21b423904ede3fec 0xbf8011807fe7ffcc 0x2bf8011807fe7ffc

def z903 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xafe7e0007fe70005 0xdafe7e0007fe7000

def z904 : W := mkw 0x2ddfa05077be002c 0x82ddfa05077be002 0xafffe0607fff003d 0xfafffe0607fff003

def z905 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0xfffffffffff8ffff 0xffffffffffff8fff

def z906 : W := mkw 0x4ffddffb25402a01 0x04ffddffb25402a0 0x7fffffff87c08f0f 0xf7fffffff87c08f0

def z907 : W := mkw 0x1022660dd0f33ce4 0xa1022660dd0f33ce 0xf067ee1fc1ff7cf7 0xdf067ee1fc1ff7cf

def z908 : W := mkw 0x0be95fab00000000 0x00be95fab0000000 0x4fffffff80000003 0xf4fffffff8000000

def z909 : W := mkw 0x4414c05900000000 0x04414c0590000000 0x4007e01f80000001 0x04007e01f8000000

def z910 : W := mkw 0x2ddfa0a277be011c 0x42ddfa0a277be011 0xbffff3e07fff8f3f 0xfbffff3e07fff8f3

def z911 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xafe7e0007fc7000c 0xfafe7e0007fc7000

def z912 : W := mkw 0x30022004d2ff3ccc 0x230022004d2ff3cc 0xb000000041ff7cc4 0x0b000000041ff7cc

def z913 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf07fee7fc1ff7cf7 0xdf07fee7fc1ff7cf

def z914 : W := mkw 0x00022004c0a314c4 0x000022004c0a314c 0xf067ee1fc1e77cc7 0xdf067ee1fc1e77cc

def z915 : W := mkw 0x10022004c2ef3ddc 0x610022004c2ef3dd 0xb000000041ff7cf4 0x0b000000041ff7cf

def z916 : W := mkw 0x449dc0fb020c0118 0x4449dc0fb020c011 0x401fe07f80180031 0x0401fe07f8018003

def z917 : W := mkw 0x4ffddffb2d00c002 0x04ffddffb2d00c00 0xffffffffffc0f00f 0xfffffffffffc0f00

def z918 : W := mkw 0x2ddfa00477be10ac 0x82ddfa00477be10a 0xafffe0007fff00fd 0xfafffe0007fff00f

def z919 : W := mkw 0x10ab66af42ee399c 0x610ab66af42ee399 0x81fefdfc47d8f338 0x681fefdfc47d8f33

def z920 : W := mkw 0x12205f098841ee43 0x212205f098841ee4 0x10001f838000ff02 0x010001f838000ff0

def z921 : W := mkw 0x2ddfa00477be108c 0x02ddfa00477be108 0xefffe01c7fff00cd 0xfefffe01c7fff00c

def z922 : W := mkw 0x0ddfa00065a20004 0x00ddfa00065a2000 0xafffe0007fe7000d 0xfafffe0007fe7000

def z923 : W := mkw 0x2ddfa00477be108c 0x02ddfa00477be108 0xbfffe0007fff70cd 0xfbfffe0007fff70c

def z924 : W := mkw 0x49e9c7ab25402a01 0x049e9c7ab25402a0 0xf1e7ef9fc7c07f07 0xdf1e7ef9fc7c07f0

def z925 : W := mkw 0x06bd5efb00000000 0x006bd5efb0000000 0x4fffffff80000003 0xf4fffffff8000000

def z926 : W := mkw 0x0b4019002d40ea03 0x00b4019002d40ea0 0xbf801d807fc0ff0e 0x7bf801d807fc0ff0

def z927 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xdf9e1ffc7838f0ff 0xfdf9e1ffc7838f0f

def z928 : W := mkw 0x02205e090800c002 0x002205e090800c00 0xde67fe1ff800f00f 0xfde67fe1ff800f00

def z929 : W := mkw 0x6ffddffb371c0008 0x06ffddffb371c000 0xefffffffffd8000f 0xfefffffffffd8000

def z930 : W := mkw 0x0202385448a2d0a6 0x80202385448a2d0a 0xf067fc7c41e7f0f7 0xdf067fc7c41e7f0f

def z931 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x4e7ffe7f80000003 0xf4e7ffe7f8000000

def z932 : W := mkw 0x2d56a00075b20004 0x02d56a00075b2000 0xafe7e0007fe7000d 0xfafe7e0007fe7000

def z933 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x4e67ec1f80000001 0x44e67ec1f8000000

def z934 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x5fffffff80008f03 0xf5fffffff80008f0

def z935 : W := mkw 0x10022004efefffdf 0x610022004efefffd 0xb00000007ffffffc 0x0b00000007ffffff

def z936 : W := mkw 0x4f74dffb00000000 0x04f74dffb0000000 0x4fe6ffff80000002 0xf4fe6ffff8000000

def z937 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xbfe013807fc0ff0c 0xabfe013807fc0ff0

def z938 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x5fffffff8000800f 0xf5fffffff8000800

def z939 : W := mkw 0x094000002d40ea03 0x0094000002d40ea0 0xbfe013807fc0ff0e 0xfbfe013807fc0ff0

def z940 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x401fec7f80000003 0x5401fec7f8000000

def z941 : W := mkw 0x4dfdc6fb00000000 0x04dfdc6fb0000000 0x4fffee7f80000003 0xf4fffee7f8000000

def z942 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0xf1991fe3c63fffff 0xff1991fe3c63ffff

def z943 : W := mkw 0x4ffddffb25402a01 0x04ffddffb25402a0 0x4fffffff81c00003 0xf4fffffff81c0000

def z944 : W := mkw 0x249fa0f6d2bf15fc 0xc249fa0f6d2bf15f 0x401fe07f803f00f1 0x0401fe07f803f00f

def z945 : W := mkw 0x2ddfa00477be108c 0x02ddfa00477be108 0xafffec1c7fff700d 0xfafffec1c7fff700

def z946 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xbfe7ff807fc0ff0f 0xfbfe7ff807fc0ff0

def z947 : W := mkw 0x06345e5900000000 0x006345e590000000 0x4e67ee1f80000003 0xd4e67ee1f8000000

def z948 : W := mkw 0x349fe0afd2bf15dc 0x6349fe0afd2bf15d 0x401fe07f803f00f1 0x0401fe07f803f00f

def z949 : W := mkw 0x2ddfa00077be011c 0x42ddfa00077be011 0xafffe0007fff833d 0xfafffe0007fff833

def z950 : W := mkw 0x469dd8fb00000000 0x0469dd8fb0000000 0x4e1fec7f80000001 0x44e1fec7f8000000

def z951 : W := mkw 0x10022004c2af15dc 0x610022004c2af15d 0x00000000003f00f0 0x000000000003f00f

def z952 : W := mkw 0x6fdd99f23f1cc02a 0x86fdd99f23f1cc02 0x0f9811e03e188038 0x20f9811e03e18803

def z953 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf067ec1fc1e77cc5 0x4f067ec1fc1e77cc

def z954 : W := mkw 0x4fddd9fb00000000 0x04fddd9fb0000000 0x4f9ff3ff80000003 0xb4f9ff3ff8000000

def z955 : W := mkw 0x1022660dc0e33dd4 0x61022660dc0e33dd 0xf067ee1fc1e7fff7 0xdf067ee1fc1e7fff

def z956 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xffe61f9c7fc0ff0f 0xfffe61f9c7fc0ff0

def z957 : W := mkw 0x0b605f092d40ea03 0x00b605f092d40ea0 0xbfe1ff83ffc0ff0e 0xfbfe1ff83ffc0ff0

def z958 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x5fffffff802000c7 0xf5fffffff802000c

def z959 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xd067ee1fc1e77cc3 0x4d067ee1fc1e77cc

def z960 : W := mkw 0x0dfdc6ab00000000 0x00dfdc6ab0000000 0x4fffffff80000003 0xf4fffffff8000000

def z961 : W := mkw 0x4fddd9fb00000000 0x04fddd9fb0000000 0x4ffff1ff80000001 0xf4ffff1ff8000000

def z962 : W := mkw 0x4ffddffb020c0008 0x04ffddffb020c000 0x7fffffff863f8f0f 0xf7fffffff863f8f0

def z963 : W := mkw 0x10022004c0a314c4 0x210022004c0a314c 0x3000000000270cc4 0x03000000000270cc

def z964 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf067ee1fc7e7ffcf 0xdf067ee1fc7e7ffc

def z965 : W := mkw 0x4434c65900000000 0x04434c6590000000 0x4067ee1f80000003 0xd4067ee1f8000000

def z966 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x0e67ec1f80000000 0x40e67ec1f8000000

def z967 : W := mkw 0x061619545830d2a3 0x8061619545830d2a 0xde1e1dfc7838f3ff 0x7de1e1dfc7838f3f

def z968 : W := mkw 0x02201e000840e802 0x002201e000840e80 0xbfe01f807fc0ff0e 0xfbfe01f807fc0ff0

def z969 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0xdffffffff9c0ff03 0xfdffffffff9c0ff0

def z970 : W := mkw 0x0020460900000000 0x0002046090000000 0x4066ee1f80000002 0x44066ee1f8000000

def z971 : W := mkw 0x4ffddffb2d00c203 0x04ffddffb2d00c20 0xdffffffffe00f30f 0xfdffffffffe00f30

def z972 : W := mkw 0x6dddc0fb371c0008 0x06dddc0fb371c000 0x4f9fe07fbe180009 0x24f9fe07fbe18000

def z973 : W := mkw 0x0416200050b20004 0x00416200050b2000 0xae67e00079e70005 0xdae67e00079e7000

def z974 : W := mkw 0x19e967aba7cf2f5d 0x619e967aba7cf2f5 0x21e1e38387c70f00 0x821e1e38387c70f0

def z975 : W := mkw 0x4be9dffb00000000 0x04be9dffb0000000 0x41e7ffff80000003 0xd41e7ffff8000000

def z976 : W := mkw 0x0940000025000000 0x0094000002500000 0xafe7e0007fc0000d 0xfafe7e0007fc0000

def z977 : W := mkw 0x2ddfa00477be108c 0x02ddfa00477be108 0xfffffc7c7ffff0ff 0xffffffc7c7ffff0f

def z978 : W := mkw 0x008940ab00000000 0x0008940ab0000000 0x401fe07f80000001 0x0401fe07f8000000

def z979 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xfe1e1c7c7e38ffff 0x7fe1e1c7c7e38fff

def z980 : W := mkw 0x02205f090840ea03 0x002205f090840ea0 0x50001f9f8000ff02 0x050001f9f8000ff0

def z981 : W := mkw 0x02205e0900000000 0x002205e090000000 0x4e67fe1f80000003 0xf4e67fe1f8000000

def z982 : W := mkw 0x10022004e5e33ec5 0x210022004e5e33ec 0xb000000047e77fc4 0x0b000000047e77fc

def z983 : W := mkw 0x4ffddffb0800c002 0x04ffddffb0800c00 0x4fffffffb800800b 0xf4fffffffb800800

def z984 : W := mkw 0x4ffddffb25000000 0x04ffddffb2500000 0xffffffffffc08f0f 0xfffffffffffc08f0

def z985 : W := mkw 0x049f200052be000c 0x0049f200052be000 0xafffe0007fff000d 0xfafffe0007fff000

def z986 : W := mkw 0x2d56a00077be000c 0x02d56a00077be000 0x8e66e00079ff0000 0x48e66e00079ff000

def z987 : W := mkw 0x4ffddffb020c0118 0x44ffddffb020c011 0x5fffffff863883ff 0xf5fffffff863883f

def z988 : W := mkw 0x249fa00052be000c 0x0249fa00052be000 0x00180000003f0000 0x000180000003f000

def z989 : W := mkw 0x4ffddffb020c0008 0x04ffddffb020c000 0x4fffffff803f0003 0xf4fffffff803f000

def z990 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x719f1fff863f8fff 0xf719f1fff863f8ff

def z991 : W := mkw 0x0f765f5d7d70faa3 0x80f765f5d7d70faa 0xfffffffffff8ffff 0xffffffffffff8fff

def z992 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xffe11f83ffc0ff0f 0xfffe11f83ffc0ff0

def z993 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xbfe01f807fc0ff02 0xcbfe01f807fc0ff0

def z994 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4fe7ef9f80000003 0xd4fe7ef9f8000000

def z995 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xfe1e1e7c7838fcff 0xffe1e1e7c7838fcf

def z996 : W := mkw 0x2d56a00075b20004 0x02d56a00075b2000 0xae66e00079e70004 0x4ae66e00079e7000

def z997 : W := mkw 0x0020460900000000 0x0002046090000000 0x41e7ff9f80000003 0xf41e7ff9f8000000

def z998 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xde181c7c7838f0fe 0x2de181c7c7838f0f

def z999 : W := mkw 0x4dfdc7fb00000000 0x04dfdc7fb0000000 0x41fff3ff80000003 0xb41fff3ff8000000

def z1000 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xae7fe0007fff000d 0x4ae7fe0007fff000

def z1001 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0xefffffffc1c00007 0xfefffffffc1c0000

def z1002 : W := mkw 0x46bddffb00000000 0x046bddffb0000000 0x401fec7f80000001 0x0401fec7f8000000

def z1003 : W := mkw 0x1b623f04c0e33cc4 0x21b623f04c0e33cc 0xbfe01f8041e77cc6 0xfbfe01f8041e77cc

def z1004 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xbfe00f807fc07f06 0xdbfe00f807fc07f0

def z1005 : W := mkw 0x4fdd99f22f0cc31b 0x44fdd99f22f0cc31 0x0f9811e03e188338 0x20f9811e03e18833

def z1006 : W := mkw 0x6fdd99f23f1cc20b 0x06fdd99f23f1cc20 0x0f9811e03e188308 0x20f9811e03e18830

def z1007 : W := mkw 0x4dddc0fb00000000 0x04dddc0fb0000000 0x41ffe07f80000001 0x841ffe07f8000000

def z1008 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xde1e0c7c7838f0fd 0x4de1e0c7c7838f0f

def z1009 : W := mkw 0x6ffddffb371c0008 0x06ffddffb371c000 0x6fffffffbe3f000f 0xf6fffffffbe3f000

def z1010 : W := mkw 0x10022004d8b3d4e6 0xa10022004d8b3d4e 0x90000000783ff0fc 0x090000000783ff0f

def z1011 : W := mkw 0x0960460925000000 0x0096046092500000 0xefe7ee1fffc0000f 0xfefe7ee1fffc0000

def z1012 : W := mkw 0x469dd9fb00000000 0x0469dd9fb0000000 0x401ff1ff80000001 0x0401ff1ff8000000

def z1013 : W := mkw 0x0b4018002d00c002 0x00b4018002d00c00 0xbfe01f807fc0ff0e 0xfbfe01f807fc0ff0

def z1014 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0xb000020041e77cc6 0x9b000020041e77cc

def z1015 : W := mkw 0x4ffddffb25000000 0x04ffddffb2500000 0xcffffffff9c00003 0xfcffffffff9c0000

def z1016 : W := mkw 0x0960470925402a01 0x00960470925402a0 0x21e1e38387c00f00 0x821e1e38387c00f0

def z1017 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xbfe01f807ff8fffe 0xfbfe01f807ff8fff

def z1018 : W := mkw 0x4ffddffb3d10c223 0x84ffddffb3d10c22 0x4fffffffbe18833b 0xf4fffffffbe18833

def z1019 : W := mkw 0x2ddfa0a277be000c 0x02ddfa0a277be000 0xefffe063ffff000d 0xfefffe063ffff000

def z1020 : W := mkw 0x249fa00052be000c 0x0249fa00052be000 0xae7fe00079ff000d 0xfae7fe00079ff000

def z1021 : W := mkw 0x4089c0ab00000000 0x04089c0ab0000000 0x4007e01f80000001 0x04007e01f8000000

def z1022 : W := mkw 0x020018002d40ea03 0x0020018002d40ea0 0xbf801f807fc0ff0e 0xfbf801f807fc0ff0

def z1023 : W := mkw 0x4ffddffb020c0008 0x04ffddffb020c000 0x6fffffff86070003 0xf6fffffff8607000

def z1024 : W := mkw 0x10022004ede3fec7 0x210022004ede3fec 0xb000000079e77cc4 0x0b000000079e77cc

def z1025 : W := mkw 0x30022004f5f33cc4 0x230022004f5f33cc 0xb000000079e77cc4 0x0b000000079e77cc

def z1026 : W := mkw 0x02205f090840ea03 0x002205f090840ea0 0x5067ff9f8000ff03 0xd5067ff9f8000ff0

def z1027 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf067ff9fc1e7ffc7 0xdf067ff9fc1e7ffc

def z1028 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0x8fffe00079ff0001 0xf8fffe00079ff000

def z1029 : W := mkw 0x0022660940e22804 0x00022660940e2280 0xf067ee1fc1e77c07 0xdf067ee1fc1e77c0

def z1030 : W := mkw 0x12205f0d8841fec3 0x212205f0d8841fec 0x50000e1f80007cc2 0x050000e1f80007cc

def z1031 : W := mkw 0x4ffddffb270c0008 0x04ffddffb270c000 0xefffffffffff000f 0xfefffffffffff000

def z1032 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0xafe7ef9fffc07f00 0xcafe7ef9fffc07f0

def z1033 : W := mkw 0x10222604c0e33cc4 0x210222604c0e33cc 0xb060020041e77cc4 0x8b060020041e77cc

def z1034 : W := mkw 0x402047ab00000000 0x0402047ab0000000 0x4067ef9f80000003 0xd4067ef9f8000000

def z1035 : W := mkw 0x6ddfa0f277be000c 0x06ddfa0f277be000 0xafffe0607fff000d 0xfafffe0607fff000

def z1036 : W := mkw 0x402046fb00000000 0x0402046fb0000000 0x4067ee7f80000003 0xd4067ee7f8000000

def z1037 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0xb180138047e7ffce 0xbb180138047e7ffc

def z1038 : W := mkw 0x0960470925402a01 0x00960470925402a0 0x61e7ef9f87c00f03 0xd61e7ef9f87c00f0

def z1039 : W := mkw 0x0020460900000000 0x0002046090000000 0x407ffe7f80000003 0xf407ffe7f8000000

def z1040 : W := mkw 0x0020460900000000 0x0002046090000000 0x507ffe7f803880ff 0xf507ffe7f803880f

def z1041 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0x2000000001e70cc0 0x02000000001e70cc

def z1042 : W := mkw 0x0020460900000000 0x0002046090000000 0x4067e21f80000001 0x84067e21f8000000

def z1043 : W := mkw 0x4dfdc7fb00000000 0x04dfdc7fb0000000 0x4fffe3ff80000001 0xf4fffe3ff8000000

def z1044 : W := mkw 0x06345e590840e802 0x006345e590840e80 0xfe7ffe7ff9c0fc0f 0xffe7ffe7ff9c0fc0

def z1045 : W := mkw 0x108b2004c2ef3ccc 0x2108b2004c2ef3cc 0xb199000047ff7ccd 0xbb199000047ff7cc

def z1046 : W := mkw 0x10022004dafffdfe 0xe10022004dafffdf 0xb00000007ffffffc 0x0b00000007ffffff

def z1047 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xefffe0607fff00fd 0xfefffe0607fff00f

def z1048 : W := mkw 0x0002200040a20004 0x00002200040a2000 0xae67e00079e7000d 0xfae67e00079e7000

def z1049 : W := mkw 0x449dc0fb10100020 0x8449dc0fb1010002 0x401fe07f80180031 0x0401fe07f8018003

def z1050 : W := mkw 0x469dd8fb00000000 0x0469dd8fb0000000 0x401ffc7f80000003 0x0401ffc7f8000000

def z1051 : W := mkw 0x4ffddffb00402800 0x04ffddffb0040280 0x5fffffff80007c03 0xf5fffffff80007c0

def z1052 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xe067ee1fc1e77cc1 0xce067ee1fc1e77cc

def z1053 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0xfffffffff9c07c07 0xffffffffff9c07c0

def z1054 : W := mkw 0x49e9c7ab00000000 0x049e9c7ab0000000 0x41ffffff80000003 0xf41ffffff8000000

def z1055 : W := mkw 0x12023804c8e3fcc6 0x212023804c8e3fcc 0xbe001c0079e7fcce 0x7be001c0079e7fcc

def z1056 : W := mkw 0x0960470900000000 0x0096047090000000 0x41e7ef9f80000003 0xd41e7ef9f8000000

def z1057 : W := mkw 0x46bddffb00000000 0x046bddffb0000000 0x407fffff80000003 0xd407fffff8000000

def z1058 : W := mkw 0x4f74dffb00000000 0x04f74dffb0000000 0x0e66ef9f80000000 0x40e66ef9f8000000

def z1059 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xbfe00f807fc0ff0c 0xcbfe00f807fc0ff0

def z1060 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0xb0000c0041e77cc6 0x5b0000c0041e77cc

def z1061 : W := mkw 0x40a9c6ab00000000 0x040a9c6ab0000000 0x4067ee1f80000003 0xd4067ee1f8000000

def z1062 : W := mkw 0x0434465900000000 0x0043446590000000 0x407fee7f80000003 0xd407fee7f8000000

def z1063 : W := mkw 0x10022004c2ef3ccc 0x210022004c2ef3cc 0xb000000047ff7ccc 0x0b000000047ff7cc

def z1064 : W := mkw 0x0000400900000000 0x0000040090000000 0x4007ec1f80000003 0x54007ec1f8000000

def z1065 : W := mkw 0x12223e04d8f3fce6 0xa12223e04d8f3fce 0xbe601e0079fffcfe 0xfbe601e0079fffcf

def z1066 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x7fffffff86388fff 0xf7fffffff86388ff

def z1067 : W := mkw 0x0416000450301080 0x0041600045030108 0xde1e1c7c7838f0ff 0x7de1e1c7c7838f0f

def z1068 : W := mkw 0x0b605f0900000000 0x00b605f090000000 0x4e67ee1f80000003 0xd4e67ee1f8000000

def z1069 : W := mkw 0x4f74df592d40ea03 0x04f74df592d40ea0 0xffe7ff9fffc0ff0f 0xfffe7ff9fffc0ff0

def z1070 : W := mkw 0x0020460900402800 0x0002046090040280 0x6067ee1f81c00c03 0xd6067ee1f81c00c0

def z1071 : W := mkw 0x0ffddf0900000000 0x00ffddf090000000 0x4fffff9f80000003 0xf4fffff9f8000000

def z1072 : W := mkw 0x1f767f5d7df2faa7 0xa1f767f5d7df2faa 0x8e66ec1c79c07000 0x48e66ec1c79c0700

def z1073 : W := mkw 0x2ddfa0a277be000c 0x02ddfa0a277be000 0xaffff1e07fff000d 0xfaffff1e07fff000

def z1074 : W := mkw 0x1436460dd0713cc0 0x21436460dd0713cc 0xde1e0e1ff8387ccf 0x7de1e0e1ff8387cc

def z1075 : W := mkw 0x002046092d40ea03 0x0002046092d40ea0 0xf067ee1fffc0ff0f 0xdf067ee1fffc0ff0

def z1076 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xd067ec1fc1e770c7 0x5d067ec1fc1e770c

def z1077 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x6fffffff80270007 0xf6fffffff8027000

def z1078 : W := mkw 0x4ffddffb2f4ceb1b 0x44ffddffb2f4ceb1 0xffffffffffd8ff3f 0xfffffffffffd8ff3

def z1079 : W := mkw 0x0b4019002d40ea03 0x00b4019002d40ea0 0xbf8013807fc0ff0e 0xbbf8013807fc0ff0

def z1080 : W := mkw 0x4dfdc7ab00000000 0x04dfdc7ab0000000 0x4fffef9f80000003 0xf4fffef9f8000000

def z1081 : W := mkw 0x0020460900000000 0x0002046090000000 0x5067ee1f802000c7 0xd5067ee1f802000c

def z1082 : W := mkw 0x12205e5d8841fce2 0xa12205e5d8841fce 0x50000e1f80007cc2 0x050000e1f80007cc

def z1083 : W := mkw 0x00a946ab020c0118 0x400a946ab020c011 0x41ffffff8618833b 0xf41ffffff8618833

def z1084 : W := mkw 0x4ffddffb25000201 0x04ffddffb2500020 0x4fffffff86000303 0xf4fffffff8600030

def z1085 : W := mkw 0x46bddffb00000000 0x046bddffb0000000 0x4e1fffff80000003 0x74e1fffff8000000

def z1086 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xb067ee1fc1c77c06 0xdb067ee1fc1c77c0

def z1087 : W := mkw 0x0fdd98f200000000 0x00fdd98f20000000 0x4fffffff80000003 0xf4fffffff8000000

def z1088 : W := mkw 0x42205ffb00000000 0x042205ffb0000000 0x4066ffff80000002 0x44066ffff8000000

def z1089 : W := mkw 0x2dfdc609371c0008 0x02dfdc609371c000 0x4fffee1fbe18000b 0xf4fffee1fbe18000

def z1090 : W := mkw 0x10222604c0e33cc4 0x210222604c0e33cc 0xb0600c0041e77cc4 0x4b0600c0041e77cc

def z1091 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0x8e67e00079c70000 0x48e67e00079c7000

def z1092 : W := mkw 0x0940200025820004 0x0094020002582000 0xafe1e0007fc7000c 0xfafe1e0007fc7000

def z1093 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xbf801f807fc0ff0e 0x2bf801f807fc0ff0

def z1094 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4fffffff8018803b 0xf4fffffff8018803

def z1095 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xbfffe0007fff80fd 0xfbfffe0007fff80f

def z1096 : W := mkw 0x4dddc0fb00000000 0x04dddc0fb0000000 0x4ffff3ff80000003 0xf4ffff3ff8000000

def z1097 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0xcfffffffffc0f30b 0xfcfffffffffc0f30

def z1098 : W := mkw 0x020018540800d0a2 0x8020018540800d0a 0xde181c7c7838f0ff 0x7de181c7c7838f0f

def z1099 : W := mkw 0x4ffddffb25402800 0x04ffddffb2540280 0xffffffffffc07c0f 0xfffffffffffc07c0

def z1100 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0xbfe7ff9fffc0ff0e 0xfbfe7ff9fffc0ff0

def z1101 : W := mkw 0x0d76075475703aa1 0x80d76075475703aa 0x61fe03fc07f80ff1 0x861fe03fc07f80ff

def z1102 : W := mkw 0x44bdc7fb00000000 0x044bdc7fb0000000 0x401fe3ff80000001 0x0401fe3ff8000000

def z1103 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xbff81f807ff8ff0f 0xfbff81f807ff8ff0

def z1104 : W := mkw 0x4ffddffb1810c022 0x84ffddffb1810c02 0x4fffffffb8000003 0xf4fffffffb800000

def z1105 : W := mkw 0x0020460900000000 0x0002046090000000 0x4007ee1f80000003 0x04007ee1f8000000

def z1106 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4fffffff803800f3 0xf4fffffff803800f

def z1107 : W := mkw 0x30022004e7ef3ccc 0x230022004e7ef3cc 0xb000000047e77cc4 0x0b000000047e77cc

def z1108 : W := mkw 0x2d56a00075b20004 0x02d56a00075b2000 0x8e67e00079e70001 0x48e67e00079e7000

def z1109 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xffe01fe07fc0fffe 0xfffe01fe07fc0fff

def z1110 : W := mkw 0x20022004ffbfd5fe 0xc20022004ffbfd5f 0xb00000007ffffffc 0x0b00000007ffffff

def z1111 : W := mkw 0x0000400900000000 0x0000040090000000 0x4007e21f80000003 0x94007e21f8000000

def z1112 : W := mkw 0x39e9e6aba7cf2d5c 0x639e9e6aba7cf2d5 0x21e1e38387c70f00 0x821e1e38387c70f0

def z1113 : W := mkw 0x1022670dc0e33ec5 0x21022670dc0e33ec 0xf067ef9fc1e77fc7 0xdf067ef9fc1e77fc

def z1114 : W := mkw 0x2d56a00077be000c 0x02d56a00077be000 0xae66e0007fc70000 0x4ae66e0007fc7000

def z1115 : W := mkw 0x0960460900000000 0x0096046090000000 0x4fe7ee1f80000003 0xf4fe7ee1f8000000

def z1116 : W := mkw 0x42205ffb8841ef53 0x442205ffb8841ef5 0x50001fff8000fff2 0x050001fff8000fff

def z1117 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x519913e3863f8ffb 0x2519913e3863f8ff

def z1118 : W := mkw 0x4ffddffb020c0118 0x44ffddffb020c011 0x6fffffff863f833f 0xf6fffffff863f833

def z1119 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xafe7e0007fff000c 0xcafe7e0007fff000

def z1120 : W := mkw 0x4ffddffb10100000 0x04ffddffb1010000 0x4fffffffb818000b 0xf4fffffffb818000

def z1121 : W := mkw 0x4f74dffb00000000 0x04f74dffb0000000 0x4e67ffff80000003 0xd4e67ffff8000000

def z1122 : W := mkw 0x0d74c60900000000 0x00d74c6090000000 0x4e67ee1f80000003 0xd4e67ee1f8000000

def z1123 : W := mkw 0x52205fff8841fec3 0x252205fff8841fec 0x50001fff8000ffc2 0x050001fff8000ffc

def z1124 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x4e1fe07f80000001 0x74e1fe07f8000000

def z1125 : W := mkw 0x30022004fffffecf 0x230022004fffffec 0xb00000007fffffcc 0x0b00000007fffffc

def z1126 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x0fffffff80000000 0xe0fffffff8000000

def z1127 : W := mkw 0x4f74df592d40ea03 0x04f74df592d40ea0 0xfe67ee1ff9c07c07 0xdfe67ee1ff9c07c0

def z1128 : W := mkw 0x2ddfa0a277be000c 0x02ddfa0a277be000 0xfffff3e3ffff8f0f 0xffffff3e3ffff8f0

def z1129 : W := mkw 0x4ffddffb0800c002 0x04ffddffb0800c00 0xdffffffff838f0ff 0xfdffffffff838f0f

def z1130 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf1e7ef9fc7e77fc7 0xdf1e7ef9fc7e77fc

def z1131 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4ffeffff80000002 0x64ffeffff8000000

def z1132 : W := mkw 0x16163854d8f3fce6 0xa16163854d8f3fce 0xbe18106079fffcfc 0x2be18106079fffcf

def z1133 : W := mkw 0x04bdc60900000000 0x004bdc6090000000 0x407fee1f80000003 0xd407fee1f8000000

def z1134 : W := mkw 0x10022004d8f3fce6 0xa10022004d8f3fce 0xb000000079e77cc4 0x0b000000079e77cc

def z1135 : W := mkw 0x2d56a00075b20004 0x02d56a00075b2000 0xae67e00079c70000 0xcae67e00079c7000

def z1136 : W := mkw 0x4634dffb00000000 0x04634dffb0000000 0x4006ffff80000002 0x04006ffff8000000

def z1137 : W := mkw 0x6ffddffb35100000 0x06ffddffb3510000 0x4fffffffb8000003 0xf4fffffffb800000

def z1138 : W := mkw 0x44bdc6fb00000000 0x044bdc6fb0000000 0x401fee7f80000003 0x0401fee7f8000000

def z1139 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xbfe01d807fc0ff0c 0x6bfe01d807fc0ff0

def z1140 : W := mkw 0x44bdc6fb00000000 0x044bdc6fb0000000 0x407fec7f80000001 0x4407fec7f8000000

def z1141 : W := mkw 0x0000000000000000 0x0000000000000000 0x7181138386008f0f 0xb7181138386008f0

def z1142 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf067fe7fc1e7fcf7 0xdf067fe7fc1e7fcf

def z1143 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0xf000000041e77cc7 0x1f000000041e77cc

def z1144 : W := mkw 0x0b605f092d40ea03 0x00b605f092d40ea0 0xce67ee1ff9c07003 0xdce67ee1ff9c0700

def z1145 : W := mkw 0x2d56a00077be000c 0x02d56a00077be000 0xae67e0007fff000d 0xdae67e0007fff000

def z1146 : W := mkw 0x4b60df092d40ea03 0x04b60df092d40ea0 0xbfe0ff807fc0ff0e 0xfbfe0ff807fc0ff0

def z1147 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x719ff3ff86008f0f 0xb719ff3ff86008f0

def z1148 : W := mkw 0x4ffddffb00402800 0x04ffddffb0040280 0x6fffffff81c00c03 0xf6fffffff81c00c0

def z1149 : W := mkw 0x0b601f502d40ea23 0x80b601f502d40ea2 0xbfe01fe07fc0ff3e 0xfbfe01fe07fc0ff3

def z1150 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x401ff3ff80000003 0x0401ff3ff8000000

def z1151 : W := mkw 0x0dddc00900000000 0x00dddc0090000000 0x4fffe01f80000001 0xf4fffe01f8000000

def z1152 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf067fe1fc1e7fccf 0xff067fe1fc1e7fcc

def z1153 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xafffe0007fc70001 0xfafffe0007fc7000

def z1154 : W := mkw 0x29c9a000278e000c 0x029c9a000278e000 0xafe1e0007fc70000 0xcafe1e0007fc7000

def z1155 : W := mkw 0x00a94609020c0008 0x000a94609020c000 0x61ffee1f863f000f 0xf61ffee1f863f000

def z1156 : W := mkw 0x1002600dc0a314c4 0x21002600dc0a314c 0xf067ec1fc1e770c7 0xdf067ec1fc1e770c

def z1157 : W := mkw 0x10022004c8e3fce6 0xa10022004c8e3fce 0xb000000041e7fcf4 0x0b000000041e7fcf

def z1158 : W := mkw 0x6ffddffb3f1cc02a 0x86ffddffb3f1cc02 0x4fffffffbe18803b 0xf4fffffffbe18803

def z1159 : W := mkw 0x4b605ffb2d40ea03 0x04b605ffb2d40ea0 0xffe7ffffffc0ff0f 0xfffe7ffffffc0ff0

def z1160 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4ffff3ff80000001 0xa4ffff3ff8000000

def z1161 : W := mkw 0x0b601f502d40ea03 0x00b601f502d40ea0 0xffe01ffc7fc0ff0e 0xfffe01ffc7fc0ff0

def z1162 : W := mkw 0x4b605ffb00000000 0x04b605ffb0000000 0x4fe7ffff80000003 0xf4fe7ffff8000000

def z1163 : W := mkw 0x0b605f092d40ea03 0x00b605f092d40ea0 0x8e66ec1c79c07000 0x48e66ec1c79c0700

def z1164 : W := mkw 0x0960060025402800 0x0096006002540280 0xbfe01f807fc0ff0e 0xfbfe01f807fc0ff0

def z1165 : W := mkw 0x2ddfa05477be10ac 0x82ddfa05477be10a 0xffffec7c7fff70ff 0xfffffec7c7fff70f

def z1166 : W := mkw 0x4ffddffb0800c203 0x04ffddffb0800c20 0x4fffffff80008303 0xf4fffffff8000830

def z1167 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xffffe0007fff00cf 0xfffffe0007fff00c

def z1168 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf067ee1fc1c77cc2 0xcf067ee1fc1c77cc

def z1169 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x7fffffff80000c07 0xf7fffffff80000c0

def z1170 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xde1e0c7c783870f7 0x5de1e0c7c783870f

def z1171 : W := mkw 0x10022004d0f33ce4 0xa10022004d0f33ce 0xb000000041ff7cf4 0x0b000000041ff7cf

def z1172 : W := mkw 0x1022660dd0f33cc4 0x21022660dd0f33cc 0xf067ee1ff9ff7ccf 0xdf067ee1ff9ff7cc

def z1173 : W := mkw 0x6ffddffb371c0118 0x46ffddffb371c011 0x4fffffffbe18833b 0xf4fffffffbe18833

def z1174 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x401ff07f80000003 0x3401ff07f8000000

def z1175 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4e7fffff80000003 0x44e7fffff8000000

def z1176 : W := mkw 0x30022004f7bf14cc 0x230022004f7bf14c 0xa00000007fff00cc 0x0a00000007fff00c

def z1177 : W := mkw 0x4ffddffb0840e802 0x04ffddffb0840e80 0xfffffffff9c0fc0f 0xffffffffff9c0fc0

def z1178 : W := mkw 0x10022004c8e3fec7 0x210022004c8e3fec 0xb000000041e7ffc4 0x0b000000041e7ffc

def z1179 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xe067ee1fc1c77c03 0xde067ee1fc1c77c0

def z1180 : W := mkw 0x4414c0fb00000000 0x04414c0fb0000000 0x4006e07f80000000 0x04006e07f8000000

def z1181 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0xefffffffffc0700f 0xfefffffffffc0700

def z1182 : W := mkw 0x6ddfa1a277be000c 0x06ddfa1a277be000 0xafffe1807fff000d 0xfafffe1807fff000

def z1183 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf067ee1fc1fffcff 0xdf067ee1fc1fffcf

def z1184 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xe067ec1fc1e770c5 0xde067ec1fc1e770c

def z1185 : W := mkw 0x149f60ffd2bf15fc 0xe149f60ffd2bf15f 0x401fe07f803f00f1 0x0401fe07f803f00f

def z1186 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xde1e1c7c7838f0f3 0x4de1e1c7c7838f0f

def z1187 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf1e7ff9fc1e77cc7 0xff1e7ff9fc1e77cc

def z1188 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xc067ee1fc1e770c3 0xdc067ee1fc1e770c

def z1189 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x619913e3863f8ff9 0xa619913e3863f8ff

def z1190 : W := mkw 0x30022004fffffcee 0xa30022004fffffce 0xb00000007ffffcfc 0x0b00000007ffffcf

def z1191 : W := mkw 0x008900a2820d0558 0x4008900a2820d055 0x00180060003f00f0 0x000180060003f00f

def z1192 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xbfffec007fff700f 0xfbfffec007fff700

def z1193 : W := mkw 0x4be9dfab2d40ea03 0x04be9dfab2d40ea0 0xffe7ff9fffc0ff0f 0xfffe7ff9fffc0ff0

def z1194 : W := mkw 0x0b4019002d40ea03 0x00b4019002d40ea0 0xbfe011807fc0ff0c 0xfbfe011807fc0ff0

def z1195 : W := mkw 0x2616b85458b2d0a6 0x82616b85458b2d0a 0xde1efc7c7838f0ff 0x7de1efc7c7838f0f

def z1196 : W := mkw 0x4dfdc7fb25402a01 0x04dfdc7fb25402a0 0x61ffe3ff87c00f01 0x861ffe3ff87c00f0

def z1197 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xaffff3807fff000f 0xfaffff3807fff000

def z1198 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xfff81fe07fc0ff0f 0xffff81fe07fc0ff0

def z1199 : W := mkw 0x2fdd98f23f1cc13a 0xc2fdd98f23f1cc13 0x0f9811e03e188338 0x20f9811e03e18833

def z1200 : W := mkw 0x09cb200067ae000c 0x009cb200067ae000 0xafffe0007fff000d 0xfafffe0007fff000

def z1201 : W := mkw 0x4ffddffb020c0008 0x04ffddffb020c000 0x4fffffff8618000b 0xf4fffffff8618000

def z1202 : W := mkw 0x10022004d0b314e4 0xa10022004d0b314e 0x00000000003f00f0 0x000000000003f00f

def z1203 : W := mkw 0x4ffddffb020c0118 0x44ffddffb020c011 0x7fffffff86188f3f 0xf7fffffff86188f3

def z1204 : W := mkw 0x4f74dffb00000000 0x04f74dffb0000000 0x4e66ec7f80000000 0x44e66ec7f8000000

def z1205 : W := mkw 0x30022004f7ff3ddc 0x630022004f7ff3dd 0xb00000007ffffffc 0x0b00000007ffffff

def z1206 : W := mkw 0x0434460900000000 0x0043446090000000 0x4e7fee1f80000003 0xf4e7fee1f8000000

def z1207 : W := mkw 0x4ffddffb020c0118 0x44ffddffb020c011 0x4fffffff86000303 0xf4fffffff8600030

def z1208 : W := mkw 0x12205faf8841ffd3 0x612205faf8841ffd 0x50001fff8000fff2 0x050001fff8000fff

def z1209 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0x9fe01f807fc0ff0a 0x69fe01f807fc0ff0

def z1210 : W := mkw 0x52205fff8841fce2 0xa52205fff8841fce 0x50001fff8000fcf2 0x050001fff8000fcf

def z1211 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4fffffff8600830b 0xf4fffffff8600830

def z1212 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xff9e1c7c7e38f0ff 0xfff9e1c7c7e38f0f

def z1213 : W := mkw 0x10022004c0e33dd4 0x610022004c0e33dd 0xb000000041e7fff4 0x0b000000041e7fff

def z1214 : W := mkw 0x4fddd9fb00000000 0x04fddd9fb0000000 0x4f9ffdff80000003 0x74f9ffdff8000000

def z1215 : W := mkw 0x061418541810d0a2 0x8061418541810d0a 0x5e181c7c3838f0ff 0x35e181c7c3838f0f

def z1216 : W := mkw 0x10022004e5e33cc4 0x210022004e5e33cc 0xb00000007fe77ccc 0x0b00000007fe77cc

def z1217 : W := mkw 0x0ffddf092d40ea03 0x00ffddf092d40ea0 0xffffff9fffc0ff0f 0xfffffff9fffc0ff0

def z1218 : W := mkw 0x4ffddffb2d00c203 0x04ffddffb2d00c20 0xefffffffffc0830f 0xfefffffffffc0830

def z1219 : W := mkw 0x10022004c0a314c4 0x210022004c0a314c 0x90000000402770c4 0x090000000402770c

def z1220 : W := mkw 0x29c9a000278e000c 0x029c9a000278e000 0x2fe1e0003fc70008 0xa2fe1e0003fc7000

def z1221 : W := mkw 0x10022004c0e33cc4 0x210022004c0e33cc 0xb060000041e77cc4 0xdb060000041e77cc

def z1222 : W := mkw 0x39622604f7ff3ccc 0x239622604f7ff3cc 0xbfe00e007fff7cce 0xfbfe00e007fff7cc

def z1223 : W := mkw 0x3ddfa004f7ff3ccc 0x23ddfa004f7ff3cc 0xbf9800007fff7ccc 0x2bf9800007fff7cc

def z1224 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x4e66ee1f80000002 0x44e66ee1f8000000

def z1225 : W := mkw 0x2ddfa0a277be011c 0x42ddfa0a277be011 0xafffe0607fff003d 0xfafffe0607fff003

def z1226 : W := mkw 0x4fddd9fb00000000 0x04fddd9fb0000000 0x4e1fe07f80000001 0x04e1fe07f8000000

def z1227 : W := mkw 0x0616385458b2d0a6 0x80616385458b2d0a 0xde7efc7c79f8f0ff 0x7de7efc7c79f8f0f

def z1228 : W := mkw 0x4ffddffb3d50ea23 0x84ffddffb3d50ea2 0xffffffffffd8ff3f 0xfffffffffffd8ff3

def z1229 : W := mkw 0x1020660d80c33cc4 0x21020660d80c33cc 0x7067ee1f81c77cc3 0xd7067ee1f81c77cc

def z1230 : W := mkw 0x4ffddffb020c0008 0x04ffddffb020c000 0x7fffffff863f80ff 0xf7fffffff863f80f

def z1231 : W := mkw 0x46bddffb0840ea03 0x046bddffb0840ea0 0x501fffff8000ff03 0x0501fffff8000ff0

def z1232 : W := mkw 0x19422004e5e33cc4 0x219422004e5e33cc 0xbfe000007fe77ccc 0xfbfe000007fe77cc

def z1233 : W := mkw 0x4f74dffb2d40ea03 0x04f74dffb2d40ea0 0xde66fffff9c0ff02 0x4de66fffff9c0ff0

def z1234 : W := mkw 0x0b605f092d00c203 0x00b605f092d00c20 0x4fe7ff9fbe00830b 0xf4fe7ff9fbe00830

def z1235 : W := mkw 0x6ffddffb270c0008 0x06ffddffb270c000 0x4fffffff86000003 0xf4fffffff8600000

def z1236 : W := mkw 0x4ffddffb0840ea03 0x04ffddffb0840ea0 0xdffffffff800ff0f 0xfdffffffff800ff0

def z1237 : W := mkw 0x2ddda000379e000c 0x02ddda000379e000 0x2fe1e0003fc70000 0x82fe1e0003fc7000

def z1238 : W := mkw 0x4dddc1fb00000000 0x04dddc1fb0000000 0x419fe1ff80000001 0x0419fe1ff8000000

def z1239 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x4fe7ff9f80000003 0xf4fe7ff9f8000000

def z1240 : W := mkw 0x4ffddffb0800c022 0x84ffddffb0800c02 0x4fffffff80008033 0xf4fffffff8000803

def z1241 : W := mkw 0x449dc0fb020c0008 0x0449dc0fb020c000 0x401fe07f803f0001 0x0401fe07f803f000

def z1242 : W := mkw 0x0d56200075b20004 0x00d56200075b2000 0xafffe0007fff000d 0xfafffe0007fff000

def z1243 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0x8e7fe00079ff000d 0x78e7fe00079ff000

def z1244 : W := mkw 0x00a946ab00000000 0x000a946ab0000000 0x407fee7f80000003 0xd407fee7f8000000

def z1245 : W := mkw 0x4ffddffb020c0118 0x44ffddffb020c011 0x4fffffff80180033 0xf4fffffff8018003

def z1246 : W := mkw 0x0ffdde5900000000 0x00ffdde590000000 0x4ffffe7f80000003 0xf4ffffe7f8000000

def z1247 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0x5e1e1c7c3838f0fb 0x25e1e1c7c3838f0f

def z1248 : W := mkw 0x10222604c2ef3ddc 0x610222604c2ef3dd 0xb1e01f8047fffffe 0xfb1e01f8047fffff

def z1249 : W := mkw 0x469dd8fb00000000 0x0469dd8fb0000000 0x4e1ff07f80000001 0x24e1ff07f8000000

def z1250 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x401fe27f80000003 0x9401fe27f8000000

def z1251 : W := mkw 0x108b20a6c2ef3ddc 0x6108b20a6c2ef3dd 0xb19811e047fffffc 0x2b19811e047fffff

def z1252 : W := mkw 0x4ffddffb25402a01 0x04ffddffb25402a0 0xefffffffffc00f0f 0xfefffffffffc00f0

def z1253 : W := mkw 0x6ffddffb3f1cc20b 0x06ffddffb3f1cc20 0x4fffffffbe18830b 0xf4fffffffbe18830

def z1254 : W := mkw 0x449dc0fb00000000 0x0449dc0fb0000000 0x407fe07f80000001 0xd407fe07f8000000

def z1255 : W := mkw 0x0b605f092d40ea03 0x00b605f092d40ea0 0xbfe6ff9c7fc0ff0e 0xfbfe6ff9c7fc0ff0

def z1256 : W := mkw 0x469dd8fb00000000 0x0469dd8fb0000000 0x4f9fffff80000003 0xf4f9fffff8000000

def z1257 : W := mkw 0x0020460900402800 0x0002046090040280 0xc067ee1fc1c07003 0xdc067ee1fc1c0700

def z1258 : W := mkw 0x4ffddffb00000110 0x44ffddffb0000011 0x4fffffff80008333 0xf4fffffff8000833

def z1259 : W := mkw 0x0616385458b2d0a6 0x80616385458b2d0a 0xde1ffc7c783ff0ff 0x7de1ffc7c783ff0f

def z1260 : W := mkw 0x42a95ffb00000000 0x042a95ffb0000000 0x41ffffff80000003 0xf41ffffff8000000

def z1261 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4e7ffc7f80000003 0x74e7ffc7f8000000

def z1262 : W := mkw 0x4ffddffb0840ea03 0x04ffddffb0840ea0 0x7fffffff8600ff0f 0xf7fffffff8600ff0

def z1263 : W := mkw 0x10022004c2ef3ddc 0x610022004c2ef3dd 0xb000000047e77fc4 0x0b000000047e77fc

def z1264 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xae7fe00079ff0005 0xdae7fe00079ff000

def z1265 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xde1e1ffc7838ffff 0x7de1e1ffc7838fff

def z1266 : W := mkw 0x0614585900000000 0x0061458590000000 0x4e1ffc7f80000003 0x74e1ffc7f8000000

def z1267 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x0fe7ff9f80000002 0xf0fe7ff9f8000000

def z1268 : W := mkw 0x2d56a00077be000c 0x02d56a00077be000 0xae7ee0007fff000d 0x7ae7ee0007fff000

def z1269 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4fffffff8038000f 0xf4fffffff8038000

def z1270 : W := mkw 0x12205eff8841fdf2 0xe12205eff8841fdf 0x50001fff8000fff2 0x050001fff8000fff

def z1271 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x4e7fee7f80000003 0xd4e7fee7f8000000

def z1272 : W := mkw 0x4ffddffb2d40ea03 0x04ffddffb2d40ea0 0x5fffffffbe00ff0b 0xf5fffffffbe00ff0

def z1273 : W := mkw 0x2fffff097ffeea0f 0x02fffff097ffeea0 0xffffff9fffffff0f 0xfffffff9fffffff0

def z1274 : W := mkw 0x1022660dc0e33cc4 0x21022660dc0e33cc 0xf1e7ee1fc7e77ccf 0xff1e7ee1fc7e77cc

def z1275 : W := mkw 0x1b623f04ede3fec7 0x21b623f04ede3fec 0xbe600c0079e77cc4 0x4be600c0079e77cc

def z1276 : W := mkw 0x0020460900402800 0x0002046090040280 0x5067ee1f80007c03 0xd5067ee1f80007c0

def z1277 : W := mkw 0x12223f04c8e3fec7 0x212223f04c8e3fec 0xb0001f8041e7ffc6 0x0b0001f8041e7ffc

def z1278 : W := mkw 0x4dfdc7fb00000000 0x04dfdc7fb0000000 0x407fe07f80000001 0x0407fe07f8000000

def z1279 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xaffff0607fff803d 0xfaffff0607fff803

def z1280 : W := mkw 0x4dfdc7fb00000000 0x04dfdc7fb0000000 0x41ffefff80000003 0xd41ffefff8000000

def z1281 : W := mkw 0x649dc0fb121c0008 0x0649dc0fb121c000 0x401fe07f80180001 0x0401fe07f8018000

def z1282 : W := mkw 0x0942200065a20004 0x00942200065a2000 0xae67e00079e70005 0xdae67e00079e7000

def z1283 : W := mkw 0x30022004d2bf14cc 0x230022004d2bf14c 0x00000000003f00c0 0x000000000003f00c

def z1284 : W := mkw 0x4960c70900000000 0x04960c7090000000 0x4067ee1f80000003 0xd4067ee1f8000000

def z1285 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xce1e0c7c783870fd 0x7ce1e0c7c783870f

def z1286 : W := mkw 0x2ddfa00077be000c 0x02ddfa00077be000 0xafffe3807fff0f0d 0xfafffe3807fff0f0

def z1287 : W := mkw 0x2d56a00075b20004 0x02d56a00075b2000 0xae7fe00079ff000d 0xfae7fe00079ff000

def z1288 : W := mkw 0x00a9460900000000 0x000a946090000000 0x41ffee1f80000003 0xf41ffee1f8000000

def z1289 : W := mkw 0x0000000080010440 0x0000000008001044 0x719913e3863f8fff 0xb719913e3863f8ff

def z1290 : W := mkw 0x4ffddffb1a1cc13a 0xc4ffddffb1a1cc13 0x4fffffffbe18833b 0xf4fffffffbe18833

def z1291 : W := mkw 0x4ffddffb0840ea03 0x04ffddffb0840ea0 0x4fffffff80007003 0xf4fffffff8000700

def z1292 : W := mkw 0x46bddefb00000000 0x046bddefb0000000 0x4e7ffe7f80000003 0xf4e7ffe7f8000000

def z1293 : W := mkw 0x4ffddffb25402a01 0x04ffddffb25402a0 0xffffffffc7c07f07 0xfffffffffc7c07f0

def z1294 : W := mkw 0x04160054503010a0 0x804160054503010a 0x00180060003800f0 0x000180060003800f

def z1295 : W := mkw 0x4dddc0fb25000000 0x04dddc0fb2500000 0xefffe07fffc0000d 0xfefffe07fffc0000

def z1296 : W := mkw 0x09e9c60900000000 0x009e9c6090000000 0x41e7ee1f80000003 0xd41e7ee1f8000000

def z1297 : W := mkw 0x2416200077be000c 0x02416200077be000 0xae7fe0007fff000d 0xfae7fe0007fff000

def z1298 : W := mkw 0x096007002d40ea03 0x0096007002d40ea0 0xbfe003807fc0ff0c 0xfbfe003807fc0ff0

def z1299 : W := mkw 0x0b601f002d40ea03 0x00b601f002d40ea0 0xafe01f807fc07f02 0xfafe01f807fc07f0

def z1300 : W := mkw 0x29c9a000278e000c 0x029c9a000278e000 0xaff9e0007fff000d 0xfaff9e0007fff000

def z1301 : W := mkw 0x061618545830d0a2 0x8061618545830d0a 0xce1e1c7c7838f0f9 0x6ce1e1c7c7838f0f

def z1302 : W := mkw 0x4ffddffb00000000 0x04ffddffb0000000 0x6fffffff8600000f 0xf6fffffff8600000

def z1303 : W := mkw 0x020018000800c002 0x0020018000800c00 0xde061c1c7800f00f 0x7de061c1c7800f00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z6,z7]),(0,[z0,z1,z2,z3,z8,z4,z7]),(0,[z9,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z10]),(0,[z0,z1,z11,z2,z3,z4,z7]),(0,[z12,z0,z1,z2,z13,z3,z4])],[(0,[z0,z14,z1,z2,z3,z4,z7]),(0,[z0,z15,z2,z16,z3,z4,z7]),(0,[z0,z1,z17,z2,z3,z4,z7]),(0,[z0,z1,z2,z18,z3,z4,z7])],[(0,[z19,z0,z20,z2,z3,z4,z7]),(0,[z0,z1,z2,z21,z3,z4,z7]),(0,[z0,z1,z2,z22,z3,z4,z23])],[(0,[z0,z1,z2,z24,z3,z4,z7]),(0,[z0,z1,z2,z3,z25,z4,z7]),(0,[z0,z1,z2,z26,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z27]),(0,[z0,z1,z2,z3,z4,z27,z7]),(0,[z28,z0,z1,z2,z3,z4,z29]),(0,[z30,z0,z1,z2,z3,z4,z29]),(0,[z31,z0,z1,z2,z3,z4,z32])],[(0,[z0,z33,z1,z2,z3,z4,z7]),(0,[z19,z0,z34,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z35,z7]),(0,[z36,z0,z1,z2,z13,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z37]),(0,[z0,z1,z2,z3,z4,z38,z7]),(0,[z39,z0,z1,z2,z3,z4,z7]),(0,[z0,z40,z1,z2,z22,z4,z7]),(0,[z41,z0,z1,z2,z3,z4,z7])],[(0,[z31,z0,z42,z1,z2,z3,z4]),(0,[z43,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z44,z7])],[(0,[z45,z0,z1,z2,z3,z4,z29]),(0,[z0,z2,z22,z3,z46,z4,z7]),(0,[z47,z0,z1,z2,z3,z4,z48]),(0,[z0,z1,z2,z49,z3,z4,z7]),(0,[z0,z1,z2,z50,z4,z51,z7]),(0,[z0,z1,z52,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z53,z4,z7]),(0,[z0,z1,z2,z3,z54,z4,z7]),(0,[z0,z55,z1,z2,z3,z4,z7]),(0,[z56,z0,z42,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z57,z4,z7]),(0,[z0,z1,z2,z3,z4,z23,z58]),(0,[z56,z0,z1,z2,z49,z4,z7])]],
   [[(1,[z59,z1,z2,z60,z4,z7]),(0,[z0,z61,z62,z2,z3,z4,z7]),(0,[z0,z63,z1,z2,z3,z4,z64]),(0,[z0,z65,z1,z2,z3,z4,z66]),(0,[z67,z31,z0,z1,z2,z3,z4])],[(0,[z68,z0,z1,z2,z3,z4,z69]),(0,[z70,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z71,z4,z7]),(0,[z12,z0,z1,z72,z3,z4,z7]),(0,[z0,z1,z3,z73,z4,z74,z7]),(0,[z0,z1,z2,z3,z4,z75,z7]),(0,[z0,z1,z2,z3,z4,z29,z76])],[(0,[z77,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z78]),(0,[z68,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z79,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z80]),(1,[z0,z1,z2,z3,z4,z81]),(0,[z0,z1,z3,z82,z4,z7,z29]),(0,[z0,z1,z2,z83,z3,z4,z29]),(0,[z56,z0,z1,z2,z3,z4,z7]),(0,[z0,z84,z1,z2,z3,z4,z7])],[(0,[z0,z1,z85,z2,z3,z4,z7]),(0,[z0,z2,z3,z4,z64,z7,z86]),(0,[z0,z1,z72,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z87,z4,z7]),(0,[z0,z1,z2,z88,z3,z4,z23])],[(0,[z89,z0,z90,z2,z3,z4,z7]),(0,[z0,z91,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z92,z7]),(0,[z0,z1,z2,z13,z3,z4,z93]),(0,[z0,z61,z1,z62,z3,z4,z7]),(0,[z0,z1,z2,z83,z3,z4,z7]),(0,[z0,z94,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z50,z4,z95])],[(0,[z96,z0,z1,z2,z3,z4,z7]),(1,[z0,z97,z1,z2,z3,z7]),(0,[z0,z42,z1,z2,z3,z98,z7]),(1,[z0,z1,z2,z3,z4,z99]),(0,[z0,z1,z2,z3,z4,z29,z100]),(0,[z31,z0,z1,z2,z3,z50,z4])],[(0,[z0,z61,z90,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z101,z4,z7]),(0,[z102,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z103,z4,z7]),(0,[z0,z1,z2,z3,z4,z104,z7]),(1,[z36,z1,z2,z105,z4,z7]),(0,[z0,z1,z2,z3,z98,z106,z7]),(0,[z0,z107,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z108,z7]),(0,[z31,z0,z1,z2,z4,z7,z109])],[(0,[z110,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z111,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z112,z7]),(0,[z0,z1,z2,z3,z113,z4,z7]),(1,[z0,z1,z2,z3,z4,z114]),(0,[z0,z1,z2,z13,z3,z4,z23]),(0,[z56,z0,z1,z2,z3,z50,z7])]],
   [[(0,[z115,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z116,z7]),(0,[z0,z1,z2,z3,z4,z64,z93]),(0,[z0,z117,z1,z2,z3,z4,z7]),(0,[z0,z118,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z119,z7]),(0,[z0,z1,z2,z3,z120,z4,z7])],[(0,[z89,z0,z1,z2,z3,z4,z23])],[(0,[z0,z1,z2,z3,z121,z4,z7]),(0,[z122,z0,z1,z2,z3,z4,z7]),(0,[z123,z0,z1,z2,z3,z4,z23])],[(1,[z0,z1,z2,z124,z4,z7]),(0,[z125,z0,z1,z2,z3,z4,z23]),(0,[z0,z40,z1,z2,z3,z4,z10]),(0,[z31,z0,z65,z1,z2,z3,z4]),(0,[z0,z126,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z127,z7]),(0,[z36,z0,z1,z2,z105,z4,z7]),(0,[z0,z1,z2,z3,z4,z128,z7])],[(1,[z0,z1,z2,z3,z4,z129]),(0,[z130,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z131,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z132]),(0,[z56,z0,z65,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z7,z76])],[(0,[z0,z1,z2,z3,z124,z4,z7]),(0,[z0,z133,z1,z2,z3,z4,z7]),(0,[z0,z1,z134,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z135]),(0,[z0,z1,z136,z2,z3,z4,z7]),(0,[z0,z1,z137,z2,z3,z4,z7]),(0,[z0,z1,z2,z13,z13,z3,z4])],[(0,[z138,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z139,z4,z7]),(0,[z0,z1,z2,z3,z140,z4,z7]),(0,[z0,z141,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z13,z3,z4,z58])]],
   [[(0,[z89,z0,z1,z2,z13,z3,z4]),(0,[z0,z1,z142,z2,z3,z4,z7]),(0,[z143,z0,z1,z2,z3,z4,z7]),(0,[z31,z36,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z144,z4,z23]),(0,[z145,z0,z1,z2,z3,z4,z7]),(0,[z0,z97,z1,z2,z3,z4,z7]),(1,[z0,z1,z146,z3,z4,z29]),(1,[z0,z147,z2,z3,z4,z7]),(0,[z31,z0,z1,z2,z13,z4,z7])],[(0,[z36,z0,z1,z2,z60,z4,z7]),(0,[z0,z148,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z22,z105,z4,z7]),(1,[z149,z1,z2,z3,z106,z7]),(0,[z0,z1,z2,z3,z4,z7,z100]),(0,[z123,z0,z1,z2,z13,z3,z4]),(0,[z47,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z150,z3,z4,z29]),(0,[z31,z0,z1,z2,z3,z151,z4])],[(0,[z125,z0,z1,z2,z13,z3,z4]),(1,[z0,z152,z16,z3,z4,z7]),(0,[z0,z1,z2,z153,z3,z4,z7]),(0,[z0,z61,z1,z2,z13,z3,z4]),(0,[z0,z42,z2,z3,z4,z154,z7]),(0,[z0,z1,z155,z2,z3,z4,z7]),(0,[z0,z1,z2,z156,z3,z4,z51]),(0,[z0,z1,z2,z3,z4,z7,z157]),(0,[z0,z1,z2,z3,z158,z4,z7])],[(0,[z159,z0,z1,z2,z3,z4,z7]),(1,[z45,z0,z2,z46,z4,z7]),(0,[z0,z1,z2,z13,z3,z98,z4]),(0,[z0,z1,z2,z3,z4,z29,z86]),(0,[z47,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z150,z3,z4,z7]),(0,[z160,z0,z1,z2,z3,z4,z7]),(0,[z31,z0,z1,z2,z161,z3,z4])],[(0,[z0,z63,z1,z2,z3,z4,z86]),(0,[z0,z1,z2,z162,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z163,z7]),(1,[z0,z1,z2,z13,z4,z58])],[(0,[z31,z0,z1,z2,z16,z3,z4]),(0,[z45,z0,z1,z2,z22,z4,z7]),(0,[z0,z1,z2,z13,z49,z3,z4])],[(0,[z0,z1,z2,z22,z60,z4,z7]),(0,[z0,z164,z1,z2,z3,z4,z7]),(0,[z0,z1,z165,z2,z3,z4,z7]),(0,[z0,z65,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z166,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z23])],[(0,[z89,z15,z1,z2,z3,z4,z7]),(0,[z19,z0,z1,z2,z3,z167,z7]),(0,[z0,z1,z2,z168,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z7,z7]),(0,[z0,z1,z2,z3,z4,z7,z169]),(0,[z0,z1,z2,z3,z4,z170,z7]),(0,[z171,z0,z1,z2,z13,z3,z4]),(0,[z172,z0,z1,z2,z13,z3,z4])]],
   [[(0,[z0,z1,z173,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z174,z7]),(0,[z0,z1,z2,z3,z175,z4,z7]),(0,[z0,z1,z2,z176,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z93,z29]),(0,[z0,z1,z177,z2,z3,z4,z29]),(0,[z178,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z13,z3,z3,z4])],[(0,[z0,z179,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z180,z7]),(0,[z0,z1,z2,z3,z4,z181,z7]),(1,[z31,z0,z1,z2,z13,z4]),(0,[z0,z182,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z151,z4,z183])],[(0,[z0,z184,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z185,z4,z7]),(0,[z0,z1,z177,z2,z3,z4,z7]),(0,[z0,z1,z2,z2,z3,z4,z29]),(0,[z31,z0,z1,z186,z2,z3,z4]),(0,[z31,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z187,z2,z3,z4,z7])],[(0,[z0,z1,z188,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z189,z4,z7]),(0,[z0,z1,z2,z3,z190,z4,z7]),(0,[z0,z1,z191,z2,z3,z4,z7])],[(0,[z0,z1,z90,z2,z3,z4,z23]),(1,[z0,z1,z2,z3,z167,z7]),(0,[z0,z1,z2,z3,z73,z106,z7]),(1,[z0,z1,z2,z3,z192,z7]),(0,[z0,z1,z2,z3,z193,z4,z7]),(0,[z12,z31,z0,z1,z2,z3,z4]),(1,[z0,z1,z2,z13,z3,z4])],[(0,[z36,z0,z1,z2,z3,z194,z7]),(0,[z195,z0,z1,z2,z3,z4,z29]),(0,[z0,z196,z1,z2,z3,z4,z7]),(0,[z197,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z146,z2,z3,z4,z23]),(0,[z31,z0,z1,z186,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z198])],[(0,[z199,z0,z1,z2,z3,z4,z7]),(0,[z200,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z201,z3,z4,z7]),(0,[z202,z0,z1,z2,z3,z4,z93]),(0,[z0,z1,z2,z3,z4,z7,z86])]],
   [[(1,[z0,z1,z2,z3,z4,z203]),(0,[z31,z0,z1,z2,z105,z3,z4]),(0,[z56,z0,z1,z2,z4,z51,z7]),(0,[z0,z1,z2,z204,z13,z3,z4])],[(0,[z0,z1,z2,z3,z98,z144,z7]),(1,[z202,z1,z2,z3,z4,z93]),(0,[z0,z65,z1,z2,z3,z74,z7]),(0,[z0,z1,z2,z3,z205,z4,z7])],[(0,[z0,z1,z146,z3,z4,z7,z29])],[(1,[z0,z1,z2,z3,z4,z206]),(0,[z0,z1,z2,z207,z3,z4,z7]),(0,[z31,z0,z1,z2,z3,z46,z4]),(0,[z0,z208,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z209,z7])],[(0,[z0,z1,z90,z2,z13,z3,z4]),(0,[z210,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z211,z4,z7]),(0,[z0,z1,z2,z13,z3,z4,z51])],[(0,[z0,z1,z2,z3,z4,z212,z7]),(0,[z0,z1,z2,z213,z3,z4,z7]),(0,[z214,z0,z1,z2,z3,z4,z7]),(0,[z215,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z5]),(0,[z0,z1,z2,z3,z151,z144,z7]),(1,[z0,z1,z2,z216,z3,z4]),(0,[z0,z1,z177,z2,z3,z74,z7]),(0,[z0,z1,z2,z3,z4,z217,z7]),(0,[z0,z1,z146,z2,z13,z3,z4]),(0,[z0,z1,z2,z218,z3,z4,z7]),(0,[z219,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z220,z7]),(0,[z59,z0,z1,z2,z3,z4,z23]),(0,[z0,z221,z42,z2,z3,z4,z7]),(0,[z222,z31,z0,z1,z2,z3,z4])],[(0,[z223,z0,z1,z2,z224,z4,z7]),(0,[z0,z1,z2,z3,z4,z225,z7]),(0,[z149,z0,z1,z2,z3,z106,z7]),(0,[z0,z226,z1,z2,z13,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z227,z7]),(0,[z0,z1,z2,z3,z98,z4,z23]),(0,[z0,z1,z2,z3,z228,z4,z7]),(0,[z0,z1,z2,z3,z4,z183,z7])],[(0,[z0,z1,z2,z13,z3,z144,z4]),(0,[z0,z1,z2,z3,z4,z7,z229]),(0,[z0,z1,z2,z230,z3,z4,z7]),(0,[z67,z0,z1,z2,z230,z3,z4]),(0,[z0,z65,z1,z177,z3,z4,z7]),(0,[z0,z231,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z13,z3,z4,z232])],[(0,[z0,z233,z1,z2,z3,z4,z7]),(0,[z234,z0,z1,z2,z3,z4,z7]),(0,[z0,z40,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z235,z7])],[(1,[z0,z1,z2,z224,z4,z7]),(0,[z236,z0,z1,z2,z3,z4,z7]),(0,[z0,z42,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z237,z7]),(0,[z0,z1,z2,z3,z4,z238,z7]),(0,[z0,z1,z72,z2,z82,z4,z7]),(1,[z0,z1,z2,z3,z4,z239]),(1,[z0,z1,z2,z150,z3,z4]),(0,[z0,z231,z1,z2,z3,z4,z7])],[(0,[z0,z1,z188,z2,z3,z4,z240]),(0,[z0,z241,z1,z2,z3,z4,z7]),(0,[z31,z242,z0,z1,z2,z3,z4])],[(0,[z59,z0,z1,z2,z13,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z243]),(0,[z0,z1,z2,z244,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z245,z7]),(0,[z0,z1,z2,z13,z22,z3,z4]),(0,[z242,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z177,z2,z3,z4,z246]),(0,[z0,z1,z2,z3,z247,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z248])],[(0,[z0,z15,z1,z2,z3,z4,z7]),(0,[z0,z249,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z250,z4,z7]),(0,[z0,z1,z2,z251,z3,z4,z7])]],
   [[(0,[z252,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z253,z4,z7]),(0,[z12,z0,z1,z146,z3,z4,z7]),(0,[z254,z31,z0,z1,z2,z3,z4]),(0,[z31,z0,z1,z161,z3,z4,z7]),(0,[z255,z0,z1,z2,z3,z4,z7])],[(1,[z56,z0,z1,z2,z51,z7]),(0,[z256,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z257,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z106,z7]),(0,[z0,z1,z2,z258,z3,z4,z7])],[(0,[z259,z0,z1,z2,z3,z4,z7]),(1,[z0,z260,z1,z2,z3,z4]),(0,[z0,z97,z1,z2,z3,z46,z7]),(0,[z0,z1,z2,z261,z3,z4,z7]),(1,[z123,z0,z2,z3,z4,z64]),(0,[z0,z1,z262,z2,z3,z4,z7])],[(0,[z19,z0,z1,z2,z3,z263,z7]),(0,[z0,z1,z2,z3,z4,z7,z264]),(0,[z0,z1,z2,z265,z3,z4,z7])],[(0,[z0,z1,z2,z3,z60,z4,z7]),(0,[z0,z1,z2,z3,z4,z266,z7]),(0,[z0,z1,z2,z3,z4,z129,z7]),(0,[z267,z0,z1,z2,z3,z4,z7]),(0,[z268,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z151,z4,z29]),(0,[z0,z269,z1,z2,z3,z4,z23])],[(0,[z0,z1,z2,z3,z4,z7,z270]),(0,[z0,z152,z1,z2,z3,z4,z29]),(0,[z271,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z13,z3,z82,z4]),(0,[z0,z1,z2,z49,z50,z4,z7]),(0,[z0,z1,z2,z3,z4,z272,z7])],[(0,[z273,z0,z1,z2,z3,z4,z7]),(0,[z274,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z3,z4,z23,z7,z29]),(0,[z0,z1,z2,z3,z4,z51,z23]),(0,[z0,z1,z2,z13,z3,z4,z183]),(0,[z275,z0,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z73,z144,z7]),(0,[z0,z1,z2,z3,z4,z69,z76]),(0,[z0,z63,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z23,z276])],[(0,[z0,z1,z2,z3,z4,z7,z277]),(0,[z0,z1,z2,z278,z3,z4,z7])],[(1,[z0,z1,z2,z3,z263,z7]),(0,[z0,z1,z62,z188,z3,z4,z7])],[(0,[z279,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z280,z2,z3,z4,z7]),(0,[z0,z281,z1,z2,z3,z4,z7]),(0,[z31,z0,z1,z62,z2,z3,z4]),(0,[z282,z0,z1,z2,z3,z4,z7]),(0,[z47,z0,z1,z2,z82,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z283]),(0,[z284,z0,z1,z2,z3,z4,z7]),(0,[z0,z285,z1,z2,z3,z4,z7])],[(0,[z19,z31,z0,z1,z2,z3,z4]),(0,[z286,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z287])],[(0,[z0,z1,z2,z105,z3,z4,z29]),(0,[z222,z0,z1,z2,z3,z4,z23])],[(0,[z223,z0,z1,z2,z3,z4,z288]),(0,[z223,z31,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z289]),(0,[z0,z1,z2,z3,z4,z290,z7]),(0,[z0,z1,z2,z3,z4,z7,z291]),(0,[z0,z221,z1,z2,z49,z3,z7]),(0,[z0,z292,z1,z2,z3,z4,z7]),(0,[z293,z0,z1,z2,z13,z3,z4])],[(0,[z294,z0,z1,z2,z3,z4,z7]),(0,[z295,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z194,z7]),(0,[z0,z1,z2,z296,z3,z4,z7]),(0,[z0,z1,z2,z297,z3,z4,z7]),(0,[z0,z63,z1,z2,z13,z3,z4]),(0,[z0,z1,z2,z3,z73,z4,z23]),(0,[z0,z1,z2,z3,z4,z298,z29]),(1,[z31,z0,z1,z161,z3,z4])]],
   [[(0,[z30,z0,z1,z2,z3,z4,z7]),(0,[z0,z61,z1,z2,z3,z8,z7]),(0,[z28,z0,z1,z2,z3,z4,z7])],[(0,[z299,z0,z1,z2,z3,z4,z7]),(0,[z36,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z300,z3,z4,z7]),(0,[z31,z0,z1,z2,z3,z4,z106]),(0,[z0,z1,z2,z3,z301,z4,z7]),(0,[z302,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z82,z4,z23]),(0,[z303,z0,z1,z2,z3,z4,z7]),(0,[z0,z304,z1,z2,z3,z4,z7])],[(1,[z0,z1,z2,z3,z4,z288]),(0,[z59,z0,z1,z2,z60,z4,z7]),(0,[z0,z1,z2,z3,z4,z23,z69]),(0,[z0,z305,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z306,z7]),(0,[z0,z307,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z308,z7]),(0,[z0,z1,z2,z3,z4,z309,z7]),(1,[z31,z0,z1,z2,z3,z4])],[(0,[z31,z0,z1,z2,z3,z4,z93]),(0,[z310,z0,z1,z2,z3,z4,z7]),(0,[z45,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z23,z29]),(0,[z0,z1,z2,z3,z311,z4,z7]),(0,[z0,z1,z2,z258,z3,z151,z7])],[(0,[z0,z1,z1,z2,z3,z4,z7]),(0,[z312,z0,z1,z2,z3,z4,z7]),(0,[z0,z152,z1,z2,z3,z4,z313]),(0,[z0,z1,z2,z13,z3,z4,z154]),(0,[z222,z0,z1,z2,z13,z3,z4])],[(0,[z0,z152,z2,z16,z3,z4,z7]),(0,[z0,z1,z2,z3,z314,z4,z7])],[(0,[z0,z1,z2,z315,z3,z4,z7]),(0,[z0,z1,z2,z22,z3,z4,z29]),(0,[z0,z1,z2,z216,z3,z82,z4]),(0,[z0,z1,z2,z3,z4,z316,z7]),(0,[z0,z1,z317,z2,z3,z4,z7])],[(0,[z0,z1,z2,z318,z3,z4,z7]),(0,[z1,z2,z3,z144,z4,z106,z7]),(0,[z68,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z72,z2,z230,z4,z7]),(0,[z0,z1,z2,z13,z3,z319,z4])]],
   [[(0,[z0,z1,z2,z320,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z321]),(0,[z0,z1,z2,z3,z4,z322,z7]),(0,[z0,z1,z2,z3,z323,z4,z7]),(1,[z0,z221,z2,z3,z98,z7]),(0,[z324,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z325,z2,z3,z4,z7]),(0,[z149,z0,z1,z2,z3,z4,z23]),(0,[z0,z2,z3,z46,z4,z154,z7]),(0,[z0,z1,z2,z13,z3,z73,z4])],[(0,[z223,z0,z1,z2,z124,z4,z7]),(0,[z0,z1,z2,z3,z4,z69,z86]),(0,[z0,z1,z2,z3,z4,z326,z29]),(0,[z0,z1,z2,z3,z4,z23,z109])],[(0,[z125,z1,z188,z2,z3,z4,z7]),(0,[z0,z1,z2,z49,z3,z106,z7]),(0,[z0,z61,z1,z16,z3,z4,z7]),(1,[z0,z1,z2,z3,z8,z7]),(0,[z0,z1,z2,z3,z327,z4,z7]),(0,[z328,z0,z1,z2,z3,z4,z7]),(0,[z329,z0,z1,z2,z3,z4,z7]),(1,[z0,z330,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z331,z7]),(0,[z0,z332,z1,z2,z3,z4,z7]),(0,[z202,z68,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z326,z7]),(0,[z0,z1,z2,z3,z4,z333,z7])],[(0,[z0,z1,z334,z2,z3,z4,z7]),(0,[z335,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z336,z4,z7]),(0,[z0,z1,z2,z3,z4,z29,z337]),(1,[z12,z0,z1,z3,z4,z23])],[(0,[z0,z1,z338,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z339,z7]),(0,[z0,z61,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z46,z4,z23]),(0,[z0,z1,z2,z3,z340,z4,z7]),(0,[z0,z1,z2,z3,z341,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z342])],[(0,[z0,z1,z343,z2,z3,z4,z7]),(0,[z344,z0,z1,z2,z3,z4,z7]),(0,[z56,z0,z1,z2,z3,z106,z7]),(0,[z345,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z346,z3,z4,z7]),(0,[z0,z1,z2,z3,z347,z4,z7])]],
   [[(0,[z223,z0,z90,z2,z3,z4,z7]),(0,[z15,z1,z90,z2,z3,z4,z7]),(0,[z89,z0,z15,z2,z3,z4,z7]),(0,[z149,z0,z1,z2,z13,z3,z4]),(0,[z0,z1,z2,z3,z348,z4,z7]),(0,[z0,z1,z2,z349,z3,z4,z7]),(0,[z0,z350,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z351,z3,z4,z7])],[(0,[z352,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z183,z93]),(0,[z31,z0,z1,z2,z3,z4,z64]),(0,[z0,z1,z2,z3,z4,z353,z7]),(0,[z0,z1,z2,z3,z50,z4,z23]),(0,[z0,z354,z1,z2,z3,z4,z7]),(0,[z355,z0,z1,z2,z3,z4,z7])],[(0,[z59,z31,z0,z1,z2,z3,z4]),(0,[z31,z0,z1,z2,z3,z60,z4]),(0,[z0,z1,z2,z356,z3,z4,z7]),(0,[z195,z1,z2,z3,z144,z4,z7]),(0,[z0,z1,z2,z13,z3,z4,z69]),(0,[z0,z357,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z358,z7]),(0,[z31,z0,z1,z72,z2,z3,z4]),(0,[z359,z0,z1,z2,z3,z4,z7]),(0,[z0,z360,z1,z2,z3,z4,z7])],[(0,[z19,z0,z1,z2,z3,z4,z23]),(0,[z361,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z362,z7]),(0,[z31,z0,z1,z2,z3,z4,z76]),(0,[z0,z1,z363,z2,z3,z4,z7])],[(0,[z31,z149,z0,z1,z2,z3,z4]),(0,[z0,z364,z1,z2,z3,z4,z7]),(0,[z365,z0,z1,z2,z3,z4,z29]),(0,[z31,z0,z1,z2,z49,z3,z4]),(0,[z41,z31,z0,z1,z2,z3,z4])],[(0,[z223,z0,z1,z2,z3,z4,z23]),(0,[z89,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z366,z2,z3,z4,z7]),(0,[z0,z1,z367,z2,z3,z4,z7]),(0,[z0,z1,z2,z368,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z154,z23]),(0,[z0,z1,z2,z3,z369,z4,z7]),(0,[z370,z0,z1,z2,z3,z4,z7])],[(0,[z125,z0,z1,z168,z3,z4,z7]),(0,[z36,z1,z2,z105,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z64,z69]),(0,[z0,z1,z2,z3,z4,z7,z371]),(0,[z123,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z372,z51]),(0,[z0,z1,z2,z3,z4,z7,z373]),(0,[z0,z1,z2,z374,z3,z4,z7])],[(0,[z0,z1,z2,z3,z263,z4,z7]),(0,[z125,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z188,z2,z3,z4,z375]),(0,[z0,z1,z62,z2,z3,z4,z376]),(0,[z0,z1,z2,z13,z3,z4,z74]),(1,[z0,z1,z2,z3,z151,z183])]],
   [[(0,[z0,z1,z2,z377,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z378,z7]),(0,[z0,z1,z2,z3,z4,z379,z7])],[(0,[z0,z1,z2,z3,z4,z7,z337]),(0,[z0,z380,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z349,z3,z46,z4]),(0,[z0,z221,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z98,z51,z7])],[(0,[z0,z1,z20,z2,z3,z4,z7]),(0,[z19,z0,z1,z2,z13,z3,z4]),(0,[z0,z65,z1,z2,z3,z154,z7]),(0,[z56,z31,z0,z1,z2,z3,z4]),(0,[z31,z0,z1,z2,z258,z3,z4]),(0,[z0,z1,z2,z13,z3,z4,z109]),(0,[z0,z1,z2,z258,z3,z7,z76])],[(0,[z0,z1,z2,z3,z4,z167,z7]),(0,[z381,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z192,z7])],[(0,[z223,z0,z1,z2,z13,z3,z4]),(0,[z0,z1,z2,z168,z3,z4,z7]),(0,[z0,z1,z2,z3,z144,z4,z29]),(0,[z382,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z383,z7]),(0,[z0,z1,z2,z13,z230,z3,z4])],[(0,[z19,z0,z1,z2,z3,z4,z203]),(0,[z0,z384,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z93,z7]),(1,[z0,z40,z2,z22,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z385])],[(0,[z0,z1,z2,z3,z386,z4,z7]),(0,[z0,z1,z2,z3,z387,z4,z7]),(0,[z0,z1,z177,z2,z3,z154,z7])],[(0,[z0,z1,z2,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z92]),(0,[z0,z40,z1,z2,z46,z4,z7]),(0,[z0,z221,z2,z3,z98,z4,z7]),(0,[z0,z1,z2,z3,z4,z74,z23]),(0,[z0,z1,z2,z3,z388,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z389,z7]),(0,[z0,z1,z2,z3,z390,z4,z7]),(0,[z0,z1,z2,z3,z4,z135,z7]),(0,[z0,z221,z1,z2,z13,z3,z4]),(0,[z391,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z392,z2,z3,z4,z7]),(0,[z0,z1,z188,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z393])],[(0,[z223,z0,z1,z2,z3,z4,z206]),(0,[z0,z1,z62,z168,z3,z4,z7]),(0,[z31,z0,z40,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z394]),(0,[z0,z1,z2,z3,z395,z4,z7]),(0,[z0,z1,z2,z3,z4,z396,z7]),(1,[z0,z1,z2,z3,z4,z29])],[(0,[z195,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z62,z2,z3,z4,z29]),(0,[z0,z1,z72,z2,z3,z4,z114]),(0,[z56,z0,z330,z2,z3,z4,z7]),(0,[z0,z1,z2,z397,z3,z4,z7])],[(0,[z0,z1,z2,z398,z3,z4,z7])],[(0,[z31,z89,z0,z1,z2,z3,z4]),(0,[z202,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z93,z86]),(0,[z0,z1,z62,z2,z3,z4,z7]),(0,[z31,z0,z1,z2,z3,z4,z86]),(0,[z67,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z399,z23])],[(1,[z0,z1,z2,z3,z400,z7]),(0,[z19,z0,z1,z2,z401,z4,z7]),(0,[z0,z1,z2,z49,z3,z144,z7]),(0,[z68,z1,z2,z3,z4,z7,z69])],[(0,[z0,z1,z2,z3,z4,z402,z7]),(0,[z0,z1,z2,z3,z4,z403,z7]),(1,[z0,z65,z1,z3,z73,z7])]],
   [[(0,[z31,z0,z1,z2,z3,z144,z4]),(0,[z0,z1,z2,z3,z314,z46,z7]),(0,[z0,z1,z2,z3,z4,z404,z7]),(0,[z143,z31,z0,z1,z2,z3,z4])],[(0,[z405,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z90,z2,z3,z4,z29]),(0,[z31,z125,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z406,z3,z4,z7]),(0,[z407,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z408,z3,z4,z7]),(0,[z0,z409,z1,z2,z3,z4,z7])],[(0,[z410,z0,z1,z2,z3,z4,z7]),(0,[z56,z0,z1,z2,z3,z144,z7]),(0,[z0,z1,z2,z3,z4,z411,z7]),(1,[z0,z1,z72,z230,z4,z7]),(0,[z0,z65,z1,z2,z3,z4,z27])],[(0,[z0,z1,z412,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z80,z7]),(0,[z56,z0,z147,z2,z3,z4,z7]),(0,[z0,z1,z2,z258,z3,z4,z76])],[(1,[z0,z1,z2,z401,z4,z7]),(0,[z202,z0,z1,z2,z13,z3,z4]),(0,[z31,z0,z1,z2,z22,z3,z4]),(1,[z47,z0,z1,z82,z4,z7])],[(0,[z0,z1,z2,z3,z413,z4,z7]),(0,[z414,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z49,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z7,z415])],[(0,[z1,z188,z2,z168,z3,z4,z7]),(0,[z0,z1,z2,z3,z106,z74,z7]),(0,[z0,z416,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z288]),(0,[z0,z34,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z417,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z418]),(0,[z0,z419,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z420,z1,z2,z3,z4,z7]),(0,[z68,z0,z1,z2,z3,z4,z93]),(0,[z0,z1,z2,z3,z4,z421,z7]),(0,[z0,z42,z1,z2,z3,z4,z7])],[(0,[z125,z0,z1,z188,z3,z4,z7]),(0,[z0,z422,z1,z2,z3,z4,z7]),(0,[z0,z423,z1,z2,z3,z4,z7]),(0,[z0,z40,z2,z22,z3,z4,z7]),(0,[z0,z42,z1,z2,z3,z154,z7]),(0,[z56,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z424,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z425])],[(0,[z0,z1,z2,z3,z417,z4,z7]),(1,[z0,z1,z2,z3,z4,z240]),(0,[z0,z426,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z81]),(0,[z0,z1,z72,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z427,z4,z7]),(0,[z0,z1,z2,z3,z428,z4,z7]),(0,[z31,z31,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z429,z3,z4,z7])],[(0,[z0,z1,z2,z3,z98,z4,z29]),(0,[z0,z1,z430,z2,z3,z4,z7]),(0,[z0,z1,z2,z431,z3,z4,z7])],[(0,[z432,z0,z1,z2,z3,z4,z7]),(0,[z433,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z434,z7]),(0,[z0,z1,z2,z161,z3,z4,z7])],[(0,[z19,z0,z1,z188,z3,z4,z7]),(0,[z0,z1,z72,z3,z4,z7,z29]),(0,[z0,z1,z2,z3,z4,z435,z7]),(0,[z0,z436,z1,z2,z3,z4,z7]),(0,[z31,z0,z285,z1,z2,z3,z4])],[(0,[z0,z1,z437,z2,z3,z4,z7]),(0,[z31,z0,z15,z1,z2,z3,z4]),(0,[z68,z0,z1,z2,z3,z54,z7]),(0,[z0,z1,z2,z3,z438,z4,z7]),(0,[z123,z0,z63,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z114]),(0,[z0,z439,z1,z2,z3,z4,z7]),(0,[z0,z440,z1,z2,z3,z4,z7])]],
   [[(0,[z45,z0,z1,z2,z46,z4,z7]),(0,[z0,z1,z2,z3,z4,z441,z7]),(0,[z0,z1,z177,z2,z3,z4,z99]),(0,[z56,z0,z1,z2,z13,z3,z4]),(1,[z31,z0,z1,z186,z3,z4])],[(0,[z442,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z72,z2,z13,z3,z4]),(0,[z0,z1,z2,z443,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z444,z7]),(0,[z0,z1,z2,z3,z4,z445,z7]),(0,[z0,z1,z446,z2,z3,z4,z7]),(0,[z0,z447,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z151,z4,z7])],[(0,[z0,z1,z2,z3,z448,z4,z7]),(0,[z0,z152,z1,z2,z3,z4,z7]),(0,[z449,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z98,z50,z7]),(0,[z0,z1,z450,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z128,z23]),(0,[z0,z1,z451,z2,z3,z4,z7]),(0,[z452,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z453,z3,z4,z7])],[(0,[z454,z0,z1,z2,z3,z4,z7]),(0,[z59,z1,z2,z3,z60,z4,z7]),(0,[z0,z1,z2,z16,z3,z4,z23]),(1,[z0,z1,z2,z3,z348,z7]),(1,[z0,z1,z2,z258,z3,z76])],[(0,[z0,z455,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z456,z4,z7]),(0,[z0,z1,z2,z457,z3,z82,z4])],[(0,[z0,z1,z2,z458,z3,z4,z7]),(0,[z0,z221,z1,z2,z3,z98,z7]),(0,[z0,z1,z2,z3,z4,z7,z459])]],
   [[(0,[z59,z0,z1,z2,z105,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z460]),(0,[z195,z149,z1,z2,z3,z4,z7]),(0,[z461,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z462,z3,z4,z7]),(0,[z463,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z48,z7]),(0,[z464,z0,z1,z2,z3,z4,z7]),(0,[z12,z0,z1,z2,z3,z4,z29])],[(0,[z0,z1,z168,z16,z3,z4,z7]),(0,[z0,z1,z2,z3,z465,z4,z7]),(0,[z0,z152,z61,z2,z3,z4,z7]),(0,[z466,z0,z1,z2,z3,z4,z7]),(0,[z467,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z468,z2,z3,z4,z7]),(0,[z31,z0,z1,z146,z2,z3,z4]),(0,[z0,z147,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z105,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z29,z69]),(0,[z47,z0,z1,z2,z3,z4,z23]),(0,[z12,z0,z1,z2,z3,z4,z7]),(0,[z160,z0,z1,z2,z3,z4,z23])],[(0,[z469,z0,z1,z2,z3,z4,z7]),(0,[z0,z152,z1,z2,z3,z4,z38]),(0,[z31,z0,z1,z2,z3,z4,z154]),(0,[z470,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z29,z29]),(0,[z0,z1,z2,z3,z4,z51,z29]),(0,[z0,z1,z2,z13,z3,z50,z4])],[(0,[z0,z1,z2,z3,z4,z471,z7]),(0,[z472,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z13,z3,z4]),(0,[z0,z1,z2,z3,z4,z473,z7]),(0,[z0,z1,z2,z3,z474,z4,z7]),(0,[z0,z1,z2,z3,z475,z4,z7]),(0,[z0,z63,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z476,z7]),(0,[z0,z1,z2,z3,z4,z298,z7]),(1,[z31,z0,z1,z2,z4,z109])],[(0,[z0,z477,z1,z2,z3,z4,z7]),(0,[z149,z0,z1,z2,z3,z144,z7]),(0,[z478,z0,z1,z2,z3,z4,z7]),(0,[z0,z221,z2,z3,z46,z4,z7]),(0,[z0,z40,z1,z2,z3,z4,z80]),(0,[z0,z1,z2,z479,z3,z4,z7]),(0,[z0,z65,z1,z2,z3,z4,z23])],[(0,[z36,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z156,z3,z4,z7]),(0,[z31,z0,z447,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z480,z4,z7]),(0,[z0,z1,z155,z2,z3,z82,z7]),(0,[z0,z1,z72,z2,z3,z4,z239]),(0,[z0,z65,z1,z3,z73,z4,z7]),(0,[z481,z31,z0,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z482,z2,z3,z4,z7]),(0,[z0,z483,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z23,z7])],[(0,[z1,z2,z105,z3,z60,z4,z7]),(1,[z0,z1,z484,z2,z3,z4]),(0,[z47,z0,z1,z2,z13,z3,z4]),(0,[z0,z1,z177,z2,z3,z4,z23]),(0,[z222,z0,z1,z2,z3,z4,z29]),(0,[z31,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z150,z13,z3,z4])],[(1,[z223,z90,z2,z3,z4,z7]),(0,[z485,z0,z1,z2,z3,z4,z7]),(0,[z31,z0,z221,z1,z2,z3,z4]),(0,[z486,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z29,z109])],[(1,[z89,z15,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z487,z7]),(0,[z0,z1,z2,z3,z4,z488,z7]),(0,[z489,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z22,z3,z4,z7]),(0,[z0,z221,z40,z2,z3,z4,z7]),(0,[z0,z2,z3,z98,z4,z154,z7]),(0,[z0,z1,z2,z3,z73,z4,z29]),(1,[z0,z1,z3,z4,z23,z29])],[(0,[z0,z1,z2,z401,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z339,z7]),(0,[z0,z62,z2,z16,z3,z4,z7]),(0,[z56,z0,z221,z1,z2,z3,z7]),(0,[z0,z65,z1,z2,z13,z3,z4]),(0,[z0,z1,z2,z490,z3,z4,z7])],[(0,[z491,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z492,z4,z7]),(0,[z31,z68,z0,z1,z2,z3,z4]),(0,[z493,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z82,z4,z29])],[(0,[z0,z1,z2,z224,z3,z4,z7]),(0,[z19,z1,z2,z168,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z69])],[(1,[z0,z1,z437,z3,z4,z7]),(0,[z123,z0,z1,z2,z3,z4,z64]),(0,[z0,z1,z2,z13,z3,z151,z4])]],
   [[(1,[z0,z1,z320,z3,z4,z7]),(0,[z59,z36,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z194,z4,z7]),(0,[z494,z0,z1,z2,z3,z4,z7]),(0,[z495,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z496,z4,z7]),(0,[z0,z1,z2,z3,z497,z4,z7]),(0,[z0,z1,z177,z2,z13,z3,z4]),(0,[z31,z0,z1,z2,z13,z3,z4])],[(0,[z0,z260,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z498,z3,z4,z7]),(0,[z202,z31,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z499,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z66]),(0,[z31,z0,z1,z2,z3,z4,z58])],[(0,[z31,z0,z1,z2,z168,z3,z4]),(0,[z149,z0,z1,z2,z3,z4,z92]),(0,[z1,z2,z3,z4,z93,z7,z69]),(0,[z0,z1,z2,z500,z3,z4,z7]),(0,[z0,z1,z2,z501,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z48])],[(0,[z0,z1,z502,z2,z3,z4,z7]),(0,[z0,z1,z503,z2,z3,z4,z7])],[(0,[z36,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z504,z7]),(0,[z0,z1,z2,z88,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z372])],[(0,[z0,z90,z2,z16,z3,z4,z7]),(0,[z0,z61,z15,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z505,z4,z7]),(0,[z0,z1,z2,z506,z3,z4,z7]),(0,[z0,z507,z1,z2,z3,z4,z7]),(0,[z31,z0,z1,z2,z3,z98,z4]),(0,[z0,z94,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z508,z3,z60,z4]),(0,[z0,z1,z2,z3,z509,z4,z7]),(0,[z0,z1,z2,z3,z4,z93,z76]),(0,[z31,z0,z1,z2,z3,z4,z74]),(0,[z0,z1,z2,z13,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z225,z23]),(0,[z0,z1,z2,z3,z4,z7,z109]),(0,[z0,z1,z2,z3,z4,z510,z7])],[(1,[z0,z1,z2,z3,z4,z511]),(0,[z0,z1,z2,z3,z4,z227,z23]),(0,[z0,z1,z2,z3,z4,z183,z23])]],
   [[(0,[z0,z1,z2,z3,z400,z4,z7]),(0,[z0,z1,z2,z512,z3,z4,z7]),(0,[z0,z1,z2,z230,z3,z4,z23]),(0,[z0,z1,z2,z13,z3,z4,z7])],[(1,[z195,z1,z2,z3,z144,z7]),(0,[z365,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z376]),(0,[z0,z40,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z513,z4,z7]),(0,[z234,z0,z1,z2,z3,z4,z23])],[(0,[z89,z0,z1,z2,z3,z4,z7]),(0,[z0,z61,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z46,z4,z29]),(0,[z0,z1,z2,z3,z4,z514,z7]),(0,[z0,z1,z2,z3,z4,z64,z29]),(0,[z47,z0,z1,z2,z230,z4,z7]),(0,[z31,z0,z1,z2,z3,z3,z4])],[(1,[z0,z1,z2,z3,z515,z7]),(0,[z45,z31,z0,z1,z2,z3,z4]),(0,[z123,z0,z1,z2,z3,z4,z7]),(1,[z516,z0,z1,z2,z3,z4])],[(0,[z223,z0,z15,z2,z3,z4,z7]),(0,[z125,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z517,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z64,z7]),(0,[z0,z1,z2,z3,z4,z7,z518])],[(1,[z0,z1,z2,z3,z4,z375]),(0,[z149,z1,z2,z3,z4,z106,z7]),(0,[z31,z0,z63,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z50,z4,z29]),(0,[z0,z1,z2,z3,z519,z4,z7]),(0,[z0,z1,z2,z13,z3,z120,z4])],[(0,[z0,z1,z2,z520,z3,z4,z7]),(0,[z0,z15,z1,z2,z3,z4,z23]),(0,[z19,z0,z1,z168,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z521]),(0,[z0,z1,z2,z13,z105,z3,z4]),(0,[z522,z0,z1,z2,z3,z4,z7])],[(0,[z0,z523,z1,z2,z3,z4,z7]),(0,[z0,z524,z1,z2,z3,z4,z7]),(0,[z19,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z183,z69]),(0,[z0,z1,z2,z525,z3,z4,z7]),(0,[z0,z1,z2,z526,z3,z4,z7]),(0,[z0,z527,z1,z2,z3,z4,z7]),(2,[z0,z1,z161,z3,z4])]],
   [[(0,[z0,z1,z2,z528,z3,z4,z7]),(0,[z0,z1,z2,z3,z529,z4,z7]),(0,[z0,z40,z1,z2,z13,z3,z4]),(1,[z0,z1,z2,z161,z3,z4])],[(0,[z223,z0,z1,z2,z3,z4,z29]),(0,[z530,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z508,z3,z4,z7]),(0,[z0,z1,z2,z3,z144,z4,z7]),(0,[z0,z1,z2,z3,z4,z106,z23]),(0,[z202,z1,z2,z3,z4,z93,z7]),(0,[z0,z1,z2,z13,z3,z46,z4]),(0,[z171,z0,z1,z2,z3,z4,z7]),(0,[z0,z531,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z258,z3,z4,z23])],[(0,[z0,z532,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z144,z154,z7]),(1,[z0,z1,z2,z3,z113,z7])],[(0,[z0,z1,z2,z3,z533,z4,z7]),(0,[z0,z534,z1,z2,z3,z4,z7]),(0,[z0,z42,z1,z2,z13,z3,z4]),(0,[z0,z1,z2,z535,z3,z4,z7]),(0,[z0,z1,z2,z3,z536,z4,z7]),(0,[z123,z0,z1,z2,z3,z4,z86]),(0,[z0,z1,z2,z244,z13,z3,z4])],[(0,[z0,z1,z2,z3,z60,z4,z23]),(0,[z0,z1,z2,z3,z537,z4,z7]),(0,[z0,z63,z2,z3,z4,z7,z86]),(0,[z0,z1,z2,z3,z4,z99,z7]),(0,[z0,z1,z2,z13,z3,z538,z4])],[(0,[z223,z0,z1,z2,z3,z400,z7]),(0,[z0,z15,z1,z2,z13,z3,z4]),(0,[z539,z0,z1,z2,z3,z4,z7]),(0,[z0,z221,z1,z2,z3,z4,z29]),(0,[z0,z1,z330,z2,z3,z4,z7])],[(0,[z0,z540,z1,z2,z3,z4,z7]),(0,[z0,z541,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z542,z4,z7]),(1,[z0,z1,z2,z457,z3,z4]),(0,[z0,z1,z2,z3,z543,z4,z7]),(0,[z31,z0,z1,z2,z3,z4,z51]),(0,[z0,z1,z2,z3,z4,z7,z544])],[(1,[z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z545,z3,z4,z7]),(0,[z0,z1,z2,z3,z106,z154,z7])]],
   [[(0,[z31,z0,z1,z188,z2,z3,z4]),(0,[z0,z546,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z216,z3,z4,z7]),(0,[z516,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z258,z13,z3,z4])],[(0,[z36,z0,z1,z2,z3,z4,z129]),(0,[z0,z1,z2,z3,z4,z58,z29]),(1,[z0,z1,z2,z49,z50,z7])],[(0,[z0,z1,z2,z3,z3,z4,z7]),(0,[z0,z1,z2,z105,z82,z4,z7]),(1,[z0,z1,z155,z2,z3,z7]),(0,[z0,z547,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z204,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z548])],[(0,[z549,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z550,z2,z3,z4,z7]),(0,[z0,z65,z1,z2,z3,z98,z7]),(0,[z0,z551,z1,z2,z3,z4,z7]),(0,[z0,z1,z177,z3,z4,z74,z7]),(0,[z0,z1,z2,z3,z4,z74,z29]),(0,[z12,z0,z1,z3,z4,z23,z7]),(0,[z0,z1,z2,z3,z4,z552,z7]),(1,[z0,z1,z186,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z553])],[(0,[z19,z0,z1,z2,z417,z4,z7]),(0,[z0,z1,z2,z3,z144,z74,z7]),(0,[z0,z1,z2,z554,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z206,z7]),(0,[z0,z555,z1,z2,z3,z4,z7]),(0,[z0,z65,z1,z2,z49,z3,z7]),(0,[z0,z1,z146,z2,z3,z4,z29]),(0,[z0,z556,z1,z2,z3,z4,z7])],[(0,[z0,z1,z90,z2,z3,z4,z7]),(1,[z125,z1,z188,z3,z4,z7]),(0,[z0,z557,z1,z2,z3,z4,z7]),(0,[z0,z1,z558,z2,z3,z4,z7]),(0,[z47,z31,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z559,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z560,z7])],[(1,[z0,z1,z2,z3,z4,z561]),(0,[z0,z1,z177,z2,z3,z98,z7]),(0,[z562,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z146,z2,z3,z4,z7])]],
   [[(0,[z195,z0,z1,z2,z3,z106,z7]),(0,[z202,z0,z1,z2,z3,z4,z69]),(0,[z0,z1,z2,z563,z3,z4,z7])],[(0,[z0,z1,z2,z3,z564,z4,z7]),(0,[z202,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z23,z93]),(0,[z47,z0,z1,z2,z3,z4,z81]),(0,[z0,z1,z177,z2,z49,z3,z7])],[(0,[z0,z0,z1,z2,z3,z4,z7]),(0,[z0,z565,z1,z2,z3,z4,z7]),(0,[z45,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z566,z4,z7]),(0,[z0,z1,z2,z3,z311,z4,z23])],[(0,[z567,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z568,z4,z7]),(1,[z0,z1,z2,z3,z4,z313]),(1,[z0,z1,z2,z3,z538,z4]),(0,[z0,z1,z2,z3,z151,z4,z76])],[(1,[z0,z1,z2,z3,z569,z7]),(0,[z0,z1,z2,z230,z60,z4,z7]),(0,[z0,z1,z2,z570,z3,z4,z7]),(0,[z0,z1,z571,z2,z3,z4,z7])],[(0,[z59,z0,z1,z2,z3,z4,z29])],[(0,[z0,z1,z2,z3,z4,z572,z7]),(0,[z68,z0,z1,z2,z3,z4,z23])],[(0,[z0,z573,z1,z2,z3,z4,z7]),(0,[z59,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z105,z46,z4,z7]),(1,[z68,z1,z2,z3,z4,z69]),(0,[z0,z1,z2,z3,z4,z574,z7]),(0,[z0,z1,z575,z2,z3,z4,z7]),(0,[z576,z0,z1,z2,z3,z4,z7]),(0,[z0,z577,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z183,z7,z76])]],
   [[(0,[z0,z1,z2,z3,z4,z578,z7]),(0,[z0,z1,z484,z2,z3,z4,z7]),(0,[z31,z0,z1,z2,z3,z82,z4]),(0,[z0,z1,z2,z3,z4,z7,z579]),(0,[z580,z0,z1,z2,z3,z4,z7])],[(0,[z581,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z582,z2,z3,z4,z7]),(0,[z45,z0,z1,z2,z3,z192,z7]),(0,[z45,z0,z1,z2,z13,z3,z4]),(0,[z0,z1,z2,z3,z98,z4,z7]),(0,[z0,z583,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z49,z3,z4,z29]),(0,[z584,z0,z1,z2,z3,z4,z7]),(0,[z31,z0,z1,z2,z3,z4,z183]),(0,[z0,z1,z2,z3,z4,z232,z7])],[(0,[z0,z1,z2,z3,z4,z7,z585])],[(0,[z0,z586,z1,z2,z3,z4,z7]),(0,[z195,z31,z0,z1,z2,z3,z4]),(1,[z0,z1,z2,z3,z4,z246])],[(0,[z587,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z588,z7]),(0,[z0,z1,z2,z3,z154,z51,z7])],[(0,[z589,z0,z1,z2,z3,z4,z7]),(1,[z0,z20,z2,z3,z4,z7]),(0,[z0,z1,z590,z2,z3,z4,z7]),(0,[z68,z0,z1,z2,z13,z3,z4]),(0,[z56,z0,z1,z2,z3,z4,z29]),(1,[z0,z1,z161,z3,z4,z7]),(0,[z0,z1,z2,z3,z151,z183,z7])],[(0,[z0,z1,z2,z3,z4,z203,z7]),(0,[z0,z1,z2,z3,z591,z4,z7]),(0,[z0,z1,z2,z3,z592,z4,z7]),(0,[z0,z1,z72,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z7,z66]),(0,[z0,z1,z593,z2,z3,z4,z7])],[(1,[z0,z34,z2,z3,z4,z7]),(0,[z0,z1,z594,z2,z3,z4,z7]),(0,[z0,z1,z2,z13,z3,z4,z106]),(0,[z0,z1,z2,z3,z4,z23,z64]),(0,[z0,z1,z2,z3,z113,z82,z7]),(0,[z0,z1,z2,z3,z595,z4,z7])]],
   [[(0,[z0,z1,z596,z2,z3,z4,z7]),(0,[z31,z0,z152,z1,z2,z3,z4]),(0,[z597,z0,z1,z2,z3,z4,z7]),(0,[z598,z0,z1,z2,z3,z4,z7]),(0,[z0,z354,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z49,z3,z50,z7])],[(0,[z599,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z600]),(0,[z0,z1,z484,z2,z3,z46,z4]),(1,[z0,z1,z2,z349,z3,z4]),(0,[z0,z1,z2,z3,z4,z23,z76])],[(0,[z0,z1,z2,z3,z601,z4,z7]),(0,[z0,z1,z2,z13,z3,z602,z4])],[(0,[z603,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z604])],[(0,[z0,z1,z2,z3,z4,z7,z511]),(0,[z0,z42,z1,z2,z49,z3,z7])],[(1,[z0,z1,z177,z3,z74,z7]),(0,[z414,z31,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z605,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z606,z7]),(0,[z0,z269,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z376]),(0,[z0,z1,z2,z3,z607,z4,z7]),(1,[z67,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z608,z3,z4,z7]),(0,[z0,z1,z609,z2,z3,z4,z7]),(0,[z0,z1,z2,z4,z58,z7,z109])],[(0,[z0,z1,z2,z3,z4,z7,z610]),(0,[z0,z1,z2,z3,z4,z611,z7]),(0,[z0,z1,z2,z3,z151,z106,z7]),(0,[z31,z0,z61,z1,z2,z3,z4]),(0,[z0,z612,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z613,z2,z3,z4,z7]),(0,[z614,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z51,z7]),(0,[z293,z0,z1,z2,z3,z4,z7])],[(0,[z615,z0,z1,z2,z3,z4,z7]),(0,[z0,z260,z1,z2,z3,z60,z4]),(0,[z0,z1,z2,z3,z4,z7,z616]),(0,[z0,z1,z2,z3,z144,z7,z76]),(0,[z0,z1,z2,z16,z3,z4,z29]),(0,[z0,z63,z1,z2,z3,z4,z7]),(0,[z47,z0,z1,z3,z82,z4,z7]),(0,[z0,z1,z2,z3,z4,z276,z7]),(1,[z0,z1,z2,z3,z4,z95]),(0,[z361,z0,z1,z2,z13,z3,z4])],[(0,[z0,z1,z2,z3,z4,z617,z7]),(0,[z0,z1,z2,z3,z618,z4,z7]),(0,[z0,z1,z2,z3,z4,z372,z7])],[(0,[z0,z1,z2,z168,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z619,z7]),(0,[z195,z0,z1,z2,z3,z144,z7]),(0,[z0,z1,z2,z3,z620,z4,z7]),(1,[z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z621,z7]),(0,[z31,z0,z1,z2,z3,z73,z4]),(1,[z0,z1,z2,z156,z3,z4])],[(0,[z0,z1,z622,z2,z3,z4,z7]),(0,[z623,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z62,z2,z3,z4,z135]),(0,[z0,z40,z2,z3,z4,z154,z7]),(0,[z0,z1,z2,z3,z50,z4,z309]),(0,[z31,z0,z1,z624,z2,z3,z4])],[(0,[z0,z1,z188,z16,z3,z4,z7]),(0,[z0,z625,z1,z2,z3,z4,z7]),(0,[z0,z1,z72,z230,z3,z4,z7])],[(0,[z222,z0,z1,z2,z3,z4,z7]),(0,[z223,z0,z1,z437,z3,z4,z7]),(0,[z0,z1,z2,z3,z106,z7,z76]),(1,[z0,z63,z2,z3,z4,z86]),(0,[z0,z1,z230,z3,z82,z4,z7]),(0,[z0,z1,z2,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z23,z385])],[(0,[z223,z0,z1,z320,z3,z4,z7]),(0,[z0,z1,z2,z13,z3,z4,z64]),(0,[z0,z1,z2,z3,z4,z163,z29])]],
   [[(0,[z0,z1,z188,z2,z3,z4,z23]),(0,[z0,z1,z2,z13,z3,z60,z4]),(0,[z0,z1,z2,z3,z73,z4,z7]),(0,[z626,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z627,z3,z4,z7])],[(0,[z223,z89,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z628,z4,z7]),(0,[z0,z1,z2,z629,z3,z4,z7]),(0,[z0,z1,z2,z3,z630,z4,z7]),(1,[z0,z1,z2,z3,z314,z7]),(0,[z0,z65,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z13,z3,z4,z76]),(0,[z0,z1,z2,z258,z3,z4,z183])],[(0,[z0,z1,z2,z168,z13,z3,z4]),(0,[z0,z1,z2,z60,z82,z4,z7]),(0,[z195,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z631,z7]),(0,[z0,z1,z2,z3,z82,z4,z7]),(0,[z0,z1,z2,z3,z4,z170,z29]),(0,[z0,z1,z2,z3,z4,z7,z29]),(0,[z0,z1,z2,z3,z4,z23,z393])],[(0,[z19,z125,z1,z2,z3,z4,z7]),(0,[z0,z61,z1,z2,z3,z515,z7]),(0,[z632,z0,z1,z2,z3,z4,z7]),(0,[z633,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z23,z86]),(0,[z0,z1,z2,z3,z634,z4,z7]),(0,[z449,z31,z0,z1,z2,z3,z4])],[(0,[z19,z0,z1,z2,z3,z4,z511]),(0,[z0,z1,z635,z2,z3,z4,z7]),(0,[z31,z0,z1,z2,z3,z4,z69]),(0,[z636,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z62,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z637,z7]),(0,[z67,z0,z1,z2,z3,z4,z23]),(1,[z0,z1,z2,z3,z4,z309]),(0,[z638,z0,z1,z2,z3,z4,z7])],[(0,[z639,z0,z1,z2,z3,z4,z7]),(0,[z47,z0,z1,z72,z3,z4,z7]),(1,[z0,z1,z3,z82,z4,z29]),(0,[z31,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z319,z4,z7]),(0,[z0,z1,z2,z3,z538,z4,z7])],[(1,[z19,z1,z168,z3,z4,z7]),(0,[z36,z0,z1,z2,z3,z266,z7]),(0,[z0,z1,z2,z3,z640,z4,z7]),(0,[z45,z0,z1,z2,z3,z348,z7])],[(0,[z0,z1,z2,z3,z641,z4,z7]),(0,[z0,z1,z188,z2,z13,z3,z4]),(1,[z0,z1,z2,z3,z54,z7]),(0,[z0,z1,z642,z2,z3,z4,z7]),(0,[z0,z1,z2,z150,z230,z3,z4]),(0,[z643,z0,z1,z2,z3,z4,z7])]],
   [[(0,[z254,z0,z1,z2,z3,z4,z7]),(0,[z149,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z644,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z645,z7]),(0,[z195,z0,z1,z2,z13,z3,z4]),(0,[z0,z1,z2,z3,z4,z515,z7])],[(0,[z149,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z646,z2,z3,z4,z7]),(0,[z0,z1,z62,z2,z13,z3,z4]),(0,[z0,z1,z2,z647,z3,z4,z7]),(0,[z470,z31,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z7,z561]),(0,[z0,z1,z2,z3,z4,z239,z7]),(0,[z0,z1,z2,z3,z648,z4,z7]),(0,[z0,z1,z624,z2,z3,z4,z7]),(0,[z31,z0,z1,z2,z3,z4,z109]),(0,[z0,z1,z2,z13,z4,z58,z7])],[(0,[z0,z1,z649,z2,z3,z4,z7])],[(0,[z0,z1,z2,z650,z3,z4,z7]),(0,[z45,z0,z2,z3,z46,z4,z7]),(0,[z31,z0,z1,z2,z230,z3,z4]),(0,[z0,z1,z2,z3,z651,z4,z7])],[(0,[z0,z1,z2,z652,z3,z4,z7]),(0,[z0,z1,z2,z60,z46,z4,z7]),(0,[z0,z61,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z46,z4,z7]),(0,[z0,z42,z1,z2,z3,z4,z23]),(0,[z653,z0,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z654,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z313]),(0,[z0,z1,z2,z457,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z375,z7]),(1,[z0,z1,z72,z3,z4,z29]),(0,[z0,z1,z2,z655,z3,z4,z7]),(0,[z0,z65,z1,z2,z3,z73,z7]),(0,[z0,z1,z2,z49,z3,z51,z7])],[(0,[z223,z1,z90,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z240]),(0,[z0,z1,z2,z3,z4,z656,z7]),(0,[z149,z0,z1,z2,z3,z4,z561]),(0,[z657,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z658,z4,z7]),(0,[z659,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z50,z4,z7])],[(0,[z0,z1,z2,z3,z4,z660,z7]),(0,[z0,z152,z1,z62,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z661,z7]),(0,[z0,z1,z662,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z50,z154,z7]),(0,[z0,z663,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z664,z7]),(0,[z0,z1,z2,z13,z3,z4,z86]),(0,[z0,z1,z2,z3,z4,z183,z29]),(0,[z0,z1,z2,z3,z665,z4,z7])],[(0,[z19,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z666,z7]),(0,[z45,z0,z40,z2,z3,z4,z7]),(1,[z0,z42,z2,z3,z154,z7]),(0,[z0,z1,z2,z3,z4,z154,z29]),(0,[z0,z1,z2,z230,z3,z4,z29]),(0,[z172,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z667,z7])],[(0,[z0,z1,z2,z3,z4,z4,z7]),(0,[z0,z668,z1,z2,z3,z4,z7]),(0,[z0,z40,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z669,z3,z4,z7]),(0,[z0,z1,z177,z2,z3,z73,z7]),(0,[z56,z0,z1,z2,z3,z51,z7]),(0,[z0,z1,z2,z3,z602,z4,z7])],[(0,[z223,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z670,z7]),(0,[z0,z1,z2,z3,z4,z154,z7]),(0,[z31,z0,z1,z177,z2,z3,z4]),(0,[z31,z0,z1,z2,z3,z595,z4])],[(0,[z0,z1,z2,z3,z4,z7,z671]),(0,[z0,z1,z2,z672,z3,z4,z7]),(0,[z0,z152,z1,z16,z3,z4,z7]),(1,[z0,z1,z2,z88,z3,z4]),(0,[z0,z1,z2,z3,z4,z673,z7]),(0,[z0,z1,z186,z2,z3,z4,z7])]],
   [[(0,[z31,z0,z1,z90,z2,z3,z4]),(0,[z0,z1,z674,z2,z3,z4,z7]),(0,[z0,z675,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z676,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z246]),(0,[z56,z0,z1,z177,z2,z3,z7])],[(0,[z0,z1,z2,z3,z247,z4,z29]),(0,[z0,z1,z2,z3,z151,z4,z23])],[(0,[z0,z15,z1,z2,z3,z4,z29]),(0,[z0,z152,z1,z2,z3,z4,z23]),(0,[z0,z221,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z29,z277])],[(0,[z677,z0,z1,z2,z3,z4,z7]),(0,[z0,z221,z1,z2,z3,z154,z7]),(0,[z678,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z29,z679]),(0,[z433,z0,z1,z2,z13,z3,z4])],[(0,[z680,z0,z1,z2,z3,z4,z7]),(0,[z0,z681,z1,z2,z3,z4,z7]),(0,[z481,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z106,z29]),(0,[z0,z1,z2,z682,z3,z4,z7]),(0,[z0,z1,z2,z683,z3,z4,z7]),(0,[z516,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z258,z3,z4,z29])],[(0,[z0,z1,z2,z3,z684,z4,z7]),(0,[z68,z0,z1,z2,z3,z339,z7]),(0,[z0,z1,z2,z3,z4,z685,z7]),(0,[z0,z1,z2,z3,z4,z58,z7])],[(0,[z0,z1,z2,z3,z686,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z60,z4,z29]),(0,[z0,z1,z687,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z74,z7]),(0,[z688,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z105,z3,z4,z23]),(0,[z0,z152,z1,z2,z13,z3,z4]),(0,[z12,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z451,z2,z13,z3,z4]),(0,[z0,z1,z2,z3,z4,z689,z7])],[(0,[z0,z1,z2,z3,z4,z569,z7]),(0,[z690,z0,z1,z2,z3,z4,z7]),(0,[z691,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z230,z105,z4,z7]),(0,[z0,z1,z2,z3,z4,z692,z7]),(1,[z0,z1,z2,z3,z4,z38])],[(0,[z223,z0,z1,z2,z3,z569,z7]),(0,[z0,z1,z2,z3,z693,z4,z7]),(0,[z123,z0,z2,z3,z4,z64,z7]),(0,[z123,z31,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z694,z4,z7]),(0,[z0,z1,z2,z3,z4,z695,z7])],[(0,[z696,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z508,z3,z4]),(0,[z0,z1,z697,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z698,z4,z7]),(0,[z0,z699,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z32,z7]),(0,[z0,z226,z1,z2,z3,z4,z7])],[(0,[z36,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z700,z3,z4,z7]),(0,[z0,z1,z2,z701,z3,z4,z7]),(0,[z12,z0,z1,z3,z82,z4,z7]),(0,[z0,z1,z702,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z703,z4,z7]),(0,[z202,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z704,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z399,z7]),(0,[z0,z1,z2,z3,z4,z7,z95]),(0,[z0,z1,z2,z462,z13,z3,z4])],[(1,[z0,z1,z2,z3,z266,z7]),(0,[z0,z1,z2,z705,z3,z4,z7]),(0,[z0,z1,z2,z3,z706,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z679]),(0,[z0,z1,z2,z3,z4,z23,z504]),(0,[z0,z1,z2,z3,z4,z23,z23])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z320,z224,z4,z7]),(0,[z31,z0,z1,z437,z3,z4]),(0,[z0,z1,z2,z3,z707,z7]),(0,[z0,z1,z2,z3,z4,z708]),(0,[z0,z1,z446,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z709])],[(0,[z0,z1,z2,z710,z4,z7]),(0,[z0,z1,z2,z3,z711,z7]),(0,[z0,z712,z1,z2,z3,z4])],[(1,[z0,z2,z713,z4,z7])],[(0,[z19,z31,z1,z168,z3,z4]),(0,[z0,z1,z2,z3,z714,z7]),(0,[z31,z0,z1,z2,z686,z4])],[(0,[z0,z1,z2,z3,z400,z23]),(0,[z0,z715,z2,z3,z4,z7]),(0,[z0,z1,z3,z82,z4,z29]),(0,[z0,z1,z155,z2,z13,z3]),(0,[z0,z1,z2,z49,z50,z23])],[(0,[z19,z1,z168,z3,z4,z7]),(0,[z149,z1,z2,z3,z106,z561]),(0,[z0,z1,z2,z3,z716,z7]),(0,[z0,z1,z155,z2,z3,z23]),(0,[z0,z717,z2,z3,z4,z7]),(0,[z0,z1,z2,z13,z4,z718])],[(0,[z719,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z720]),(0,[z12,z0,z1,z161,z3,z4]),(0,[z0,z1,z2,z3,z721,z7])],[(0,[z0,z1,z2,z3,z167,z29]),(0,[z0,z1,z2,z3,z192,z29]),(0,[z0,z1,z502,z3,z4,z23]),(0,[z47,z0,z1,z13,z82,z4]),(0,[z0,z1,z2,z457,z3,z113]),(0,[z31,z0,z722,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z723,z7]),(0,[z0,z1,z3,z640,z4,z29]),(0,[z0,z1,z2,z3,z4,z724]),(0,[z0,z1,z2,z3,z4,z725]),(0,[z0,z1,z72,z230,z4,z23]),(0,[z726,z0,z1,z2,z3,z4]),(0,[z0,z727,z2,z3,z4,z7]),(0,[z31,z0,z1,z2,z3,z728]),(0,[z0,z1,z2,z258,z3,z729])],[(0,[z0,z1,z2,z3,z4,z730]),(0,[z0,z731,z2,z3,z4,z7]),(0,[z125,z1,z188,z3,z4,z23]),(0,[z31,z0,z1,z2,z3,z194]),(0,[z0,z1,z2,z3,z732,z7]),(0,[z0,z1,z2,z3,z4,z733])],[(0,[z0,z1,z2,z3,z4,z734]),(0,[z0,z735,z1,z2,z3,z4]),(0,[z0,z152,z16,z3,z4,z313]),(0,[z0,z1,z2,z3,z736,z7]),(0,[z0,z1,z575,z3,z4,z29]),(0,[z0,z40,z2,z13,z22,z4]),(0,[z47,z0,z1,z82,z4,z23])],[(0,[z0,z1,z2,z3,z4,z737]),(0,[z0,z42,z2,z13,z3,z154])],[(0,[z0,z1,z2,z3,z4,z738]),(0,[z45,z0,z2,z13,z46,z4]),(0,[z739,z1,z2,z3,z4,z7]),(0,[z0,z1,z230,z740,z4,z7]),(0,[z516,z0,z1,z2,z4,z109]),(0,[z0,z1,z451,z3,z4,z29])],[(0,[z0,z1,z2,z417,z4,z23]),(0,[z0,z1,z2,z3,z4,z741]),(0,[z149,z0,z1,z161,z3,z4]),(0,[z202,z1,z2,z3,z4,z93]),(0,[z0,z1,z2,z88,z4,z58])],[(0,[z0,z1,z2,z3,z742,z7]),(0,[z31,z0,z1,z2,z4,z264]),(0,[z0,z1,z3,z4,z239,z29]),(0,[z31,z0,z1,z2,z3,z743])],[(0,[z0,z423,z2,z3,z4,z86]),(0,[z47,z0,z1,z216,z82,z4]),(0,[z0,z1,z177,z3,z74,z99]),(0,[z0,z1,z2,z3,z4,z718])]],
   [[(0,[z125,z1,z188,z13,z3,z4]),(0,[z31,z0,z1,z2,z387,z4]),(0,[z0,z1,z2,z744,z3,z4]),(0,[z0,z1,z72,z3,z4,z29]),(0,[z745,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z4,z58,z718])],[(0,[z0,z1,z2,z3,z400,z206]),(0,[z223,z90,z2,z3,z4,z288]),(0,[z0,z1,z2,z3,z746,z7]),(0,[z0,z1,z2,z3,z747,z7]),(0,[z0,z1,z2,z748,z417,z4]),(0,[z749,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z750]),(0,[z123,z0,z2,z3,z4,z326]),(0,[z0,z1,z52,z3,z4,z29])],[(0,[z751,z0,z1,z2,z224,z4]),(0,[z0,z1,z2,z752,z4,z7]),(1,[z0,z1,z740,z4,z7]),(0,[z0,z1,z457,z3,z4,z29])],[(0,[z0,z1,z2,z401,z4,z29]),(0,[z0,z1,z2,z3,z4,z753]),(0,[z0,z42,z2,z3,z154,z7]),(0,[z0,z1,z2,z754,z51,z7])],[(0,[z0,z1,z2,z417,z167,z7]),(0,[z0,z1,z2,z13,z3,z263]),(1,[z1,z755,z3,z4,z7]),(0,[z45,z0,z2,z713,z4,z7]),(0,[z31,z0,z1,z2,z251,z4])],[(0,[z0,z1,z2,z224,z4,z29]),(0,[z0,z1,z2,z3,z4,z756]),(0,[z0,z1,z161,z3,z4,z93]),(0,[z0,z1,z2,z3,z4,z757]),(0,[z0,z1,z2,z3,z758,z7]),(0,[z0,z1,z2,z3,z4,z759]),(0,[z0,z1,z3,z4,z29,z548])],[(0,[z0,z1,z437,z3,z4,z288]),(0,[z0,z1,z2,z3,z4,z760]),(0,[z31,z0,z34,z2,z3,z4]),(0,[z0,z1,z2,z3,z263,z511]),(0,[z0,z1,z2,z88,z3,z4])],[(0,[z0,z1,z320,z3,z4,z288]),(0,[z0,z1,z2,z3,z761,z7]),(0,[z0,z1,z2,z417,z4,z203]),(0,[z0,z1,z3,z4,z762,z7]),(0,[z0,z2,z3,z301,z154,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z763]),(0,[z0,z1,z2,z3,z4,z764]),(0,[z0,z1,z3,z4,z670,z29]),(0,[z0,z1,z2,z3,z4,z765]),(0,[z0,z1,z2,z3,z766,z23]),(0,[z0,z1,z2,z3,z595,z183])],[(0,[z0,z1,z767,z3,z4,z7]),(0,[z0,z1,z2,z224,z400,z7]),(0,[z0,z1,z2,z3,z4,z768]),(0,[z0,z1,z613,z3,z4,z23])],[(0,[z0,z1,z2,z3,z769,z7]),(0,[z0,z1,z2,z3,z4,z770]),(0,[z0,z1,z2,z3,z4,z771]),(0,[z382,z1,z2,z60,z4,z7]),(0,[z772,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z773,z4,z7]),(0,[z0,z1,z676,z3,z4,z29]),(0,[z0,z1,z2,z774,z3,z4]),(0,[z0,z330,z2,z3,z51,z7]),(0,[z775,z1,z2,z3,z4,z7])],[(0,[z19,z20,z168,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z776]),(0,[z0,z1,z2,z3,z4,z777]),(0,[z0,z1,z2,z3,z4,z778])],[(0,[z286,z1,z2,z105,z4,z7]),(0,[z0,z1,z2,z779,z4,z7]),(0,[z0,z1,z2,z3,z4,z780]),(0,[z0,z1,z161,z781,z3,z4])],[(0,[z0,z1,z782,z3,z4,z7]),(0,[z19,z34,z168,z3,z4,z7]),(0,[z31,z36,z1,z2,z105,z4]),(0,[z0,z1,z2,z3,z783,z7]),(0,[z784,z1,z2,z3,z4,z7]),(0,[z0,z1,z72,z230,z4,z239]),(0,[z0,z330,z177,z2,z3,z7]),(0,[z56,z0,z1,z2,z51,z7])],[(0,[z89,z0,z1,z161,z3,z4]),(0,[z0,z1,z2,z3,z785,z7]),(0,[z0,z1,z82,z4,z163,z29]),(0,[z449,z0,z1,z161,z3,z4])],[(0,[z0,z1,z2,z3,z786,z7]),(0,[z0,z1,z2,z3,z4,z787]),(0,[z0,z1,z2,z788,z3,z4]),(0,[z0,z1,z2,z3,z789,z4]),(0,[z0,z790,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z791]),(0,[z0,z1,z2,z3,z792,z29]),(0,[z0,z1,z2,z3,z4,z793])]],
   [[(0,[z0,z1,z794,z3,z4,z7]),(0,[z0,z1,z2,z3,z795,z7]),(0,[z0,z796,z2,z3,z4,z7]),(0,[z31,z0,z1,z2,z368,z4]),(0,[z0,z1,z2,z797,z4,z7]),(0,[z0,z1,z2,z3,z4,z798]),(0,[z67,z0,z1,z2,z88,z4]),(0,[z254,z0,z1,z161,z3,z4]),(0,[z0,z1,z161,z3,z4,z58])],[(0,[z0,z799,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z800,z7]),(0,[z653,z1,z2,z60,z4,z7]),(0,[z0,z1,z2,z3,z4,z801]),(0,[z0,z40,z2,z669,z4,z7]),(0,[z0,z63,z2,z3,z4,z504]),(0,[z0,z1,z2,z3,z4,z802])],[(0,[z0,z1,z437,z124,z4,z7]),(0,[z0,z1,z2,z3,z803,z7]),(0,[z125,z0,z1,z161,z3,z4]),(0,[z516,z36,z0,z1,z2,z4]),(0,[z370,z1,z2,z3,z144,z7]),(0,[z0,z1,z2,z13,z465,z4]),(0,[z0,z1,z2,z804,z4,z7]),(0,[z0,z805,z1,z2,z3,z4]),(0,[z56,z0,z1,z2,z754,z7]),(0,[z0,z1,z806,z3,z4,z7])],[(0,[z0,z1,z320,z124,z4,z7]),(0,[z0,z1,z2,z508,z3,z4]),(0,[z1,z2,z3,z4,z807,z69])],[(0,[z0,z1,z2,z808,z4,z7]),(0,[z89,z809,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z263,z29]),(0,[z0,z1,z2,z3,z348,z29]),(0,[z31,z0,z1,z2,z3,z348]),(0,[z0,z1,z2,z3,z810,z7]),(0,[z0,z2,z22,z713,z4,z7]),(0,[z811,z0,z1,z2,z4,z7]),(0,[z0,z1,z2,z13,z4,z621])],[(0,[z31,z0,z1,z2,z3,z569]),(0,[z0,z1,z2,z3,z4,z812]),(0,[z219,z1,z2,z3,z144,z7]),(1,[z1,z2,z3,z4,z807]),(0,[z0,z42,z330,z2,z3,z7]),(0,[z0,z813,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z814]),(0,[z31,z89,z15,z2,z3,z4]),(0,[z0,z1,z2,z3,z263,z7]),(0,[z0,z1,z2,z3,z266,z7]),(0,[z0,z815,z2,z3,z4,z7]),(0,[z31,z0,z1,z2,z618,z4]),(0,[z0,z354,z2,z3,z4,z227]),(0,[z0,z1,z161,z49,z3,z4])],[(0,[z0,z1,z2,z816,z4,z7])]],
   [[(0,[z0,z1,z2,z817,z4,z7]),(0,[z0,z1,z2,z818,z4,z7]),(0,[z0,z1,z2,z3,z4,z819]),(0,[z0,z1,z150,z3,z82,z4]),(0,[z0,z1,z3,z4,z399,z29]),(0,[z31,z0,z1,z155,z2,z3]),(0,[z0,z1,z2,z3,z247,z170]),(0,[z0,z1,z2,z13,z443,z4])],[(0,[z89,z15,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z194,z29]),(0,[z0,z1,z2,z820,z3,z4]),(0,[z0,z1,z705,z3,z4,z29]),(0,[z0,z1,z2,z13,z341,z4]),(0,[z516,z0,z1,z3,z82,z4]),(0,[z0,z1,z3,z4,z23,z709]),(0,[z0,z1,z161,z3,z3,z4])],[(0,[z0,z1,z2,z3,z821,z7]),(0,[z0,z1,z2,z377,z50,z7]),(0,[z0,z1,z155,z2,z216,z3])],[(0,[z822,z0,z1,z2,z3,z4])],[(0,[z223,z809,z2,z3,z4,z7]),(0,[z0,z422,z62,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z823]),(0,[z0,z1,z2,z3,z314,z23]),(0,[z31,z0,z40,z2,z22,z4]),(0,[z31,z0,z1,z2,z301,z4]),(0,[z0,z1,z2,z3,z4,z824]),(0,[z449,z0,z624,z2,z3,z4]),(0,[z0,z1,z161,z258,z3,z4])],[(0,[z0,z1,z437,z3,z4,z23]),(0,[z0,z1,z2,z825,z124,z4]),(0,[z539,z0,z2,z46,z4,z7]),(0,[z0,z1,z2,z3,z4,z826]),(0,[z0,z1,z827,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z828]),(0,[z0,z1,z2,z3,z151,z170]),(0,[z0,z1,z2,z13,z3,z829])],[(0,[z0,z1,z2,z3,z4,z288]),(0,[z31,z0,z1,z2,z3,z4]),(0,[z0,z1,z320,z3,z4,z23]),(0,[z0,z1,z590,z3,z4,z29])],[(0,[z0,z830,z1,z2,z3,z4]),(0,[z0,z285,z1,z161,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z400,z288]),(0,[z89,z15,z2,z13,z3,z4]),(0,[z0,z1,z2,z3,z4,z831]),(0,[z0,z1,z2,z3,z4,z832])],[(0,[z223,z90,z2,z3,z4,z29]),(0,[z0,z1,z2,z417,z263,z7]),(0,[z31,z0,z1,z2,z682,z4]),(0,[z293,z1,z2,z3,z4,z69]),(0,[z0,z1,z2,z3,z4,z833]),(0,[z0,z1,z2,z3,z4,z80]),(0,[z31,z0,z1,z2,z4,z434]),(0,[z0,z1,z2,z3,z4,z81])],[(0,[z0,z1,z2,z3,z4,z834]),(0,[z0,z835,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z836]),(0,[z0,z1,z2,z3,z54,z23]),(0,[z0,z837,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z838,z4]),(0,[z0,z65,z330,z2,z3,z7])],[(0,[z0,z1,z437,z13,z3,z4]),(0,[z0,z1,z2,z3,z266,z5]),(0,[z0,z1,z2,z839,z3,z4]),(0,[z0,z97,z1,z2,z3,z7]),(0,[z0,z1,z2,z840,z3,z4]),(0,[z0,z221,z2,z3,z98,z7]),(0,[z0,z1,z2,z88,z82,z4]),(0,[z0,z1,z72,z3,z4,z841]),(0,[z0,z1,z2,z3,z4,z99])],[(0,[z0,z1,z842,z3,z4,z7]),(0,[z223,z90,z2,z3,z400,z7]),(0,[z843,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z844]),(0,[z36,z1,z2,z105,z4,z7]),(0,[z0,z1,z2,z3,z845,z7]),(0,[z0,z1,z2,z3,z8,z29]),(0,[z0,z221,z2,z3,z846,z7]),(0,[z0,z1,z2,z3,z4,z847]),(0,[z0,z1,z2,z848,z3,z4]),(0,[z31,z0,z717,z2,z3,z4]),(0,[z0,z1,z2,z3,z151,z232])],[(0,[z0,z1,z2,z3,z4,z849]),(0,[z0,z1,z2,z3,z4,z114]),(0,[z0,z1,z155,z3,z82,z29])],[(0,[z0,z1,z2,z3,z4,z850]),(0,[z0,z1,z2,z3,z4,z851]),(0,[z0,z1,z2,z3,z339,z69]),(0,[z639,z1,z2,z3,z4,z93]),(0,[z0,z1,z2,z3,z4,z852]),(0,[z0,z1,z62,z161,z3,z4]),(0,[z0,z2,z713,z46,z4,z7]),(0,[z0,z330,z2,z3,z4,z7]),(0,[z12,z0,z1,z3,z4,z709]),(0,[z31,z0,z1,z2,z4,z385])]],
   [[(0,[z19,z1,z168,z3,z167,z7]),(0,[z0,z1,z2,z3,z339,z29]),(0,[z0,z1,z853,z3,z4,z7]),(0,[z0,z1,z72,z82,z4,z29]),(0,[z31,z0,z1,z177,z3,z74]),(0,[z854,z0,z1,z2,z3,z4])],[(0,[z855,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z515,z23]),(0,[z31,z0,z1,z2,z3,z314]),(1,[z0,z1,z3,z856,z7]),(0,[z0,z1,z2,z4,z7,z718])],[(0,[z0,z1,z2,z124,z4,z7]),(0,[z0,z1,z437,z3,z4,z206]),(0,[z0,z1,z2,z3,z4,z857]),(0,[z0,z1,z2,z858,z3,z4]),(0,[z0,z1,z161,z3,z144,z4]),(0,[z0,z1,z2,z13,z297,z4]),(0,[z0,z1,z2,z859,z3,z4]),(1,[z0,z2,z3,z4,z759]),(0,[z0,z860,z2,z3,z4,z7]),(0,[z0,z1,z2,z861,z3,z4]),(0,[z0,z1,z146,z161,z3,z4])],[(0,[z0,z1,z320,z3,z4,z206]),(0,[z0,z1,z2,z3,z569,z288]),(0,[z862,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z863,z4]),(0,[z0,z1,z2,z864,z3,z4])],[(0,[z0,z1,z2,z3,z4,z865]),(0,[z0,z1,z2,z3,z866,z7]),(0,[z0,z1,z2,z3,z167,z511]),(0,[z0,z2,z3,z4,z867,z7]),(0,[z0,z1,z134,z3,z74,z7]),(0,[z47,z0,z1,z3,z538,z4]),(0,[z0,z330,z2,z3,z50,z7])],[(0,[z0,z868,z2,z3,z4,z7]),(0,[z0,z65,z1,z3,z73,z66]),(0,[z28,z1,z2,z3,z4,z337]),(0,[z56,z0,z1,z2,z156,z51]),(0,[z433,z1,z2,z3,z602,z4])],[(0,[z0,z1,z2,z3,z4,z869]),(0,[z0,z1,z161,z22,z3,z4]),(0,[z870,z0,z1,z2,z4,z29]),(0,[z0,z871,z1,z2,z3,z4])],[(0,[z0,z1,z2,z872,z3,z4]),(0,[z0,z147,z2,z3,z4,z7]),(0,[z0,z1,z2,z873,z3,z7]),(0,[z0,z2,z3,z846,z4,z7]),(0,[z0,z447,z1,z161,z3,z4])]],
   [[(0,[z0,z1,z2,z13,z417,z4]),(0,[z0,z2,z3,z846,z154,z7]),(0,[z0,z1,z2,z3,z113,z23])],[(0,[z0,z1,z2,z3,z4,z874]),(0,[z31,z0,z20,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z875]),(0,[z0,z1,z876,z3,z4,z7]),(0,[z202,z0,z1,z161,z3,z4]),(0,[z0,z152,z16,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z877]),(0,[z56,z31,z0,z1,z2,z51])],[(0,[z0,z1,z437,z224,z4,z7]),(0,[z0,z1,z2,z825,z3,z4]),(0,[z0,z1,z2,z3,z4,z878]),(0,[z0,z1,z2,z13,z3,z348]),(0,[z0,z1,z2,z740,z4,z7]),(0,[z0,z1,z2,z3,z4,z879]),(0,[z0,z1,z2,z13,z4,z695])],[(0,[z0,z1,z2,z13,z3,z569]),(0,[z0,z1,z2,z880,z3,z4]),(0,[z0,z1,z2,z3,z4,z881]),(0,[z59,z516,z0,z1,z2,z4]),(0,[z36,z1,z2,z105,z4,z5]),(0,[z0,z1,z2,z3,z4,z882]),(0,[z1,z2,z3,z883,z4,z7]),(0,[z195,z1,z2,z13,z3,z144]),(0,[z0,z221,z1,z161,z3,z4]),(0,[z0,z1,z2,z3,z4,z884]),(0,[z31,z0,z1,z2,z3,z885]),(0,[z0,z1,z2,z13,z4,z58]),(0,[z0,z1,z2,z3,z151,z183])],[(0,[z0,z1,z320,z3,z4,z886]),(0,[z0,z1,z2,z3,z4,z887]),(0,[z0,z1,z3,z158,z4,z29])],[(0,[z0,z1,z2,z3,z4,z23]),(0,[z197,z1,z168,z3,z4,z7]),(0,[z47,z0,z1,z113,z82,z7]),(0,[z0,z1,z2,z888,z3,z29]),(0,[z160,z1,z2,z3,z4,z225]),(0,[z31,z0,z1,z161,z13,z4])],[(0,[z889,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z890,z7]),(0,[z0,z1,z2,z3,z144,z561]),(0,[z68,z0,z1,z161,z3,z4]),(0,[z0,z1,z2,z3,z4,z891]),(0,[z0,z1,z2,z892,z3,z4]),(0,[z0,z1,z3,z4,z23,z272]),(0,[z0,z440,z1,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z893])],[(0,[z0,z1,z2,z124,z569,z7]),(0,[z0,z1,z2,z3,z894,z7]),(0,[z0,z1,z2,z3,z895,z7]),(0,[z0,z40,z2,z22,z4,z29]),(0,[z0,z1,z161,z3,z82,z4])]],
   [[(0,[z0,z1,z2,z401,z4,z511]),(0,[z0,z1,z2,z3,z4,z896]),(0,[z31,z0,z1,z2,z13,z4]),(0,[z0,z1,z161,z3,z4,z183])],[(0,[z31,z0,z1,z2,z3,z400]),(0,[z0,z897,z2,z3,z4,z7]),(0,[z0,z1,z2,z898,z3,z4]),(0,[z0,z1,z2,z3,z266,z129]),(0,[z0,z152,z16,z3,z4,z38]),(0,[z0,z1,z2,z3,z899,z7]),(0,[z0,z1,z2,z900,z3,z4]),(0,[z0,z1,z186,z3,z4,z23])],[(0,[z68,z1,z2,z3,z339,z69]),(0,[z31,z0,z901,z2,z3,z4])],[(0,[z47,z0,z1,z155,z82,z7]),(0,[z0,z1,z2,z3,z902,z4])],[(0,[z0,z1,z2,z13,z3,z4]),(0,[z0,z1,z2,z3,z903,z7]),(0,[z267,z15,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z167,z7]),(0,[z195,z31,z1,z2,z3,z144]),(0,[z0,z1,z2,z3,z904,z7]),(0,[z0,z1,z2,z3,z192,z7]),(0,[z30,z1,z2,z3,z4,z298])],[(0,[z0,z1,z320,z3,z4,z905]),(0,[z0,z1,z2,z3,z4,z906]),(0,[z47,z0,z1,z457,z82,z4]),(0,[z31,z643,z0,z1,z2,z4]),(0,[z0,z1,z2,z907,z4,z29])],[(0,[z0,z1,z72,z161,z3,z4]),(0,[z0,z1,z3,z388,z4,z29])],[(0,[z0,z1,z2,z3,z4,z203]),(0,[z0,z1,z2,z908,z3,z4]),(0,[z0,z1,z2,z3,z4,z909]),(0,[z638,z1,z2,z3,z106,z7]),(0,[z160,z1,z2,z3,z4,z93]),(0,[z0,z1,z2,z907,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z400,z29]),(0,[z0,z1,z457,z161,z3,z4]),(0,[z31,z0,z1,z72,z230,z4]),(0,[z0,z1,z2,z3,z910,z7]),(0,[z0,z1,z2,z49,z50,z29]),(0,[z0,z1,z186,z13,z3,z4])],[(0,[z0,z1,z2,z3,z911,z7]),(0,[z0,z573,z1,z3,z4,z29]),(0,[z0,z1,z2,z13,z4,z112]),(0,[z0,z1,z155,z2,z3,z29]),(0,[z0,z65,z1,z3,z73,z29]),(0,[z0,z1,z2,z3,z4,z912]),(1,[z0,z1,z2,z3,z729])],[(0,[z0,z1,z2,z3,z4,z206]),(0,[z0,z1,z2,z913,z4,z7]),(0,[z0,z1,z2,z3,z569,z23]),(0,[z914,z0,z1,z2,z4,z7]),(0,[z0,z1,z2,z915,z3,z4]),(0,[z0,z1,z2,z3,z4,z916]),(0,[z0,z1,z2,z3,z4,z917]),(0,[z0,z1,z2,z3,z918,z29])],[(1,[z1,z2,z919,z4,z7]),(0,[z516,z0,z1,z2,z46,z4]),(0,[z0,z1,z2,z3,z920,z7]),(0,[z0,z1,z150,z3,z538,z4]),(0,[z0,z65,z1,z3,z73,z7]),(0,[z56,z0,z1,z2,z428,z7])],[(0,[z0,z1,z2,z880,z401,z4]),(0,[z0,z1,z2,z3,z921,z7]),(0,[z0,z1,z2,z216,z3,z4]),(0,[z0,z1,z72,z230,z4,z29]),(0,[z0,z1,z2,z922,z3,z29]),(0,[z0,z1,z2,z258,z3,z32]),(0,[z0,z1,z2,z13,z3,z923])],[(0,[z19,z1,z168,z3,z263,z7]),(0,[z1,z2,z755,z3,z4,z7]),(0,[z125,z1,z188,z3,z4,z29]),(0,[z0,z1,z2,z3,z885,z7]),(0,[z0,z1,z2,z3,z4,z924]),(0,[z0,z1,z161,z3,z4,z154]),(0,[z0,z1,z177,z3,z475,z7]),(0,[z0,z269,z2,z3,z4,z504])],[(0,[z0,z1,z925,z2,z3,z4]),(0,[z31,z0,z1,z2,z683,z4]),(0,[z0,z1,z2,z3,z390,z183]),(0,[z0,z1,z926,z3,z4,z7]),(0,[z47,z0,z1,z82,z4,z29])],[(0,[z0,z573,z16,z3,z4,z7]),(0,[z0,z927,z2,z3,z4,z7]),(0,[z1,z188,z755,z3,z4,z7]),(0,[z0,z928,z1,z2,z3,z4]),(0,[z0,z1,z2,z13,z3,z314]),(0,[z0,z1,z2,z3,z4,z929])]],
   [[(0,[z0,z1,z2,z401,z4,z7]),(0,[z36,z1,z2,z105,z4,z129]),(0,[z0,z930,z1,z2,z3,z7]),(0,[z31,z0,z1,z2,z4,z316]),(0,[z0,z1,z2,z204,z3,z120])],[(0,[z0,z1,z2,z3,z4,z931]),(0,[z0,z540,z16,z3,z4,z7]),(0,[z0,z1,z2,z417,z4,z29]),(0,[z0,z1,z2,z3,z932,z7]),(0,[z0,z1,z2,z3,z4,z933])],[(0,[z0,z1,z2,z224,z4,z7]),(0,[z0,z1,z2,z3,z4,z934]),(0,[z0,z1,z2,z935,z3,z4]),(0,[z0,z1,z2,z3,z4,z936]),(0,[z0,z1,z937,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z239]),(0,[z0,z1,z2,z150,z3,z4]),(0,[z0,z1,z161,z3,z73,z4]),(0,[z0,z1,z2,z3,z7,z729])],[(0,[z0,z1,z2,z3,z4,z938]),(0,[z0,z1,z2,z3,z4,z886]),(0,[z0,z20,z2,z3,z4,z23]),(0,[z59,z1,z2,z60,z4,z23]),(0,[z0,z1,z939,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z940]),(0,[z0,z1,z2,z3,z4,z941]),(0,[z0,z1,z161,z3,z4,z23]),(1,[z0,z1,z2,z4,z718]),(0,[z172,z0,z1,z2,z3,z232])],[(0,[z0,z61,z334,z3,z4,z7]),(0,[z942,z1,z2,z3,z4,z7]),(0,[z481,z0,z1,z2,z3,z32])],[(0,[z0,z1,z2,z3,z4,z943]),(0,[z0,z1,z3,z944,z4,z7]),(0,[z0,z1,z2,z3,z945,z7]),(0,[z0,z34,z2,z3,z4,z23]),(0,[z0,z1,z2,z13,z401,z4]),(0,[z0,z1,z946,z3,z4,z7])],[(0,[z223,z90,z437,z3,z4,z7]),(0,[z0,z40,z1,z161,z3,z4]),(0,[z0,z1,z186,z3,z4,z239]),(0,[z0,z65,z1,z3,z856,z7]),(0,[z481,z0,z1,z161,z3,z4])],[(0,[z223,z90,z320,z3,z4,z7]),(0,[z0,z1,z2,z3,z569,z206]),(0,[z0,z1,z947,z2,z3,z4]),(0,[z0,z1,z3,z4,z948,z7]),(0,[z0,z1,z2,z3,z949,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z950]),(0,[z0,z1,z2,z951,z3,z4]),(0,[z45,z0,z97,z2,z46,z7]),(0,[z0,z1,z2,z4,z7,z952])],[(0,[z0,z1,z2,z953,z4,z7]),(0,[z0,z1,z2,z3,z4,z954]),(0,[z0,z1,z2,z955,z4,z7]),(0,[z0,z1,z956,z3,z4,z7]),(0,[z0,z1,z957,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z958]),(1,[z809,z2,z3,z4,z7]),(0,[z0,z20,z2,z13,z3,z4]),(0,[z0,z20,z2,z3,z167,z7]),(0,[z0,z1,z2,z959,z4,z7]),(0,[z0,z260,z1,z2,z3,z4]),(0,[z0,z1,z2,z960,z3,z4]),(0,[z123,z0,z2,z3,z4,z64]),(0,[z0,z2,z3,z4,z759,z7]),(0,[z0,z1,z2,z3,z4,z961]),(0,[z0,z1,z2,z3,z4,z962]),(0,[z0,z1,z161,z13,z3,z4]),(0,[z31,z0,z1,z2,z374,z4])],[(0,[z0,z1,z2,z963,z3,z4]),(0,[z0,z1,z161,z3,z4,z69]),(0,[z0,z1,z72,z218,z4,z7]),(0,[z0,z1,z177,z3,z74,z23])],[(0,[z0,z1,z2,z3,z4,z905]),(0,[z0,z34,z2,z13,z3,z4]),(0,[z0,z34,z2,z3,z167,z7]),(0,[z0,z1,z2,z964,z4,z7]),(0,[z0,z1,z2,z3,z4,z965]),(0,[z0,z1,z161,z168,z3,z4]),(0,[z599,z0,z1,z2,z13,z4]),(0,[z1,z2,z3,z4,z93,z807]),(0,[z0,z1,z2,z3,z792,z7]),(0,[z0,z63,z624,z2,z3,z4]),(0,[z31,z0,z1,z186,z3,z4]),(0,[z41,z0,z1,z161,z3,z4])],[(0,[z0,z20,z2,z3,z4,z203]),(0,[z31,z0,z1,z2,z417,z4]),(0,[z0,z1,z755,z3,z4,z7]),(0,[z19,z0,z1,z161,z3,z4]),(0,[z0,z1,z2,z3,z4,z966]),(0,[z516,z0,z1,z2,z230,z4]),(0,[z0,z1,z2,z13,z4,z415])],[(0,[z59,z1,z2,z508,z60,z4]),(0,[z0,z967,z2,z3,z4,z7]),(0,[z0,z1,z72,z13,z230,z4])],[(0,[z0,z1,z2,z224,z569,z7]),(0,[z0,z1,z2,z13,z3,z400]),(0,[z0,z968,z1,z3,z4,z7]),(0,[z0,z34,z2,z3,z4,z203]),(0,[z149,z1,z2,z13,z3,z106]),(0,[z0,z1,z161,z3,z98,z4]),(0,[z31,z0,z1,z2,z3,z810])]],
   [[(0,[z0,z1,z2,z3,z4,z969]),(0,[z970,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z971]),(0,[z31,z0,z42,z2,z3,z154]),(0,[z0,z1,z161,z3,z4,z74]),(0,[z0,z1,z2,z3,z4,z972])],[(0,[z223,z0,z1,z161,z3,z4]),(0,[z0,z973,z1,z2,z3,z7]),(0,[z0,z2,z3,z974,z4,z7]),(0,[z0,z1,z2,z3,z348,z7]),(0,[z0,z221,z97,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z975]),(0,[z0,z1,z230,z3,z538,z4]),(0,[z0,z1,z2,z3,z856,z7]),(0,[z0,z1,z2,z13,z49,z50]),(0,[z0,z1,z976,z161,z3,z4]),(0,[z0,z1,z2,z258,z3,z76])],[(0,[z0,z1,z2,z3,z977,z7]),(0,[z0,z978,z1,z2,z3,z4]),(0,[z0,z1,z3,z4,z23,z402]),(0,[z123,z0,z2,z3,z4,z759])],[(0,[z0,z979,z2,z3,z4,z7]),(0,[z0,z1,z146,z3,z4,z709]),(0,[z0,z1,z278,z3,z4,z29]),(0,[z0,z980,z1,z161,z3,z4]),(0,[z0,z1,z2,z3,z4,z729])],[(0,[z149,z1,z2,z3,z106,z23]),(0,[z0,z981,z1,z2,z3,z4]),(0,[z0,z1,z2,z982,z3,z4]),(0,[z0,z1,z2,z3,z846,z7]),(0,[z47,z0,z1,z161,z3,z4]),(0,[z516,z0,z1,z2,z4,z277])],[(0,[z31,z0,z1,z2,z3,z167]),(0,[z0,z1,z2,z3,z4,z983]),(0,[z45,z0,z2,z349,z46,z4]),(0,[z0,z40,z2,z22,z4,z10]),(0,[z0,z1,z161,z230,z3,z4])],[(0,[z0,z20,z2,z401,z4,z7]),(0,[z0,z1,z2,z3,z194,z7]),(0,[z0,z1,z2,z3,z4,z984]),(0,[z45,z0,z2,z46,z4,z23]),(0,[z31,z0,z1,z161,z3,z4])],[(0,[z223,z31,z90,z2,z3,z4]),(0,[z0,z985,z1,z2,z3,z7]),(0,[z274,z1,z188,z3,z4,z7]),(0,[z0,z1,z2,z3,z986,z29])]],
   [[(0,[z0,z34,z2,z401,z4,z7]),(0,[z0,z1,z2,z3,z4,z987]),(0,[z0,z1,z155,z2,z457,z3]),(0,[z0,z1,z161,z150,z3,z4]),(0,[z0,z1,z161,z3,z988,z4]),(0,[z31,z0,z1,z2,z4,z109]),(0,[z293,z1,z2,z244,z3,z4])],[(0,[z0,z483,z1,z3,z4,z23])],[(0,[z0,z1,z2,z3,z4,z989]),(0,[z59,z1,z2,z919,z4,z7]),(0,[z28,z1,z2,z3,z4,z69]),(0,[z0,z1,z177,z278,z3,z7]),(0,[z0,z1,z2,z13,z566,z4]),(0,[z31,z990,z1,z2,z3,z4]),(0,[z0,z1,z161,z991,z3,z4])],[(0,[z0,z15,z1,z161,z3,z4]),(0,[z0,z1,z674,z3,z4,z29]),(0,[z0,z722,z2,z3,z4,z7]),(0,[z31,z0,z1,z992,z3,z4])],[(0,[z0,z1,z993,z3,z4,z7]),(0,[z19,z1,z168,z3,z4,z23]),(0,[z0,z97,z2,z3,z154,z7])],[(0,[z0,z15,z320,z3,z4,z7]),(0,[z89,z15,z2,z3,z4,z29]),(0,[z45,z0,z2,z46,z192,z7]),(0,[z0,z1,z161,z3,z595,z4])],[(0,[z223,z90,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z994]),(0,[z0,z995,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z996,z7])],[(0,[z997,z0,z1,z2,z3,z4]),(0,[z31,z0,z1,z2,z620,z4]),(0,[z31,z0,z998,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z999]),(0,[z0,z1,z2,z3,z1000,z7]),(0,[z45,z0,z484,z2,z46,z4]),(0,[z0,z1,z2,z3,z314,z29]),(0,[z0,z1,z2,z3,z4,z1001]),(0,[z0,z1,z2,z3,z732,z23]),(0,[z0,z1,z161,z3,z4,z51]),(0,[z0,z1,z2,z49,z754,z7])],[(0,[z0,z1,z437,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z1002]),(0,[z0,z152,z1,z161,z3,z4]),(0,[z0,z1,z2,z3,z1003,z4])],[(0,[z0,z1,z320,z3,z4,z29]),(0,[z1,z2,z3,z144,z883,z7]),(0,[z195,z0,z1,z161,z3,z4]),(0,[z0,z1,z2,z3,z8,z7]),(0,[z0,z1,z2,z258,z3,z393]),(0,[z56,z0,z1,z2,z13,z51]),(0,[z31,z784,z1,z2,z3,z4])],[(0,[z0,z1,z1004,z3,z4,z7]),(0,[z19,z1,z168,z13,z3,z4]),(0,[z43,z1,z2,z3,z144,z7]),(0,[z657,z0,z1,z3,z4,z23]),(0,[z0,z1,z2,z4,z1005,z29]),(0,[z0,z1,z2,z4,z29,z1006]),(0,[z0,z1,z2,z3,z754,z7])],[(0,[z0,z1,z2,z3,z194,z5]),(0,[z284,z1,z2,z3,z106,z7]),(0,[z0,z555,z2,z3,z154,z7]),(0,[z0,z1,z2,z3,z4,z1007]),(0,[z0,z1,z177,z3,z856,z7]),(0,[z12,z0,z1,z3,z4,z23]),(0,[z0,z1,z2,z3,z151,z729])],[(0,[z0,z1,z437,z3,z400,z7]),(0,[z0,z1008,z2,z3,z4,z7]),(0,[z36,z1,z2,z919,z4,z7]),(0,[z0,z1,z2,z3,z4,z1009]),(0,[z0,z1,z2,z3,z339,z7]),(0,[z0,z1,z2,z1010,z3,z4]),(0,[z0,z1,z2,z3,z4,z66]),(0,[z0,z1,z1011,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1012])],[(0,[z0,z1,z320,z3,z400,z7]),(0,[z0,z1,z1013,z3,z4,z7]),(0,[z0,z1,z2,z1014,z3,z4]),(0,[z19,z1,z168,z3,z4,z203]),(0,[z0,z1,z2,z3,z4,z1015]),(0,[z31,z0,z1,z2,z654,z4]),(0,[z0,z1,z2,z3,z54,z29]),(0,[z0,z1,z647,z3,z4,z23]),(0,[z0,z1,z2,z13,z3,z113]),(0,[z0,z1,z2,z13,z218,z4]),(0,[z31,z0,z1,z186,z13,z4]),(0,[z0,z727,z2,z13,z3,z4])],[(0,[z0,z20,z2,z3,z263,z7]),(0,[z0,z97,z1,z2,z349,z3]),(0,[z56,z516,z0,z1,z2,z4]),(0,[z0,z1,z1016,z161,z3,z4])]],
   [[(0,[z0,z1,z1017,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1018])],[(0,[z0,z34,z2,z3,z263,z7]),(0,[z0,z1,z503,z3,z4,z29])],[(0,[z31,z0,z1,z2,z401,z4]),(0,[z0,z1,z2,z3,z1019,z7]),(0,[z0,z1,z2,z3,z1020,z7]),(0,[z0,z1,z2,z3,z4,z1021]),(0,[z0,z42,z2,z3,z154,z23])],[(0,[z223,z90,z2,z3,z569,z7]),(0,[z0,z1022,z1,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1023]),(0,[z870,z0,z1,z2,z4,z7]),(0,[z0,z1,z2,z1024,z3,z4]),(0,[z195,z1,z2,z3,z144,z29]),(0,[z0,z1,z2,z3,z4,z1025]),(0,[z0,z1,z2,z398,z3,z76]),(0,[z0,z1026,z1,z2,z3,z4])],[(0,[z0,z1,z2,z1027,z4,z7]),(0,[z0,z1,z2,z3,z1028,z7]),(0,[z0,z330,z2,z3,z106,z7]),(0,[z0,z221,z2,z13,z3,z98]),(0,[z1029,z0,z1,z2,z4,z29])],[(0,[z0,z1,z2,z3,z1030,z7]),(0,[z36,z1,z2,z105,z266,z7]),(0,[z195,z1,z2,z3,z144,z7]),(0,[z0,z1,z2,z3,z4,z376]),(0,[z0,z1,z2,z3,z515,z29]),(0,[z0,z1,z3,z4,z29,z385]),(0,[z0,z1,z624,z161,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1031]),(0,[z0,z2,z3,z713,z4,z7]),(0,[z0,z97,z330,z2,z3,z7]),(0,[z0,z409,z2,z3,z154,z7]),(0,[z47,z0,z1,z82,z4,z48]),(0,[z47,z31,z0,z1,z82,z4]),(0,[z0,z1,z2,z216,z3,z113])],[(0,[z809,z90,z2,z3,z4,z7]),(0,[z19,z1,z168,z401,z4,z7]),(0,[z0,z1,z2,z13,z3,z8]),(0,[z516,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z4,z7,z1006])]],
   [[(0,[z31,z0,z1,z2,z224,z4]),(0,[z1,z809,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1032]),(0,[z68,z285,z1,z2,z3,z4]),(0,[z0,z1,z2,z1033,z3,z4]),(0,[z45,z0,z2,z314,z46,z7]),(0,[z0,z1,z2,z3,z4,z1034]),(0,[z0,z1,z2,z3,z7,z1035]),(0,[z0,z1,z2,z3,z4,z1036]),(0,[z0,z1,z2,z490,z3,z76])],[(0,[z843,z0,z1,z2,z401,z4]),(0,[z0,z1,z2,z1037,z3,z4]),(0,[z0,z1,z1038,z2,z3,z4])],[(0,[z1039,z0,z1,z2,z124,z4]),(0,[z1040,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z888,z3,z7]),(0,[z0,z1,z2,z1041,z3,z4]),(0,[z0,z65,z1,z3,z658,z7])],[(0,[z0,z1,z2,z13,z3,z167]),(0,[z0,z1,z2,z3,z883,z7]),(0,[z1042,z0,z1,z2,z3,z4]),(0,[z0,z65,z1,z13,z3,z73])],[(0,[z0,z1,z992,z3,z4,z7]),(0,[z273,z0,z2,z3,z4,z64]),(0,[z0,z1,z2,z3,z4,z1043]),(0,[z0,z40,z2,z22,z4,z7]),(0,[z0,z1,z1044,z2,z3,z4]),(0,[z0,z1,z2,z3,z113,z29]),(0,[z56,z0,z1,z2,z51,z23])],[(0,[z0,z1,z2,z3,z1045,z4]),(0,[z0,z1,z3,z740,z4,z7])],[(0,[z0,z1,z2,z1046,z3,z4]),(0,[z0,z1,z2,z417,z4,z511]),(0,[z0,z1,z2,z3,z4,z92]),(0,[z463,z1,z2,z3,z4,z69]),(0,[z0,z1,z136,z3,z4,z29]),(0,[z31,z0,z1,z2,z49,z50])],[(0,[z0,z1,z2,z3,z1047,z7]),(0,[z59,z1,z2,z13,z60,z4]),(0,[z1048,z0,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z1049]),(0,[z0,z1,z2,z3,z4,z1050]),(0,[z0,z1,z2,z3,z4,z1051]),(0,[z254,z242,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z1052,z4,z7]),(0,[z125,z1,z188,z3,z4,z375]),(0,[z0,z1,z2,z3,z4,z1053]),(0,[z1,z2,z3,z883,z106,z7]),(0,[z0,z1,z2,z3,z800,z23])],[(0,[z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z1054]),(0,[z0,z1,z2,z3,z194,z129]),(0,[z0,z1,z2,z3,z1055,z4]),(0,[z0,z1,z1056,z2,z3,z4]),(1,[z0,z2,z3,z846,z7]),(0,[z12,z0,z1,z3,z4,z239]),(0,[z0,z1,z2,z88,z4,z399]),(0,[z0,z1,z2,z4,z718,z109])],[(0,[z0,z1,z280,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z1057])],[],[(0,[z0,z1,z2,z3,z4,z1058]),(0,[z0,z1,z161,z3,z50,z4])],[(0,[z0,z1,z2,z3,z400,z7]),(0,[z0,z1,z1059,z3,z4,z7]),(0,[z0,z1,z2,z3,z266,z23]),(0,[z0,z1,z186,z3,z4,z29]),(0,[z0,z1,z2,z49,z50,z7])],[(0,[z0,z233,z1,z3,z4,z29]),(0,[z0,z1,z155,z2,z3,z7])],[(0,[z125,z1,z755,z3,z4,z7]),(0,[z0,z1,z2,z1060,z3,z4]),(0,[z0,z1,z2,z3,z4,z1061]),(0,[z0,z1062,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z918,z7]),(0,[z0,z1,z550,z3,z4,z29]),(0,[z123,z0,z2,z3,z319,z4]),(0,[z222,z0,z1,z161,z3,z4])]],
   [[(0,[z59,z31,z1,z2,z60,z4]),(0,[z0,z1,z2,z1063,z3,z4]),(0,[z0,z196,z2,z3,z98,z7]),(0,[z0,z1,z2,z13,z3,z339]),(0,[z1064,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1065,z4]),(0,[z0,z612,z2,z3,z154,z7]),(0,[z659,z0,z1,z2,z13,z4])],[(0,[z0,z1,z2,z872,z224,z4]),(0,[z68,z1,z2,z3,z4,z276]),(0,[z0,z1,z2,z3,z4,z1066]),(0,[z0,z63,z1,z161,z3,z4]),(0,[z0,z1,z649,z3,z4,z29]),(0,[z0,z1,z72,z230,z4,z7]),(0,[z0,z1,z2,z922,z3,z7])],[(0,[z125,z1,z188,z3,z4,z7]),(0,[z0,z1067,z2,z3,z4,z7]),(0,[z234,z1,z2,z3,z4,z276])],[(0,[z352,z31,z0,z1,z2,z4]),(0,[z0,z1,z2,z1068,z3,z4]),(0,[z0,z1,z406,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z1069]),(0,[z0,z1,z2,z3,z4,z561]),(0,[z328,z1,z2,z3,z106,z7]),(0,[z1070,z0,z1,z2,z3,z4]),(0,[z47,z0,z1,z82,z4,z7]),(0,[z0,z1,z2,z1071,z3,z4]),(0,[z0,z813,z2,z13,z3,z4])],[(0,[z1,z2,z3,z1072,z4,z7]),(0,[z31,z0,z1,z2,z88,z4]),(0,[z31,z745,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z1073,z7]),(0,[z0,z1,z2,z3,z1074,z7]),(0,[z31,z0,z65,z1,z3,z73]),(0,[z1075,z0,z1,z2,z3,z4]),(0,[z31,z0,z1,z2,z4,z604])],[(0,[z0,z1,z2,z3,z569,z29]),(0,[z0,z1,z2,z1076,z4,z7]),(0,[z0,z1,z2,z417,z4,z7]),(0,[z0,z1,z2,z3,z4,z1077]),(0,[z0,z1,z2,z3,z4,z1078]),(0,[z0,z1,z1079,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1080])],[(0,[z1081,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1082,z7]),(0,[z0,z1083,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z313]),(0,[z0,z1,z2,z3,z4,z1084]),(0,[z0,z1,z2,z3,z4,z1085]),(0,[z268,z0,z2,z46,z4,z7]),(1,[z0,z1,z161,z3,z4]),(0,[z0,z1,z2,z3,z538,z4]),(0,[z0,z1,z2,z83,z3,z679])]],
   [[(0,[z0,z1,z2,z1086,z4,z7]),(0,[z0,z1,z2,z1087,z3,z4]),(0,[z0,z1,z2,z3,z4,z1088]),(0,[z0,z420,z1,z3,z73,z7]),(0,[z0,z1,z740,z82,z4,z7]),(0,[z0,z1,z2,z3,z4,z1089]),(0,[z31,z0,z1,z956,z3,z4]),(0,[z414,z0,z447,z2,z3,z4])],[(0,[z0,z1,z90,z161,z3,z4]),(0,[z0,z1,z2,z3,z4,z240]),(0,[z0,z1,z2,z1090,z3,z4]),(0,[z0,z1,z2,z3,z1091,z7]),(0,[z0,z221,z2,z3,z340,z7]),(0,[z0,z1,z1092,z2,z3,z7]),(0,[z516,z0,z1,z2,z13,z4]),(0,[z143,z285,z1,z2,z3,z4]),(0,[z31,z0,z1,z1093,z3,z4]),(0,[z255,z0,z1,z2,z13,z4])],[(0,[z0,z1,z2,z3,z4,z1094]),(0,[z0,z1,z2,z3,z1095,z7]),(0,[z0,z1,z2,z3,z4,z1096]),(0,[z0,z1,z2,z3,z4,z1097]),(0,[z0,z97,z1,z2,z13,z3]),(0,[z31,z0,z1,z2,z535,z4]),(0,[z143,z0,z1,z161,z3,z4])],[(0,[z0,z586,z16,z3,z4,z7]),(0,[z0,z1098,z2,z3,z4,z7]),(0,[z68,z1,z2,z3,z4,z69]),(0,[z0,z97,z1,z2,z3,z23]),(0,[z0,z221,z2,z3,z98,z23]),(0,[z31,z0,z1,z2,z3,z113]),(0,[z0,z1,z2,z13,z4,z163]),(0,[z0,z1,z2,z3,z4,z1099])],[(0,[z0,z1,z188,z161,z3,z4]),(0,[z516,z0,z1,z2,z22,z4]),(0,[z0,z1,z3,z82,z4,z81]),(0,[z414,z0,z1,z161,z3,z4])],[(0,[z59,z260,z1,z2,z60,z4]),(0,[z516,z0,z1,z2,z82,z4])],[(0,[z0,z1,z2,z13,z224,z4]),(0,[z0,z20,z168,z3,z4,z7]),(0,[z0,z1,z2,z3,z339,z93]),(0,[z0,z1,z3,z4,z23,z404]),(0,[z0,z330,z2,z3,z4,z23]),(0,[z31,z0,z1,z186,z4,z109])],[(0,[z0,z1,z2,z3,z4,z1100]),(0,[z0,z20,z2,z3,z4,z29]),(0,[z59,z1,z2,z60,z4,z29]),(0,[z0,z1101,z16,z3,z4,z7]),(0,[z0,z1,z2,z3,z829,z7]),(0,[z0,z1,z2,z3,z4,z1102]),(0,[z0,z1,z161,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z246]),(0,[z0,z65,z1,z3,z73,z27]),(0,[z0,z1,z2,z3,z729,z76])]],
   [[(0,[z0,z1,z1103,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1104]),(0,[z125,z1,z188,z3,z4,z240]),(0,[z149,z1,z2,z3,z883,z7]),(0,[z0,z42,z2,z3,z846,z7]),(0,[z1105,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1106]),(0,[z0,z1,z2,z124,z4,z23]),(0,[z0,z34,z2,z3,z4,z29]),(0,[z0,z152,z1101,z3,z4,z7]),(0,[z0,z1,z2,z3,z766,z7]),(0,[z0,z1,z2,z3,z4,z1107]),(0,[z0,z1,z2,z3,z1108,z7]),(0,[z0,z1,z2,z13,z3,z721])],[(0,[z0,z1,z1109,z3,z4,z7]),(0,[z0,z1,z2,z3,z1110,z4]),(0,[z0,z1,z1101,z3,z4,z7]),(0,[z0,z1,z3,z4,z441,z29])],[(0,[z1111,z0,z1,z2,z3,z4]),(0,[z0,z2,z3,z4,z1112,z7]),(0,[z0,z1,z2,z1113,z4,z7]),(0,[z0,z1,z2,z3,z1114,z7]),(0,[z0,z1,z1115,z2,z3,z4]),(0,[z0,z1,z2,z3,z1116,z29])],[(0,[z1,z2,z3,z4,z807,z7]),(0,[z31,z0,z1,z2,z3,z8]),(0,[z1117,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1118])],[(0,[z0,z1,z2,z3,z1119,z7]),(0,[z580,z1,z2,z3,z4,z93]),(0,[z0,z1,z2,z349,z3,z4]),(0,[z0,z1,z2,z3,z4,z1120]),(0,[z0,z2,z3,z4,z759,z86]),(0,[z0,z330,z2,z13,z3,z4]),(0,[z0,z998,z2,z3,z4,z7])],[(0,[z997,z0,z1,z2,z417,z4]),(0,[z0,z1,z2,z3,z4,z1121]),(0,[z0,z1,z2,z1122,z3,z4]),(0,[z0,z1,z3,z4,z709,z29]),(0,[z0,z1,z2,z3,z29,z1123]),(0,[z0,z147,z2,z3,z4,z23]),(0,[z0,z1,z161,z3,z4,z109]),(0,[z0,z1,z2,z3,z183,z729])],[(0,[z0,z1,z161,z105,z3,z4]),(0,[z0,z1,z177,z3,z74,z29]),(0,[z365,z0,z2,z3,z4,z326]),(0,[z31,z0,z1,z926,z3,z4]),(0,[z361,z0,z2,z3,z319,z4])]],
   [[(0,[z0,z152,z16,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z1124]),(0,[z0,z2,z3,z4,z64,z759]),(0,[z0,z1,z72,z3,z4,z81]),(0,[z0,z1,z3,z4,z709,z7]),(0,[z31,z0,z1,z161,z4,z109])],[(0,[z242,z1,z2,z3,z4,z93]),(0,[z45,z0,z1,z161,z3,z4]),(0,[z516,z0,z1,z82,z4,z29]),(0,[z0,z1,z2,z3,z4,z1125]),(0,[z0,z1,z2,z150,z4,z163]),(0,[z31,z775,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1126]),(0,[z0,z1,z2,z224,z4,z288]),(0,[z197,z90,z2,z3,z4,z7]),(0,[z31,z0,z1,z2,z3,z192]),(0,[z0,z1,z161,z3,z46,z4]),(0,[z0,z221,z330,z2,z3,z7]),(0,[z67,z0,z1,z2,z3,z4]),(0,[z56,z0,z330,z2,z51,z7])],[(0,[z0,z1,z2,z3,z4,z1127]),(0,[z0,z1,z2,z3,z1128,z29]),(0,[z0,z1,z2,z3,z711,z23]),(0,[z0,z1,z2,z50,z754,z7])],[(0,[z0,z20,z2,z417,z4,z7]),(0,[z303,z1,z2,z3,z106,z7]),(0,[z0,z1,z2,z3,z986,z7])],[(0,[z0,z1,z2,z3,z4,z1129]),(0,[z149,z1,z2,z3,z106,z92]),(0,[z56,z0,z1,z2,z389,z7]),(0,[z0,z1,z2,z49,z323,z7]),(0,[z0,z1,z2,z3,z4,z841]),(0,[z0,z1,z2,z83,z3,z76]),(0,[z0,z147,z2,z13,z3,z4]),(0,[z0,z1,z2,z3,z4,z95])],[(0,[z0,z1,z2,z124,z4,z206]),(0,[z0,z1,z2,z1130,z4,z7]),(0,[z15,z809,z2,z3,z4,z7]),(0,[z0,z34,z2,z417,z4,z7]),(0,[z0,z1,z2,z3,z4,z1131]),(0,[z0,z1,z2,z3,z728,z7]),(0,[z0,z133,z2,z3,z154,z7]),(0,[z0,z1,z2,z3,z1132,z4]),(0,[z0,z42,z1,z161,z3,z4]),(0,[z0,z1133,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z311,z183]),(0,[z0,z1,z2,z4,z754,z7])],[(0,[z0,z1,z2,z1134,z3,z4]),(0,[z1,z2,z105,z919,z4,z7]),(0,[z0,z1,z590,z230,z4,z7]),(0,[z0,z152,z16,z13,z3,z4]),(0,[z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z1135,z7]),(0,[z268,z0,z1,z2,z51,z7]),(0,[z0,z1,z72,z150,z230,z4]),(0,[z56,z0,z1,z161,z3,z4]),(0,[z0,z1,z2,z156,z3,z4]),(0,[z0,z1,z2,z49,z50,z95])]],
   [[(0,[z751,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1136]),(0,[z0,z1,z2,z3,z4,z1137]),(0,[z149,z1,z2,z3,z106,z29]),(0,[z0,z1,z484,z2,z3,z4]),(0,[z0,z1,z3,z4,z23,z333])],[(0,[z0,z1,z2,z3,z4,z807]),(0,[z0,z1,z2,z3,z4,z1138]),(0,[z31,z0,z1,z1139,z3,z4])],[(0,[z89,z15,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1140]),(0,[z45,z0,z2,z46,z4,z29]),(0,[z0,z1,z3,z4,z23,z29]),(0,[z1141,z0,z1,z161,z3,z4])],[(0,[z0,z1,z2,z1142,z4,z7]),(0,[z0,z1,z2,z1143,z3,z4]),(0,[z0,z1,z2,z3,z167,z23]),(0,[z0,z1,z2,z1144,z3,z4]),(0,[z0,z1,z2,z3,z1145,z7]),(0,[z0,z1,z2,z3,z192,z23]),(0,[z67,z0,z1,z2,z4,z385])],[(0,[z0,z1,z3,z4,z1146,z7]),(0,[z0,z1,z2,z3,z4,z1147]),(0,[z638,z1,z2,z3,z4,z69]),(0,[z0,z1,z2,z3,z4,z1148]),(0,[z0,z1,z1149,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1150]),(0,[z31,z0,z1,z2,z3,z339]),(0,[z0,z1,z2,z3,z314,z7]),(0,[z0,z1,z2,z1151,z3,z4])],[(0,[z0,z1,z437,z3,z4,z7]),(0,[z0,z1,z2,z1152,z4,z7]),(0,[z0,z1,z2,z3,z1153,z7]),(0,[z0,z1,z2,z3,z1154,z7]),(0,[z59,z0,z1,z161,z3,z4]),(0,[z0,z1155,z1,z2,z3,z4]),(0,[z0,z1,z2,z1156,z4,z7]),(0,[z0,z1,z2,z1157,z3,z4])],[(0,[z0,z1,z320,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1158]),(0,[z0,z354,z2,z3,z4,z64]),(0,[z0,z1,z191,z3,z4,z29]),(0,[z0,z1,z363,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z1159])]],
   [[(0,[z19,z1,z168,z3,z4,z29]),(0,[z0,z1,z2,z4,z1005,z7]),(0,[z0,z1,z2,z3,z4,z1160]),(0,[z0,z1,z2,z3,z4,z309]),(0,[z171,z0,z1,z3,z538,z4])],[(0,[z0,z20,z188,z3,z4,z7]),(0,[z0,z1,z60,z82,z4,z29]),(0,[z0,z1,z2,z13,z3,z54]),(0,[z31,z0,z152,z16,z3,z4]),(0,[z0,z40,z2,z713,z4,z7]),(0,[z31,z0,z1,z2,z351,z4]),(0,[z0,z1,z1161,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z48]),(0,[z0,z1,z2,z3,z4,z1162]),(0,[z0,z1,z72,z740,z4,z7]),(0,[z0,z1,z1163,z161,z3,z4])],[(0,[z0,z1,z1164,z3,z4,z7]),(0,[z0,z439,z2,z3,z98,z7]),(0,[z0,z1,z2,z3,z1165,z7]),(0,[z0,z65,z1,z3,z73,z23]),(0,[z0,z1,z2,z49,z50,z309])],[(0,[z0,z1,z2,z3,z54,z7]),(0,[z0,z1,z498,z3,z4,z29]),(0,[z0,z61,z1,z161,z3,z4]),(0,[z0,z1,z484,z2,z3,z314]),(0,[z31,z0,z330,z2,z3,z4]),(0,[z56,z0,z147,z2,z51,z7]),(0,[z0,z1,z2,z3,z4,z372])],[(0,[z0,z1,z500,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z1166]),(0,[z0,z65,z1,z161,z3,z4]),(0,[z0,z1,z3,z538,z4,z29]),(0,[z0,z1,z2,z13,z3,z996])],[(0,[z0,z1,z2,z3,z1167,z7]),(0,[z0,z1,z2,z1168,z4,z7]),(0,[z0,z1,z2,z3,z4,z1169]),(0,[z0,z1170,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z167,z203]),(0,[z0,z148,z2,z22,z4,z7]),(0,[z0,z2,z1101,z3,z4,z7]),(0,[z0,z1,z2,z1171,z3,z4]),(0,[z0,z1,z2,z1172,z4,z7]),(0,[z0,z1,z2,z230,z88,z4]),(0,[z0,z1,z177,z3,z74,z246])],[(0,[z0,z1,z2,z3,z4,z511]),(0,[z0,z1,z2,z3,z4,z1173])],[(0,[z0,z1,z437,z3,z4,z1174]),(0,[z0,z1,z2,z401,z4,z23]),(0,[z0,z1,z2,z3,z4,z1175]),(0,[z0,z1,z2,z554,z3,z76]),(0,[z202,z1,z2,z3,z4,z807]),(0,[z0,z1,z2,z3,z4,z1176]),(0,[z516,z0,z1,z161,z3,z4]),(0,[z0,z1,z2,z3,z311,z128]),(1,[z0,z1,z2,z754,z7]),(0,[z31,z0,z1,z946,z3,z4])]],
   [[(0,[z0,z1,z3,z509,z4,z29]),(0,[z0,z1,z2,z3,z4,z1177]),(0,[z0,z1,z2,z1178,z3,z4])],[(0,[z0,z1,z2,z224,z4,z23]),(0,[z0,z1,z2,z1179,z4,z7]),(0,[z36,z0,z1,z161,z3,z4]),(0,[z0,z1,z2,z3,z4,z1180]),(0,[z31,z0,z97,z1,z2,z3]),(0,[z12,z0,z1,z457,z3,z4]),(0,[z1029,z0,z1,z2,z4,z7]),(0,[z0,z1,z2,z49,z336,z7])],[(0,[z0,z1,z2,z3,z4,z1181]),(0,[z0,z305,z16,z3,z4,z7]),(0,[z0,z1,z2,z3,z515,z7])],[(0,[z0,z1,z437,z3,z569,z7]),(0,[z202,z1,z2,z3,z602,z4]),(0,[z0,z1,z2,z3,z7,z1182]),(0,[z0,z556,z2,z3,z98,z7]),(0,[z516,z0,z1,z72,z3,z4])],[(0,[z0,z1,z320,z3,z569,z7]),(0,[z0,z1,z2,z1183,z4,z7]),(0,[z0,z1,z2,z3,z4,z375]),(0,[z0,z1,z2,z1184,z4,z7]),(0,[z68,z1,z2,z3,z4,z807])],[(0,[z0,z1,z3,z1185,z4,z7]),(0,[z19,z1,z168,z417,z4,z7]),(0,[z0,z1186,z2,z3,z4,z7]),(0,[z0,z1,z2,z1187,z4,z7]),(0,[z0,z1,z2,z1188,z4,z7]),(0,[z36,z1,z2,z105,z194,z7]),(0,[z0,z1,z672,z3,z4,z23]),(0,[z1189,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1190]),(0,[z1191,z0,z1,z161,z3,z4]),(0,[z0,z1,z161,z3,z4,z32])],[(0,[z0,z1,z2,z401,z167,z7]),(0,[z576,z1,z2,z105,z4,z7]),(0,[z0,z1,z2,z3,z151,z6]),(0,[z0,z1,z2,z3,z1192,z7]),(0,[z0,z1,z2,z3,z4,z1193]),(0,[z0,z42,z2,z3,z154,z29]),(0,[z0,z1,z1194,z3,z4,z7])],[(0,[z0,z2,z3,z1195,z4,z7]),(0,[z0,z1,z1139,z3,z4,z7]),(0,[z0,z1,z2,z13,z3,z266]),(0,[z123,z0,z1,z161,z3,z4]),(0,[z0,z1,z2,z161,z3,z4])]],
   [[(0,[z279,z0,z1,z82,z4,z7]),(0,[z0,z1,z161,z3,z4,z106]),(0,[z0,z1,z2,z3,z4,z1196]),(0,[z0,z1,z2,z13,z3,z192]),(1,[z0,z1,z3,z4,z709]),(0,[z470,z0,z1,z161,z3,z4])],[(0,[z0,z1,z2,z401,z4,z203]),(0,[z0,z1,z2,z3,z1197,z7]),(0,[z0,z1,z2,z3,z113,z7])],[(0,[z0,z1,z1198,z3,z4,z7]),(0,[z195,z1,z2,z3,z883,z7]),(0,[z56,z0,z1,z2,z301,z7]),(0,[z0,z447,z2,z3,z4,z64])],[(0,[z0,z1,z2,z4,z1199,z7]),(0,[z0,z1,z1200,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z1201]),(0,[z68,z1,z2,z3,z54,z69]),(0,[z0,z1,z2,z1202,z3,z4]),(0,[z0,z1,z2,z3,z4,z1203]),(0,[z516,z0,z1,z2,z150,z4]),(0,[z0,z1,z3,z856,z4,z7]),(0,[z0,z1,z2,z3,z4,z1204]),(0,[z0,z1,z3,z4,z29,z553]),(0,[z0,z1,z186,z161,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1205]),(0,[z0,z1206,z1,z2,z3,z4]),(0,[z31,z0,z1,z2,z525,z4]),(0,[z67,z0,z1,z72,z230,z4]),(0,[z31,z0,z147,z2,z3,z4])],[(0,[z0,z1,z2,z124,z4,z288]),(0,[z0,z1,z2,z3,z4,z1207]),(0,[z0,z1,z2,z3,z1208,z7]),(0,[z45,z0,z2,z46,z348,z7]),(0,[z0,z1,z2,z457,z3,z4]),(0,[z31,z0,z1,z806,z3,z4]),(0,[z0,z1,z451,z150,z3,z4])],[(0,[z0,z1,z2,z3,z4,z7]),(0,[z31,z0,z1,z2,z124,z4]),(0,[z0,z1,z2,z224,z4,z206]),(0,[z0,z1,z1209,z3,z4,z7]),(0,[z31,z0,z1,z2,z4,z37]),(0,[z0,z1,z2,z3,z7,z1210]),(0,[z12,z0,z1,z3,z538,z4])],[(0,[z0,z1,z2,z3,z4,z1211]),(0,[z0,z1212,z2,z3,z4,z7]),(0,[z0,z1,z2,z1213,z3,z4]),(0,[z0,z1,z2,z3,z4,z1214]),(0,[z0,z1,z265,z3,z4,z23])]],
   [[(0,[z0,z1,z2,z3,z263,z23]),(0,[z0,z1215,z2,z3,z4,z7]),(0,[z202,z1,z2,z3,z4,z298]),(0,[z0,z1,z2,z3,z348,z23]),(0,[z0,z1,z2,z1216,z3,z4]),(0,[z56,z0,z1,z2,z51,z29]),(0,[z0,z1,z593,z3,z4,z23]),(0,[z0,z1,z2,z1217,z3,z4]),(0,[z0,z1,z2,z3,z4,z1218])],[(0,[z0,z1,z2,z1219,z3,z4]),(0,[z0,z1,z2,z3,z1220,z7]),(0,[z0,z1,z72,z150,z3,z4]),(0,[z0,z1,z2,z1221,z3,z4]),(0,[z0,z1,z2,z3,z4,z1222]),(0,[z0,z1,z2,z3,z4,z1223]),(0,[z0,z1,z2,z3,z4,z1224]),(0,[z31,z0,z1,z1079,z3,z4]),(0,[z41,z0,z1,z2,z3,z595])],[(0,[z223,z90,z2,z124,z4,z7]),(0,[z0,z1,z2,z748,z3,z4]),(0,[z19,z1,z755,z3,z4,z7]),(0,[z0,z1,z2,z3,z1225,z7]),(0,[z0,z1,z2,z3,z4,z1226]),(0,[z0,z1,z2,z13,z3,z515]),(0,[z31,z0,z1,z2,z456,z4]),(0,[z0,z1,z186,z3,z4,z7]),(0,[z0,z1,z3,z73,z856,z7]),(0,[z31,z0,z1,z2,z559,z4]),(0,[z0,z231,z2,z3,z4,z100])],[(0,[z0,z1227,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1228]),(0,[z0,z1,z2,z1229,z4,z7]),(0,[z0,z1,z2,z3,z4,z1230]),(0,[z0,z1,z2,z3,z4,z1231]),(0,[z0,z796,z2,z3,z4,z29])],[(0,[z0,z20,z2,z3,z4,z511]),(0,[z0,z1,z105,z82,z4,z29]),(0,[z0,z1,z3,z4,z841,z29]),(0,[z0,z1,z2,z3,z1232,z4])],[(0,[z0,z1,z2,z3,z194,z23]),(0,[z0,z1,z2,z3,z4,z1233]),(0,[z0,z1,z2,z713,z4,z7]),(0,[z0,z1,z2,z1234,z3,z4])],[(0,[z0,z34,z2,z3,z4,z511]),(0,[z0,z1,z2,z3,z743,z7]),(0,[z0,z1,z2,z3,z4,z38]),(0,[z0,z1,z2,z3,z4,z1235]),(0,[z0,z1,z2,z3,z4,z1236]),(0,[z0,z1,z3,z856,z74,z7])],[(0,[z0,z1,z2,z3,z4,z1174]),(0,[z0,z901,z2,z3,z4,z7]),(0,[z1,z2,z3,z919,z4,z7]),(0,[z0,z1,z2,z3,z1237,z7]),(0,[z0,z1,z2,z3,z4,z1238]),(0,[z47,z0,z1,z740,z4,z7])]],
   [[(0,[z31,z0,z1,z320,z3,z4]),(0,[z0,z1,z2,z3,z4,z1239]),(0,[z0,z1,z2,z3,z4,z1240]),(0,[z0,z1,z161,z3,z4,z64]),(1,[z516,z0,z1,z82,z4])],[(0,[z0,z1,z161,z3,z60,z4]),(0,[z0,z1,z2,z3,z266,z29]),(0,[z0,z1,z2,z3,z4,z1241]),(0,[z0,z1,z2,z1242,z3,z7]),(0,[z0,z2,z3,z98,z846,z7])],[(0,[z1039,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1243,z7]),(0,[z0,z1,z2,z3,z263,z203]),(0,[z0,z1244,z1,z2,z3,z4]),(0,[z0,z330,z2,z3,z144,z7]),(0,[z31,z0,z221,z2,z3,z98]),(0,[z0,z1,z177,z161,z3,z4]),(0,[z0,z1,z2,z816,z4,z29]),(0,[z0,z1,z317,z3,z4,z29]),(0,[z0,z1,z1093,z3,z4,z7]),(0,[z0,z1,z161,z3,z4,z76])],[(0,[z0,z1,z2,z3,z569,z7]),(0,[z0,z1,z2,z3,z4,z1245]),(0,[z0,z1,z2,z1246,z3,z4]),(0,[z0,z1,z3,z698,z4,z29]),(0,[z0,z1247,z2,z3,z4,z7]),(0,[z31,z0,z1,z937,z3,z4]),(0,[z0,z1,z161,z3,z151,z4])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z1248,z3,z4]),(0,[z0,z1,z2,z13,z3,z194]),(0,[z31,z0,z1,z2,z153,z4]),(0,[z0,z97,z1,z484,z2,z3]),(0,[z0,z1,z2,z3,z4,z1249])],[(0,[z223,z90,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z1250]),(0,[z0,z1,z2,z3,z1251,z4]),(0,[z0,z1,z2,z49,z175,z7]),(0,[z242,z0,z1,z161,z3,z4]),(0,[z0,z1,z161,z161,z3,z4])],[(0,[z0,z90,z320,z3,z4,z7]),(0,[z31,z0,z1,z2,z3,z54]),(0,[z0,z1,z2,z3,z4,z1252]),(0,[z0,z1,z2,z3,z4,z1253]),(0,[z0,z1,z2,z3,z4,z1254]),(0,[z31,z0,z1,z1255,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1256]),(0,[z1257,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z919,z4,z7]),(0,[z0,z1,z2,z3,z4,z1258]),(0,[z0,z1,z161,z16,z3,z4]),(0,[z0,z2,z3,z46,z192,z7]),(0,[z990,z1,z2,z3,z4,z7]),(0,[z0,z40,z2,z22,z4,z80]),(0,[z0,z1259,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z27]),(0,[z0,z1,z161,z3,z4,z399]),(0,[z31,z0,z1,z2,z4,z718])]],
   [[(0,[z0,z1,z2,z3,z4,z1260]),(0,[z0,z1,z2,z3,z106,z561]),(0,[z0,z231,z2,z3,z4,z86]),(0,[z67,z0,z1,z186,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1261]),(0,[z0,z1,z2,z3,z4,z1262]),(0,[z0,z1,z2,z3,z8,z23])],[(0,[z0,z1,z2,z1263,z3,z4]),(0,[z31,z125,z1,z188,z3,z4])],[(0,[z0,z1,z2,z3,z1264,z7]),(0,[z0,z1,z2,z401,z263,z7]),(0,[z0,z1265,z2,z3,z4,z7]),(0,[z0,z1266,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z120,z76])],[(0,[z0,z1,z2,z3,z4,z1267]),(0,[z223,z90,z2,z13,z3,z4]),(0,[z0,z20,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z1268,z7]),(0,[z59,z1,z2,z60,z4,z7]),(0,[z0,z1,z134,z3,z4,z29]),(0,[z0,z1,z2,z3,z339,z23]),(0,[z0,z1,z161,z3,z4,z7])],[(0,[z0,z40,z2,z3,z192,z7])],[(0,[z0,z34,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1269]),(0,[z1,z2,z919,z60,z4,z7]),(0,[z56,z0,z1,z2,z372,z51])],[(0,[z0,z1,z2,z3,z1270,z7]),(0,[z0,z1,z2,z3,z4,z1271]),(0,[z31,z0,z1,z2,z629,z4]),(0,[z0,z97,z1,z2,z3,z29]),(0,[z0,z221,z2,z3,z98,z29]),(0,[z0,z1,z2,z3,z4,z1272]),(0,[z0,z1,z161,z3,z4,z1273])]],
   [[(0,[z0,z1,z2,z1274,z4,z7]),(0,[z0,z1,z2,z3,z1116,z7]),(0,[z0,z1,z2,z3,z1275,z4]),(0,[z1276,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1277,z4])],[(0,[z0,z1,z2,z3,z4,z1278]),(0,[z0,z1,z2,z176,z3,z76]),(0,[z0,z221,z2,z3,z424,z7]),(0,[z0,z63,z2,z3,z4,z759]),(0,[z0,z1,z3,z113,z82,z29]),(0,[z0,z1,z2,z3,z1019,z23]),(0,[z31,z0,z1,z1194,z3,z4])],[(0,[z0,z1,z320,z13,z3,z4]),(0,[z223,z90,z2,z3,z4,z206]),(0,[z268,z31,z0,z1,z2,z4]),(0,[z67,z0,z1,z161,z3,z4]),(0,[z0,z330,z2,z3,z4,z29]),(0,[z516,z0,z1,z2,z50,z4])],[(0,[z0,z1,z1255,z3,z4,z7])],[(0,[z0,z1,z437,z3,z4,z738]),(0,[z0,z1,z2,z13,z124,z4]),(0,[z0,z1,z2,z3,z1279,z7]),(0,[z31,z0,z1,z2,z3,z266]),(0,[z195,z1,z2,z3,z144,z23]),(0,[z0,z1,z2,z3,z4,z1280]),(0,[z0,z1,z161,z3,z4,z86]),(0,[z0,z1,z430,z3,z4,z29]),(0,[z0,z1,z177,z3,z74,z7])],[(0,[z0,z1,z2,z124,z4,z29]),(0,[z19,z1,z168,z3,z4,z511]),(0,[z1,z755,z168,z3,z4,z7]),(0,[z0,z1,z2,z13,z501,z4]),(0,[z0,z1,z177,z13,z3,z74]),(0,[z0,z1,z2,z3,z4,z1281])],[(0,[z0,z809,z2,z3,z4,z7]),(0,[z31,z0,z1,z2,z3,z263]),(0,[z0,z1,z1282,z2,z3,z7]),(0,[z47,z0,z1,z82,z4,z81]),(0,[z516,z0,z1,z82,z4,z7]),(0,[z0,z1,z2,z3,z4,z1283])],[(0,[z0,z1,z2,z3,z4,z1284]),(0,[z0,z1285,z2,z3,z4,z7]),(1,[z1,z2,z3,z883,z7]),(0,[z0,z2,z3,z4,z867,z29])]],
   [[(0,[z0,z1,z2,z3,z1286,z7]),(0,[z0,z1,z2,z3,z1287,z7]),(0,[z0,z1288,z1,z2,z3,z4]),(0,[z1289,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z1128,z7]),(0,[z275,z0,z1,z3,z4,z23])],[(0,[z0,z1,z2,z124,z400,z7]),(0,[z0,z1,z2,z3,z4,z1290]),(0,[z0,z1,z2,z3,z4,z1291]),(0,[z0,z1,z2,z3,z4,z129]),(0,[z31,z149,z1,z2,z3,z106]),(0,[z0,z1,z2,z3,z4,z1292]),(0,[z0,z1,z72,z230,z4,z114]),(0,[z0,z1,z2,z3,z23,z1035])],[(0,[z223,z90,z2,z224,z4,z7]),(0,[z0,z1,z2,z3,z4,z135]),(0,[z45,z31,z0,z2,z46,z4]),(0,[z0,z1,z2,z3,z4,z1293]),(0,[z0,z147,z2,z3,z4,z29]),(0,[z0,z1294,z1,z161,z3,z4]),(0,[z0,z226,z2,z462,z3,z4])],[(0,[z0,z1,z165,z3,z4,z29]),(0,[z0,z1,z2,z349,z3,z314]),(0,[z0,z40,z2,z22,z4,z23]),(0,[z0,z1,z2,z3,z4,z1295]),(0,[z0,z65,z1,z3,z388,z7]),(0,[z0,z94,z1,z2,z3,z393])],[(0,[z122,z1,z2,z3,z144,z7]),(0,[z0,z152,z16,z3,z4,z29]),(0,[z0,z1,z1296,z2,z3,z4]),(0,[z0,z1,z146,z3,z4,z29]),(0,[z0,z1,z3,z618,z4,z29]),(0,[z31,z0,z1,z957,z3,z4])],[(0,[z149,z1,z2,z3,z106,z7]),(0,[z0,z1,z2,z3,z1297,z7]),(0,[z0,z63,z2,z3,z4,z86]),(0,[z0,z226,z2,z3,z4,z86]),(0,[z0,z1,z2,z3,z7,z1123])],[(0,[z0,z1,z2,z3,z923,z7]),(0,[z0,z1,z1298,z3,z4,z7])],[(0,[z0,z1,z1299,z3,z4,z7]),(0,[z0,z1,z2,z3,z1300,z7]),(0,[z0,z1301,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1302]),(0,[z31,z0,z1,z2,z3,z515]),(0,[z0,z61,z62,z3,z4,z29]),(0,[z45,z0,z2,z46,z4,z7]),(0,[z0,z1303,z1,z161,z3,z4])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 512) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 512).take 507) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1019).take 343) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1362)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [512, 507, 343] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 76).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 76).take 73).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 149).take 68).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 217).take 39).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [76, 73, 68, 39] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_40319

theorem PEqualNP.Outside.L_meta_40319 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4274580672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4274580672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40319.solve