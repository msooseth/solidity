/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0
#pragma once

#include <vector>
#include <tuple>
#include <map>
#include <string>
#include <functional>
#include <memory>
#include <limits>
#include <optional>
#include "heap.h"

namespace solidity::util
{

/**
 * A literal of a (potentially negated) boolean variable or an inactive constraint.
 */
struct Literal
{
	// TODO do we need to init them?
	bool positive;
	// Either points to a boolean variable or to a constraint.
	size_t variable;

	Literal operator~() const { return Literal{!positive, variable}; }
	bool operator==(Literal const& _other) const
	{
			return std::make_tuple(positive, variable) == std::make_tuple(_other.positive, _other.variable);
	}
	bool operator!=(Literal const& _other) const { return !(*this == _other); }
	bool operator<(Literal const& _other) const
	{
		return std::make_tuple(positive, variable) < std::make_tuple(_other.positive, _other.variable);
	}
};
using Clause = std::vector<Literal>;


struct Link
{
	size_t prev = std::numeric_limits<size_t>::max();
	size_t next = std::numeric_limits<size_t>::max();
};

struct Queue
{
	size_t first;
	size_t last;
	size_t unassigned;
	uint64_t bumped;

	Queue () :
		first (std::numeric_limits<size_t>::max()),
		last (std::numeric_limits<size_t>::max()),
		unassigned (std::numeric_limits<size_t>::max()),
		bumped (0)
	{}

	void enqueue (std::vector<Link>& links, const size_t var) {
		auto& l = links[var];
		l.prev = last;
		if (l.prev != std::numeric_limits<size_t>::max()) {
			// Not the first one in the list
			links[last].next = var;
		} else {
			first = var;
		}
		last = var;
		l.next = std::numeric_limits<size_t>::max();
	}

	void dequeue (std::vector<Link>& vmtf_links, const size_t var) {
		auto& l = vmtf_links[var];

		if (l.prev != std::numeric_limits<size_t>::max()) {
			// Not the first one in the list
			vmtf_links[l.prev].next = l.next;
		} else {
			first = l.next;
		}

		if (l.next != std::numeric_limits<size_t>::max()) {
			// No the last one in the list
			vmtf_links[l.next].prev = l.prev;
		} else {
			last = l.prev;
		}
	}
};

struct vmtf_analyze_bumped_smaller
{
	vmtf_analyze_bumped_smaller (const std::vector<uint64_t>& _btab):
		btab (_btab)
	{}

	bool operator () (const size_t& a, const size_t& b) const {
		return btab[a] < btab[b];
	}
	const std::vector<uint64_t>& btab;
};

class CDCL
{
public:
	using Model = std::map<size_t, bool>;
	CDCL(
		std::vector<std::string> _variables,
		std::vector<Clause> const& _clauses,
		std::function<std::optional<Clause>(size_t, std::map<size_t, bool> const&)> _theorySolver = {},
		std::function<void(size_t)> _backtrackNotify = {}
	);

	std::optional<Model> solve();

private:
	double luby(double y, int x);
	bool solveLoop(const uint32_t max_conflicts, CDCL::Model& model, int& solution);
	void setupWatches(Clause& _clause);
	std::optional<Clause> propagate();
	std::pair<Clause, size_t> analyze(Clause _conflictClause);
	size_t currentDecisionLevel() const { return m_decisionPoints.size(); }

	void addClause(Clause _clause);

	void enqueue(Literal const& _literal, Clause const* _reason);

	void cancelUntil(size_t _backtrackLevel);

	std::optional<size_t> nextDecisionVariable();

	bool isAssigned(Literal const& _literal) const;
	bool isAssignedTrue(Literal const& _literal) const;
	bool isAssignedFalse(Literal const& _literal) const;
	bool isUnknownOrAssignedTrue(Literal const& _literal) const;

	std::string toString(Literal const& _literal) const;
	std::string toString(Clause const& _clause) const;

	/// Callback that receives an assignment and uses the theory to either returns nullopt ("satisfiable")
	/// or a conflict clause, i.e. a clauses that is false in the theory with the given assignments.
	std::function<std::optional<Clause>(size_t, std::map<size_t, bool>)> m_theorySolver;
	std::function<void(size_t)> m_backtrackNotify;

	std::vector<std::string> m_variables;
	/// includes the learnt clauses
	std::vector<std::unique_ptr<Clause>> m_clauses;

	/// During the execution of the algorithm, the clauses are madified to ensure that:
	/// The first two literals are either true or unknown.
	/// Those two literals are called "watched literals".
	/// This map contains the reverse pointers from the literals.
	/// The idea is that these two literals suffice to know if a clause is unsatisfied
	/// (it might be satisfied without us knowing, but that is not bad).
	std::map<Literal, std::vector<Clause*>> m_watches;

	/// Current assignments.
	std::map<size_t, bool> m_assignments;
	std::map<size_t, bool> m_assignmentsCache; // Polarity caching. All propagated values end up here
	std::map<size_t, size_t> m_levelForVariable;
	/// TODO wolud be good to not have to copy the clauses
	std::map<Literal, Clause const*> m_reason;
	uint64_t m_sumConflicts = 0;

	// Var activity
	Queue vmtf_queue = Queue();
	uint64_t bumped = 0;
	std::vector<uint64_t> vmtf_btab; ///< Indexed by variable number. enqueue time stamps for queue
	std::vector<Link> vmtf_links; ///< Indexed by variable number. table of vmtf_links for decision queue.
	void vmtf_init_enqueue (const size_t var);
	void vmtf_update_queue_unassigned (const size_t var);
	size_t vmtf_pick_var();
	void vmtf_bump_queue (const size_t var);
	std::vector<size_t> vmtf_vars_to_bump;

	std::vector<Literal> m_assignmentTrail;
	uint64_t m_longest_trail = 0;
	/// Indices into assignmentTrail where decisions were taken.
	std::vector<size_t> m_decisionPoints;
	/// Index into assignmentTrail: All assignments starting there have not yet been propagated.
	size_t m_assignmentQueuePointer = 0;

	std::vector<size_t> m_assignemntTrailSizesWeCalledSolverFor;
};


}
