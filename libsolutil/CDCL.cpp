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

#include <libsolutil/CDCL.h>

#include <liblangutil/Exceptions.h>

// TODO remove before merge
#include <iostream>
#include <libsolutil/StringUtils.h>

using namespace std;
using namespace solidity;
using namespace solidity::util;


CDCL::CDCL(
	vector<string> _variables,
	vector<Clause> const& _clauses,
	std::function<std::optional<Clause>(size_t, std::map<size_t, bool> const&)> _theorySolver,
	std::function<void(size_t)> _backtrackNotify
):
	m_theorySolver(_theorySolver),
	m_backtrackNotify(_backtrackNotify),
	m_variables(move(_variables))
{
	for (Clause const& clause: _clauses)
		addClause(clause);

	// TODO some sanity checks like no empty clauses, no duplicate literals?
}

void CDCL::vmtf_init_enqueue (const size_t var)
{
	assert(var < vmtf_links.size());
	Link & l = vmtf_links[var];

	//Put at the end of the queue
	l.next = numeric_limits<size_t>::max();
	if (vmtf_queue.last != numeric_limits<size_t>::max()) {
		// Not empty queue
		assert(vmtf_links[vmtf_queue.last].next == numeric_limits<size_t>::max());
		vmtf_links[vmtf_queue.last].next = var;
	} else {
		// Empty queue
		assert(vmtf_queue.first == numeric_limits<size_t>::max());
		vmtf_queue.first = var;
	}
	l.prev = vmtf_queue.last;
	vmtf_queue.last = var;

	vmtf_btab[var] = ++bumped; // set timestamp of enqueue
	vmtf_update_queue_unassigned(vmtf_queue.last);
}

void CDCL::vmtf_bump_queue (const size_t var) {
	if (vmtf_links[var].next == numeric_limits<size_t>::max()) return;

	vmtf_queue.dequeue (vmtf_links, var);
	vmtf_queue.enqueue (vmtf_links, var);

	assert (bumped != numeric_limits<uint64_t>::max());
	vmtf_btab[var] = ++bumped;
	if (!m_assignments.count(var)) vmtf_update_queue_unassigned(var);
}

void CDCL::vmtf_update_queue_unassigned (const size_t var)
{
	assert(var != numeric_limits<size_t>::max());
	vmtf_queue.bumped = vmtf_btab[var];
	vmtf_queue.unassigned = var;
}

size_t CDCL::vmtf_pick_var()
{
	uint64_t searched = 0;
	size_t var = vmtf_queue.unassigned;

	while (var != numeric_limits<size_t>::max() && m_assignments.count(var))
	{
		var = vmtf_links[var].prev;
		searched++;
	}

	if (var == numeric_limits<size_t>::max()) return var;
	if (searched) vmtf_update_queue_unassigned(var);
	return var;
}

double CDCL::luby(double y, int x)
{
	int size = 1;
	int seq;
	for (seq = 0; size < x + 1; seq++) size = 2 * size + 1;

	while (size - 1 != x)
	{
		size = (size - 1) >> 1;
		seq--;
		x = x % size;
	}

	return std::pow(y, seq);
}

optional<CDCL::Model> CDCL::solve()
{
	CDCL::Model model;
	int solution;
	int loop = 1;
	bool solved = false;
	while(!solved) {
		solution = 3;
		uint32_t max_conflicts = (uint32_t)((double)luby(2, loop) * 40.0);
		solved = solveLoop(max_conflicts, model, solution);
		loop++;
	}
	cout << "c solved, conflicts: " << m_sumConflicts << endl;
	assert(solution != 3);
	if (solution) return model;
	else return nullopt;
}

bool CDCL::solveLoop(const uint32_t max_conflicts, CDCL::Model& model, int& solution)
{
	assert (max_conflicts > 0);
	uint32_t conflicts = 0;
	while (conflicts < max_conflicts)
	{
		optional<Clause> conflictClause = propagate();
		if (!conflictClause && m_theorySolver)
		{
			size_t lastTrailSizeCall = m_assignemntTrailSizesWeCalledSolverFor.empty() ? 0 : m_assignemntTrailSizesWeCalledSolverFor.back();

			std::map<size_t, bool> newAssignments;
			for (size_t i = lastTrailSizeCall; i < m_assignmentTrail.size(); ++i)
				newAssignments[m_assignmentTrail[i].variable] = m_assignmentTrail[i].positive;
			conflictClause = m_theorySolver(m_assignmentTrail.size(), newAssignments);
			m_assignemntTrailSizesWeCalledSolverFor.emplace_back(m_assignmentTrail.size());
//			if (conflictClause)
//				cout << "Theory gave us conflict: " << toString(*conflictClause) << endl;
		}
		if (conflictClause)
		{
			conflicts++;
			m_sumConflicts++;
			if (m_sumConflicts % 1000 == 999) {
				cout << "c confl: " << m_sumConflicts << std::endl;
			}
			if (currentDecisionLevel() == 0)
			{
//				cout << "Unsatisfiable" << endl;
				solution = 0;
				return true;
			}
			auto&& [learntClause, backtrackLevel] = analyze(move(*conflictClause));
			cancelUntil(backtrackLevel);
			while (!m_assignemntTrailSizesWeCalledSolverFor.empty() && m_assignemntTrailSizesWeCalledSolverFor.back() > m_assignmentTrail.size())
				m_assignemntTrailSizesWeCalledSolverFor.pop_back();
			if (m_backtrackNotify)
				m_backtrackNotify(m_assignemntTrailSizesWeCalledSolverFor.empty() ? 0 : m_assignemntTrailSizesWeCalledSolverFor.back());
			solAssert(!learntClause.empty());
			solAssert(!isAssigned(learntClause.front()));
//			for (size_t i = 1; i < learntClause.size(); i++)
//				solAssert(value(learntClause[i]) == TriState{false});

			addClause(move(learntClause));
			enqueue(m_clauses.back()->front(), &(*m_clauses.back()));
		}
		else
		{
			if (auto variable = nextDecisionVariable())
			{
// 				cout << "c Level " << currentDecisionLevel() << " - ";
// 				cout << ((m_assignments.size() * 100) / m_variables.size()) << "% of variables assigned." << endl;
				m_decisionPoints.emplace_back(m_assignmentTrail.size());
//				cout << "Deciding on " << m_variables.at(*variable) << " @" << currentDecisionLevel() << endl;

				// Polarity caching below
				bool positive = false;
				auto const& found = m_assignmentsCache.find(*variable);
				if (found != m_assignmentsCache.end()) positive = found->second;
				enqueue(Literal{positive, *variable}, nullptr);
			}
			else
			{
				//cout << "satisfiable." << endl;
				//for (auto&& [i, value]: m_assignments | ranges::view::enumerate())
				//	cout << " " << m_variables.at(i) << ": " << value.toString() << endl;
				solution = 1;
				model = m_assignments;
				return true;
			}
		}
	}
	return false;
}

void CDCL::setupWatches(Clause& _clause)
{
	for (size_t i = 0; i < min<size_t>(2, _clause.size()); i++)
		m_watches[_clause.at(i)].push_back(&_clause);
}

optional<Clause> CDCL::propagate()
{
	//cout << "Propagating." << endl;
	for (; m_assignmentQueuePointer < m_assignmentTrail.size(); m_assignmentQueuePointer++)
	{
		Literal toPropagate = m_assignmentTrail.at(m_assignmentQueuePointer);
		Literal falseLiteral = ~toPropagate;
		//cout << "Propagating " << toString(toPropagate) << endl;
		// Go through all watched clauses where this assignment makes the literal false.
		vector<Clause*> watchReplacement;
		auto it = m_watches[falseLiteral].begin();
		auto end = m_watches[falseLiteral].end();
		for (; it != end; ++it)
		{
			Clause& clause = **it;
			//cout << " watch clause: " << toString(clause) << endl;

			solAssert(!clause.empty());
			if (clause.front() != falseLiteral)
				swap(clause[0], clause[1]);
			solAssert(clause.front() == falseLiteral);
			if (clause.size() >= 2 && isAssignedTrue(clause[1]))
			{
				// Clause is already satisfied, keezp the watch.
				//cout << " -> already satisfied by " << toString(clause[1]) << endl;
				watchReplacement.emplace_back(&clause);
				continue;
			}

			// find a new watch to swap
			for (size_t i = 2; i < clause.size(); i++)
				if (isUnknownOrAssignedTrue(clause[i]))
				{
					//cout << " -> swapping " << toString(clause.front()) << " with " << toString(clause[i]) << endl;
					swap(clause.front(), clause[i]);
					m_watches[clause.front()].emplace_back(&clause);
					break;
				}
			if (clause.front() != falseLiteral)
				continue; // we found a new watch

			// We did not find a new watch, i.e. all literals starting from index 2
			// are false, thus clause[1] has to be true (if it exists)
			if (clause.size() == 1 || isAssignedFalse(clause[1]))
			{
//				if (clause.size() >= 2)
//					cout << " - Propagate resulted in conflict because " << toString(clause[1]) << " is also false." << endl;
//				else
//					cout << " - Propagate resulted in conflict since clause is single-literal." << endl;
				// Copy over the remaining watches and replace.
				while (it != end) watchReplacement.emplace_back(move(*it++));
				m_watches[falseLiteral] = move(watchReplacement);
				// Mark the queue as finished.
				m_assignmentQueuePointer = m_assignmentTrail.size();
				return clause;
			}
			else
			{
//				cout << " - resulted in new assignment: " << toString(clause[1]) << endl;
				watchReplacement.emplace_back(&clause);
				enqueue(clause[1], &clause);
			}
		}
		m_watches[falseLiteral] = move(watchReplacement);
	}
	return nullopt;
}


std::pair<Clause, size_t> CDCL::analyze(Clause _conflictClause)
{
	solAssert(!_conflictClause.empty());
	//cout << "Analyzing conflict." << endl;
	Clause learntClause;
	size_t backtrackLevel = 0;
	vmtf_vars_to_bump.clear();

	set<size_t> seenVariables;

	int pathCount = 0;
	size_t trailIndex = m_assignmentTrail.size() - 1;
	optional<Literal> resolvingLiteral;
	do
	{
		//cout << " conflict clause: " << toString(_conflictClause) << endl;
		for (Literal literal: _conflictClause)
			if ((!resolvingLiteral || literal != *resolvingLiteral) && !seenVariables.count(literal.variable))
			{
				seenVariables.insert(literal.variable);
				size_t variableLevel = m_levelForVariable.at(literal.variable);
				if (variableLevel == currentDecisionLevel())
				{
					//cout << "    ignoring " << toString(literal) << " at current decision level." << endl;
					// ignore variable, we will apply resolution with its reason.
					pathCount++;
				}
				else
				{
					//cout << "    adding " << toString(literal) << " @" << variableLevel << " to learnt clause." << endl;
					vmtf_vars_to_bump.push_back(literal.variable);
					learntClause.push_back(literal);
					backtrackLevel = max(backtrackLevel, variableLevel);
				}
			}/*
			else
				cout << "    already seen " << toString(literal) << endl;*/

		solAssert(pathCount > 0);
		pathCount--;
		while (!seenVariables.count(m_assignmentTrail[trailIndex--].variable));
		resolvingLiteral = m_assignmentTrail[trailIndex + 1];
		//cout << "  resolving literal: " << toString(*resolvingLiteral) << endl;
		seenVariables.erase(resolvingLiteral->variable);
		// TODO Is there always a reason? Not if it's a decision variable.
		if (pathCount > 0)
		{
			_conflictClause = *m_reason.at(*resolvingLiteral);
			//cout << "  reason: " << toString(_conflictClause) << endl;
		}
	}
	while (pathCount > 0);
	solAssert(resolvingLiteral);
	learntClause.push_back(~(*resolvingLiteral));
	// Move to front so we can directly propagate.
	swap(learntClause.front(), learntClause.back());

	std::sort(vmtf_vars_to_bump.begin(),vmtf_vars_to_bump.end(), vmtf_analyze_bumped_smaller(vmtf_btab));
	for (auto const& v: vmtf_vars_to_bump) vmtf_bump_queue(v);

	//cout << "-> learnt clause: " << toString(learntClause) << " backtrack to " << backtrackLevel << endl;


	return {move(learntClause), backtrackLevel};
}

void CDCL::addClause(Clause _clause)
{
// 	vmtf_btab.insert(vmtf_btab.end(), m_variables.size(), 0);
// 	vmtf_links.insert(vmtf_links.end(), m_variables.size(), Link());
// 	for(size_t i = 0; i < m_variables.size(); i++) vmtf_init_enqueue(i);

	size_t max_var = (uint32_t)vmtf_btab.size();
	size_t new_max_var = 0;
	for(auto const& l: _clause) new_max_var = std::max(l.variable+1, max_var);

	size_t to_add = new_max_var - max_var;
	vmtf_btab.insert(vmtf_btab.end(), to_add, 0);
	vmtf_links.insert(vmtf_links.end(), to_add, Link());
	//for(size_t i = 0; i < m_variables.size(); i++) vmtf_init_enqueue(i);

	for(auto const& l: _clause) {
		if (vmtf_links[l.variable].prev == std::numeric_limits<size_t>::max() &&
			vmtf_links[l.variable].next == std::numeric_limits<size_t>::max() &&
			vmtf_queue.last != l.variable)
		{
			vmtf_init_enqueue(l.variable);
		}
	}

	m_clauses.push_back(make_unique<Clause>(move(_clause)));
	setupWatches(*m_clauses.back());
}

void CDCL::enqueue(Literal const& _literal, Clause const* _reason)
{
	/*
	cout << "Enqueueing " << toString(_literal) << " @" << currentDecisionLevel() << endl;
	if (_reason)
		cout << "  because of " << toString(*_reason) << endl;
*/
	// TODO assert that assignmnets was unknown
	m_assignments[_literal.variable] = _literal.positive;
	m_levelForVariable[_literal.variable] = currentDecisionLevel();
	if (_reason) {
		m_reason[_literal] = _reason;
	}
	m_assignmentTrail.push_back(_literal);
}

void CDCL::cancelUntil(size_t _backtrackLevel)
{
	// TODO what if we backtrack to zero?
	//cout << "Canceling until " << _backtrackLevel << endl;
	solAssert(m_assignmentQueuePointer == m_assignmentTrail.size());
	size_t assignmentsToUndo = m_assignmentTrail.size() - m_decisionPoints.at(_backtrackLevel);
	if (m_assignmentTrail.size() > m_longest_trail) {
		m_assignmentsCache = m_assignments;
		m_longest_trail = m_assignmentTrail.size();
	}

	for (size_t i = 0; i < assignmentsToUndo; i++)
	{
		Literal l = m_assignmentTrail.back();
		//cout << "  undoing " << toString(l) << endl;
		m_assignmentTrail.pop_back();
		m_assignments.erase(l.variable);
		m_reason.erase(l);
		// TODO maybe could do without.
		m_levelForVariable.erase(l.variable);
		if (vmtf_queue.bumped < vmtf_btab[l.variable]) {
			vmtf_update_queue_unassigned(l.variable);
		}
	}
	m_decisionPoints.resize(_backtrackLevel);
	m_assignmentQueuePointer = m_assignmentTrail.size();

	solAssert(currentDecisionLevel() == _backtrackLevel);
}

optional<size_t> CDCL::nextDecisionVariable()
{
	const size_t v = vmtf_pick_var();
	if (v == std::numeric_limits<size_t>::max()) return nullopt;
	return v;
}

bool CDCL::isAssigned(Literal const& _literal) const
{
	return m_assignments.count(_literal.variable);
}

bool CDCL::isAssignedTrue(Literal const& _literal) const
{
	return (
		m_assignments.count(_literal.variable) &&
		m_assignments.at(_literal.variable) == _literal.positive
	);
}

bool CDCL::isAssignedFalse(Literal const& _literal) const
{
	return (
		m_assignments.count(_literal.variable) &&
		!m_assignments.at(_literal.variable) == _literal.positive
	);
}

bool CDCL::isUnknownOrAssignedTrue(Literal const& _literal) const
{
	return (
		!m_assignments.count(_literal.variable) ||
		m_assignments.at(_literal.variable) == _literal.positive
	);
}

string CDCL::toString(Literal const& _literal) const
{
	return (_literal.positive ? "" : "~") + m_variables.at(_literal.variable);
}

string CDCL::toString(Clause const& _clause) const
{
	vector<string> literals;
	for (Literal const& l: _clause)
		literals.emplace_back(toString(l));
	return "(" + joinHumanReadable(literals) + ")";
}

