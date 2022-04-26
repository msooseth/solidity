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

void CDCL::vmtfInitEnqueue (const size_t var)
{
	assert(var < m_vmtfLinks.size());
	Link & l = m_vmtfLinks[var];

	//Put at the end of the queue
	l.next = numeric_limits<size_t>::max();
	if (m_vmtfQueue.last != numeric_limits<size_t>::max()) {
		// Not empty queue
		assert(m_vmtfLinks[m_vmtfQueue.last].next == numeric_limits<size_t>::max());
		m_vmtfLinks[m_vmtfQueue.last].next = var;
	} else {
		// Empty queue
		assert(m_vmtfQueue.first == numeric_limits<size_t>::max());
		m_vmtfQueue.first = var;
	}
	l.prev = m_vmtfQueue.last;
	m_vmtfQueue.last = var;

	m_vmtfBumpVal[var] = ++m_bumped; // set timestamp of enqueue
	vmtfUpdateQueueUnassigned(m_vmtfQueue.last);
}

void CDCL::vmtfBumpQueue (const size_t var) {
	if (m_vmtfLinks[var].next == numeric_limits<size_t>::max()) return;

	m_vmtfQueue.dequeue (m_vmtfLinks, var);
	m_vmtfQueue.enqueue (m_vmtfLinks, var);

	assert (m_bumped != numeric_limits<uint64_t>::max());
	m_vmtfBumpVal[var] = ++m_bumped;
	if (!m_assignments.count(var)) vmtfUpdateQueueUnassigned(var);
}

void CDCL::vmtfUpdateQueueUnassigned (const size_t var)
{
	assert(var != numeric_limits<size_t>::max());
	m_vmtfQueue.bumped = m_vmtfBumpVal[var];
	m_vmtfQueue.unassigned = var;
}

size_t CDCL::vmtfPickVar()
{
	uint64_t searched = 0;
	size_t var = m_vmtfQueue.unassigned;

	while (var != numeric_limits<size_t>::max() && m_assignments.count(var))
	{
		var = m_vmtfLinks[var].prev;
		searched++;
	}

	if (var == numeric_limits<size_t>::max()) return var;
	if (searched) vmtfUpdateQueueUnassigned(var);
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
	int loop = 0;
	std::optional<bool> ret = nullopt;
	while(ret == nullopt) {
		loop++;
		uint32_t max_conflicts = (uint32_t)((double)luby(2, loop) * 40.0);
		ret = solveLoop(max_conflicts, model);
		cout << "c restarting" << endl;
	}
	cout << "c solved, conflicts: " << m_sumConflicts << endl;

	if (*ret) return model;
	else return nullopt;
}

optional<bool> CDCL::solveLoop(const uint32_t max_conflicts, CDCL::Model& model)
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
				return false;
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
				model = m_assignments;
				return true;
			}
		}
	}
	return nullopt;
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
	m_vmtfVarsToBump.clear();

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
					m_vmtfVarsToBump.push_back(literal.variable);
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

	std::sort(m_vmtfVarsToBump.begin(),m_vmtfVarsToBump.end(), vmtf_analyze_bumped_smaller(m_vmtfBumpVal));
	for (auto const& v: m_vmtfVarsToBump) vmtfBumpQueue(v);

	//cout << "-> learnt clause: " << toString(learntClause) << " backtrack to " << backtrackLevel << endl;


	return {move(learntClause), backtrackLevel};
}

void CDCL::addClause(Clause _clause)
{
// 	m_vmtfBumpVal.insert(m_vmtfBumpVal.end(), m_variables.size(), 0);
// 	m_vmtfLinks.insert(m_vmtfLinks.end(), m_variables.size(), Link());
// 	for(size_t i = 0; i < m_variables.size(); i++) vmtfInitEnqueue(i);

	size_t max_var = (uint32_t)m_vmtfBumpVal.size();
	size_t new_max_var = 0;
	for(auto const& l: _clause) new_max_var = std::max(l.variable+1, max_var);

	size_t to_add = new_max_var - max_var;
	m_vmtfBumpVal.insert(m_vmtfBumpVal.end(), to_add, 0);
	m_vmtfLinks.insert(m_vmtfLinks.end(), to_add, Link());
	//for(size_t i = 0; i < m_variables.size(); i++) vmtfInitEnqueue(i);

	for(auto const& l: _clause) {
		if (m_vmtfLinks[l.variable].prev == std::numeric_limits<size_t>::max() &&
			m_vmtfLinks[l.variable].next == std::numeric_limits<size_t>::max() &&
			m_vmtfQueue.last != l.variable)
		{
			vmtfInitEnqueue(l.variable);
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
		if (m_vmtfQueue.bumped < m_vmtfBumpVal[l.variable]) {
			vmtfUpdateQueueUnassigned(l.variable);
		}
	}
	m_decisionPoints.resize(_backtrackLevel);
	m_assignmentQueuePointer = m_assignmentTrail.size();

	solAssert(currentDecisionLevel() == _backtrackLevel);
}

optional<size_t> CDCL::nextDecisionVariable()
{
	const size_t v = vmtfPickVar();
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

