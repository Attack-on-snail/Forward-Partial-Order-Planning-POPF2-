#include "RPGBuilder.h"
#include "globals.h"
#include "numericanalysis.h"
#include "temporalanalysis.h"
#include "FFSolver.h"

#include "typecheck.h"
#include "TIM.h"
#include "FuncAnalysis.h"

#include "colours.h"

using namespace TIM;
using namespace Inst;
using namespace VAL;

#include <iostream>
#include <sstream>
using std::endl;
using std::ostringstream;

namespace Planner
{

//寻找动作不被其他动作删除的效果，这样的话，一旦该动作开始，就无需再次开始。填充uninterestingnessCriteria
void RPGBuilder::findUninterestingnessCriteria()
{
    const int opCount = instantiatedOps.size();

    for (int i = 0; i < opCount; ++i)
    {
        if (!rogueActions[i])
        {
            bool allUninteresting = true;
            int criterion = -1;
            // 收集动作添加的唯一开始添加效果（不被其他动作删除），放入criterion，否则allUninteresting = false
            {
                list<Literal *> &effs = actionsToStartEffects[i];
                list<Literal *>::iterator effItr = effs.begin();
                const list<Literal *>::iterator effEnd = effs.end();

                for (; effItr != effEnd; ++effItr)
                {
                    if (negativeEffectsToActions[(*effItr)->getStateID()].empty())
                    {
                        criterion = (*effItr)->getStateID();
                    }
                    else
                    {
                        allUninteresting = false;
                        break;
                    }
                }
            }

            // 收集动作添加的唯一结束添加效果（不被其他动作删除），放入criterion, 否则allUninteresting = false
            if (allUninteresting)
            {
                list<Literal *> &effs = actionsToEndEffects[i];
                list<Literal *>::iterator effItr = effs.begin();
                const list<Literal *>::iterator effEnd = effs.end();

                for (; effItr != effEnd; ++effItr)
                {
                    if (negativeEffectsToActions[(*effItr)->getStateID()].empty())
                    {
                        criterion = (*effItr)->getStateID();
                    }
                    else
                    {
                        allUninteresting = false;
                        break;
                    }
                }
            }

            // 判断动作的数值效果（不被其他动作删除），放入criterion
            if (allUninteresting)
            { // checked props, now onto numerics
                //if (criterion == -1) {
                //  cout << "Action " << i << " - " << *(instantiatedOps[i]) << " is propositionally uninteresting once applied: no propositional effects (" << actionsToStartEffects[i].size() << ", " << actionsToEndEffects[i].size() << ")\n";
                //} else {
                //  cout << "Action " << i << " - " << *(instantiatedOps[i]) << " is propositionally uninteresting once applied: nothing deletes " << *(literals[criterion]) << "\n";
                //}

                //开始数值效果
                {
                    list<int> &numEffs = actionsToRPGNumericStartEffects[i];

                    list<int>::iterator neItr = numEffs.begin();
                    const list<int>::iterator neEnd = numEffs.end();

                    for (; neItr != neEnd; ++neItr)
                    {
                        RPGNumericEffect &currRNE = rpgNumericEffects[*neItr];
                        if (NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_METRICTRACKING || NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_IRRELEVANT)
                        {
                        }
                        else
                        {
                            if (currRNE.size == 0 && !currRNE.isAssignment)
                            { //只有常量，并且是+=
                                if (NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_SMALLERISBETTER)
                                {
                                    if (currRNE.constant < 0.0)
                                    {
                                        allUninteresting = false;
                                        break;
                                    }
                                }
                                else if (NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_BIGGERISBETTER)
                                {
                                    if (currRNE.constant > 0.0)
                                    {
                                        allUninteresting = false;
                                        break;
                                    }
                                }
                                else
                                {
                                    // no known dominance - might be a good effect
                                    allUninteresting = false;
                                    break;
                                }
                            }
                            else
                            {
                                allUninteresting = false;
                                break;
                            }
                        }
                    }
                }

                //线性连续数值效果
                LinearEffects *const currLE = linearDiscretisation[i];

                if (currLE)
                {
                    const int varCount = currLE->vars.size();
                    for (int vc = 0; vc < varCount; ++vc)
                    {
                        if (NumericAnalysis::getDominanceConstraints()[currLE->vars[vc]] == NumericAnalysis::E_METRICTRACKING || NumericAnalysis::getDominanceConstraints()[currLE->vars[vc]] == NumericAnalysis::E_IRRELEVANT)
                        {
                        }
                        else
                        {
                            if (NumericAnalysis::getDominanceConstraints()[currLE->vars[vc]] == NumericAnalysis::E_SMALLERISBETTER)
                            {
                                if (currLE->effects[0][vc].constant < 0.0)
                                {
                                    allUninteresting = false;
                                    break;
                                }
                            }
                            else if (NumericAnalysis::getDominanceConstraints()[currLE->vars[vc]] == NumericAnalysis::E_BIGGERISBETTER)
                            {
                                if (currLE->effects[0][vc].constant > 0.0)
                                {
                                    allUninteresting = false;
                                    break;
                                }
                            }
                            else
                            {
                                // no known dominance - might be a good effect
                                allUninteresting = false;
                                break;
                            }
                        }
                    }
                }

                //结束数值效果
                if (allUninteresting)
                {
                    list<int> &numEffs = actionsToRPGNumericEndEffects[i];

                    list<int>::iterator neItr = numEffs.begin();
                    const list<int>::iterator neEnd = numEffs.end();

                    for (; neItr != neEnd; ++neItr)
                    {
                        RPGNumericEffect &currRNE = rpgNumericEffects[*neItr];
                        if (NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_METRICTRACKING || NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_IRRELEVANT)
                        {
                        }
                        else
                        {
                            if (currRNE.size == 0 && !currRNE.isAssignment)
                            {
                                if (NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_SMALLERISBETTER)
                                {
                                    if (currRNE.constant < 0.0)
                                    {
                                        allUninteresting = false;
                                        break;
                                    }
                                }
                                else if (NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_BIGGERISBETTER)
                                {
                                    if (currRNE.constant > 0.0)
                                    {
                                        allUninteresting = false;
                                        break;
                                    }
                                }
                                else
                                {
                                    // no known dominance - might be a good effect
                                    allUninteresting = false;
                                    break;
                                }
                            }
                            else
                            {
                                allUninteresting = false;
                                break;
                            }
                        }
                    }
                }

                if (allUninteresting)
                {
                    // cout << "Action " << i << " - " << *(instantiatedOps[i]) << " is uninteresting";
                    if (criterion != -1)
                    {
                        // cout << " once we have fact " << *(literals[criterion]) << "\n";
                        uninterestingnessCriteria[i] = criterion;
                    }
                    else
                    {
                        // cout << " full stop - there's no reason ever to apply it\n";
                        uninterestingnessCriteria[i] = -1;
                    }
                }
            }
        }
    }
};

class ConstantNumericEffectStartEndPair
{

protected:
    bool affectedAtStart;
    double effectAtStart;
    bool affectedAtEnd;
    double effectAtEnd;

public:
    ConstantNumericEffectStartEndPair()
        : affectedAtStart(false), effectAtStart(0.0), affectedAtEnd(false), effectAtEnd(0.0)
    {
    }

    void addStartEffect(const double &d)
    {
        affectedAtStart = true;
        effectAtStart = d;
    }

    void addEndEffect(const double &d)
    {
        affectedAtEnd = true;
        effectAtEnd = d;
    }

    double getNetOutcome() const
    {
        return effectAtStart + effectAtEnd;
    }
};

//没看懂，填充concurrentRedundantActions
void RPGBuilder::findConcurrentRedundantActions()
{
    const int opCount = instantiatedOps.size();

    // If allActionsDeletingADeleteB[a][b] is true, then any (snap) action deleting a deletes b
    map<int, map<int, bool>> allActionsDeletingADeleteB;

    for (int i = 0; i < opCount; ++i)
    {
        if (rogueActions[i])
        {
            continue;
        }

        if (uninterestingnessCriteria.find(i) != uninterestingnessCriteria.end())
        {
            // already have a one-way fact condition, which is necessarily as strong as the concurrent redundant action condition
            continue;
        }

        // First, think about numbers.  This is the most involved part: we need to make sure the net-effect of this action
        // is non-positive, and that between the start and the end there intermediate values of variables changed at both
        // the start and the end is necessarily worse than if the start effect hadn't occurred.

        bool allUninteresting = true;

        map<int, ConstantNumericEffectStartEndPair> actionStartEndEffectsOnVariable;

        //RPG数值开始效果，
        {
            list<int> &numEffs = actionsToRPGNumericStartEffects[i];

            list<int>::iterator neItr = numEffs.begin();
            const list<int>::iterator neEnd = numEffs.end();

            for (; neItr != neEnd; ++neItr)
            {
                RPGNumericEffect &currRNE = rpgNumericEffects[*neItr];
                if (NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_METRICTRACKING || NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_IRRELEVANT)
                {
                }
                else
                {
                    if (currRNE.size == 0 && !currRNE.isAssignment)
                    { //没有数值效果，即常值且效果是+=
                        if (NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_SMALLERISBETTER)
                        {
                            if (currRNE.constant < 0.0)
                            {
                                allUninteresting = false;
                                break;
                            }
                        }
                        else if (NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_BIGGERISBETTER)
                        {
                            if (currRNE.constant > 0.0)
                            {
                                allUninteresting = false;
                                break;
                            }
                        }
                        else
                        {
                            // no known dominance
                            allUninteresting = false;
                            break;
                        }

                        // If we get this far, the start effect is to either increase something that is better smaller; or decrease
                        // something that is better bigger.  So, on its own, the start is a bad move.  But, record it and revisit
                        // later, increase an end effect gives a net-gain to this action.
                        actionStartEndEffectsOnVariable[currRNE.fluentIndex].addStartEffect(currRNE.constant);
                    }
                    else
                    {
                        allUninteresting = false;
                        break;
                    }
                }
            }
        }

        if (!allUninteresting)
        {
            continue;
        }

        //RPG数值结束效果，
        {
            list<int> &numEffs = actionsToRPGNumericEndEffects[i];

            list<int>::iterator neItr = numEffs.begin();
            const list<int>::iterator neEnd = numEffs.end();

            for (; neItr != neEnd; ++neItr)
            {
                RPGNumericEffect &currRNE = rpgNumericEffects[*neItr];
                if (NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_METRICTRACKING || NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_IRRELEVANT)
                {
                }
                else
                {
                    if (currRNE.size == 0 && !currRNE.isAssignment)
                    {
                        ConstantNumericEffectStartEndPair &netEffect = actionStartEndEffectsOnVariable[currRNE.fluentIndex];
                        netEffect.addEndEffect(currRNE.constant);

                        if (NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_SMALLERISBETTER)
                        {
                            if (netEffect.getNetOutcome() < -0.000000001)
                            {
                                allUninteresting = false;
                                break;
                            }
                        }
                        else if (NumericAnalysis::getDominanceConstraints()[currRNE.fluentIndex] == NumericAnalysis::E_BIGGERISBETTER)
                        {
                            if (netEffect.getNetOutcome() > 0.000000001)
                            {
                                allUninteresting = false;
                                break;
                            }
                        }
                        else
                        {
                            // no known dominance
                            allUninteresting = false;
                            break;
                        }
                    }
                    else
                    {
                        allUninteresting = false;
                        break;
                    }
                }
            }
        }

        if (!allUninteresting)
        {
            continue;
        }

        // If we get this far, then the numeric effects of the action are not overall (or intermediately) beneficial
        // Now check for propositions: start and end add effects must be undeletable throughout the action's execution

        const list<Literal *> &invariants = RPGBuilder::actionsToInvariants[i];

        for (int pass = 0; allUninteresting && pass < 2; ++pass)
        {

            const list<Literal *> &propositionalAdds = (pass ? RPGBuilder::getEndPropositionAdds()[i] : RPGBuilder::getStartPropositionAdds()[i]);

            list<Literal *>::const_iterator effItr = propositionalAdds.begin();
            const list<Literal *>::const_iterator effEnd = propositionalAdds.end();

            for (int fID; allUninteresting && effItr != effEnd; ++effItr)
            {
                fID = (*effItr)->getStateID();

                bool cannotBeDeletedDuringExecution = false;

                for (int checkPass = 0; checkPass < 2; ++checkPass)
                {

                    // checkPass = 0: see if there's already an invariant known to be co-deleted along with fID
                    // checkPass = 1: for invariants whose co-deletion potential is unknown, work it out

                    list<Literal *>::const_iterator invItr = invariants.begin();
                    const list<Literal *>::const_iterator invEnd = invariants.end();

                    for (; invItr != invEnd; ++invItr)
                    {
                        const int otherFID = (*invItr)->getStateID();

                        bool plausible = true; //plausible:可信的

                        map<int, map<int, bool>>::const_iterator cdItr = allActionsDeletingADeleteB.find(fID);
                        if (cdItr != allActionsDeletingADeleteB.end())
                        {
                            map<int, bool>::const_iterator cd2Itr = cdItr->second.find(otherFID);
                            if (cd2Itr != cdItr->second.end())
                            {
                                if (cd2Itr->second)
                                {
                                    // found a known co-deleted fact
                                    cannotBeDeletedDuringExecution = true;
                                    break;
                                }
                                else
                                {
                                    plausible = false;
                                }
                            }
                        }

                        if (plausible && checkPass == 1)
                        {
                            set<pair<int, VAL::time_spec>> actionsDeletingAButNotB;
                            actionsDeletingAButNotB.insert(negativeEffectsToActions[fID].begin(), negativeEffectsToActions[fID].end());

                            list<pair<int, VAL::time_spec>>::const_iterator bdItr = negativeEffectsToActions[otherFID].begin();
                            const list<pair<int, VAL::time_spec>>::const_iterator bdEnd = negativeEffectsToActions[otherFID].end();

                            for (; bdItr != bdEnd; ++bdItr)
                            {
                                actionsDeletingAButNotB.erase(*bdItr);
                            }

                            if (actionsDeletingAButNotB.empty())
                            {
                                allActionsDeletingADeleteB[fID][otherFID] = true;
                                cannotBeDeletedDuringExecution = true;
                                break;
                            }
                            else
                            {
                                allActionsDeletingADeleteB[fID][otherFID] = false;
                            }
                        }
                    }

                    if (cannotBeDeletedDuringExecution)
                    {
                        break;
                    }
                }

                if (!cannotBeDeletedDuringExecution)
                {
                    allUninteresting = false;
                }
            }
        }

        if (allUninteresting)
        {
            concurrentRedundantActions.insert(i);
            cout << "Action " << i << " - " << *(instantiatedOps[i]) << " is concurrent-redundant\n";
        }
    }
}

//若不是E_METRICTRACKING直接报错，终止程序
void RPGBuilder::checkConditionalNumericEffectsAreOnlyOnMetricTrackingVariables()
{
    const int opCount = actionsToConditionalEffects.size();

    for (int op = 0; op < opCount; ++op)
    {
        if (rogueActions[op])
            continue;

        list<ConditionalEffect>::const_iterator eff = actionsToConditionalEffects[op].begin();
        const list<ConditionalEffect>::const_iterator effEnd = actionsToConditionalEffects[op].end();

        for (; eff != effEnd; ++eff)
        {
            list<pair<int, VAL::time_spec>>::const_iterator numEff = eff->getNumericEffects().begin();
            const list<pair<int, VAL::time_spec>>::const_iterator numEffEnd = eff->getNumericEffects().end();

            for (; numEff != numEffEnd; ++numEff)
            {
                const RPGBuilder::RPGNumericEffect &currEff = RPGBuilder::getNumericEff()[numEff->first];
                if (NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] != NumericAnalysis::E_METRICTRACKING && NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] != NumericAnalysis::E_IRRELEVANT)
                {
                    postmortem_noADL();
                }
            }
        }
    }
}

void copyLiteralListToSet(list<Literal *> &theList, LiteralSet &theSet)
{

    list<Literal *>::iterator tlItr = theList.begin();
    const list<Literal *>::iterator tlEnd = theList.end();

    for (; tlItr != tlEnd; ++tlItr)
        theSet.insert(*tlItr);
};

//class OneShotKShotFormula : public KShotFormula {
//
//private:
//list<int> watchedLiterals;
//public:
//OneShotKShotFormula(list<int> & toWatch) : KShotFormula(), watchedLiterals(toWatch) {};
//  virtual int getLimit(MinimalState & s);
//};

int RPGBuilder::OneShotKShotFormula::getLimit(const MinimalState &s) const
{

    list<int>::const_iterator wlItr = watchedLiterals.begin();
    const list<int>::const_iterator wlEnd = watchedLiterals.end();

    for (; wlItr != wlEnd; ++wlItr)
    {
        if (s.first.find(*wlItr) == s.first.end())
            return 0;
    }

    return 1;
};

int RPGBuilder::OneShotKShotFormula::getOptimisticLimit(const MinimalState &) const
{
    //cout << "Optimistic limit on one shot: 1\n";
    return 1;
};

int RPGBuilder::KShotKShotFormula::getLimit(const MinimalState &s) const
{
    int minShots = INT_MAX;

    list<ShotCalculator>::const_iterator sfItr = formulae.begin();
    const list<ShotCalculator>::const_iterator sfEnd = formulae.end();

    for (; sfItr != sfEnd; ++sfItr)
    {

        const int thisShots = (int)((s.secondMax[sfItr->variable] - sfItr->greaterThan) / sfItr->decreaseBy);
        if (thisShots < minShots)
            minShots = thisShots;
    }

    return (minShots > 0 ? minShots : 0);
}

int RPGBuilder::KShotKShotFormula::getOptimisticLimit(const MinimalState &s) const
{
    //cout << "Optimistic limit on K shot: same as limit\n";
    return getLimit(s);
};

//根据formula计算右常值，存入cValue
bool constOnlyCalculate(const list<RPGBuilder::Operand> &formula, vector<double> &fluents, double &cValue)
{
    list<double> RHS;

    list<RPGBuilder::Operand>::const_iterator fItr = formula.begin();
    const list<RPGBuilder::Operand>::const_iterator fEnd = formula.end();

    for (; fItr != fEnd; ++fItr)
    {
        const RPGBuilder::Operand &currOperand = *fItr;
        const RPGBuilder::math_op currMathOp = currOperand.numericOp;
        switch (currMathOp)
        {
        case RPGBuilder::NE_ADD:
        {
            const double oldFront = RHS.front();
            RHS.pop_front();
            RHS.front() += oldFront;
        }
        break;
        case RPGBuilder::NE_SUBTRACT:
        {
            const double oldFront = RHS.front();
            RHS.pop_front();
            RHS.front() -= oldFront;
        }
        break;
        case RPGBuilder::NE_MULTIPLY:
        {
            const double oldFront = RHS.front();
            RHS.pop_front();
            RHS.front() *= oldFront;
        }
        break;
        case RPGBuilder::NE_DIVIDE:
        {
            const double oldFront = RHS.front();
            RHS.pop_front();
            RHS.front() /= oldFront;
        }
        break;
        case RPGBuilder::NE_CONSTANT:
            RHS.push_front(currOperand.constantValue);
            break;
        case RPGBuilder::NE_FLUENT:
            return false;
            break;
        default:
            // this should never happen
            assert(false);
        }
    }

    cValue = RHS.front();
    return true;
};

void RPGBuilder::findSelfMutexes()
{
    const int opCount = instantiatedOps.size();
    selfMutexes = vector<bool>(opCount, false);

    //在开始前提需要但是开始效果就删除的文字，所在的动作，一起构成该数据结构
    // For each literal, the actions in the associated set (each of which has a start pre and
    // a start delete of that literal) are self-mutex iff the only actions adding this fact
    // are in that set
    map<int, set<int>> potentiallySelfMutexActionsDueToFact;

    for (int i = 0; i < opCount; ++i)
    {
        if (rogueActions[i])
            continue;

        LiteralSet startPreconditions;
        LiteralSet startDeletes;
        LiteralSet startAdds;

        copyLiteralListToSet(actionsToStartPreconditions[i], startPreconditions);
        copyLiteralListToSet(actionsToStartNegativeEffects[i], startDeletes);
        copyLiteralListToSet(actionsToStartEffects[i], startAdds);

        //在开始段删除但没立即添加的literal
        // facts deleted at the start which aren't immediately re-added
        LiteralSet overallStartDeletes;
        std::set_difference(startDeletes.begin(), startDeletes.end(),
                            startAdds.begin(), startAdds.end(),
                            std::insert_iterator<LiteralSet>(overallStartDeletes, overallStartDeletes.begin())); /*求集合差*/

        // 开始前提需要但是立即删除的literal, facts needed at the start that are then immediately deleted
        LiteralSet isect;
        std::set_intersection(startPreconditions.begin(), startPreconditions.end(),
                              overallStartDeletes.begin(), overallStartDeletes.end(),
                              std::insert_iterator<LiteralSet>(isect, isect.begin())); /*求集合交集*/

        // bail out if there are no possibly self-mutex-inducing facts
        if (isect.empty())
        {
            //cout << "Action " << *(RPGBuilder::getInstantiatedOp(i)) << " doesn't delete any of its own preconditions at the start; " << overallStartDeletes.size() << " strong start deletes, " << startPreconditions.size() << " start preconditions\n";
            continue;
        }

        LiteralSet endAdds;
        copyLiteralListToSet(actionsToEndEffects[i], endAdds);

        // 在结束时添加需要的前提literal， facts that are in isect, and also added at the end
        LiteralSet candidates;
        std::set_intersection(endAdds.begin(), endAdds.end(),
                              isect.begin(), isect.end(),
                              std::insert_iterator<LiteralSet>(candidates, candidates.begin()));

        LiteralSet::const_iterator fItr = isect.begin();
        const LiteralSet::const_iterator fEnd = isect.end();

        for (; fItr != fEnd; ++fItr)
        {
            // note that we might have a self-mutex inducing fact for this action
            //cout << "Action " << *(RPGBuilder::getInstantiatedOp(i)) << " might be self-mutex due to " << *(*fItr) << std::endl;
            potentiallySelfMutexActionsDueToFact[(*fItr)->getStateID()].insert(i);
        }
    }

    map<int, set<int>>::const_iterator mutexGroup = potentiallySelfMutexActionsDueToFact.begin();
    const map<int, set<int>>::const_iterator mutexGroupEnd = potentiallySelfMutexActionsDueToFact.end();

    //确定自我互斥的动作集合selfMutexes
    for (; mutexGroup != mutexGroupEnd; ++mutexGroup)
    {
        set<int> adders;

        //为每个有问题的literal寻找在结束时添加该文字的动作，即为adders
        {
            set<int>::iterator insItr = adders.begin();

            const list<pair<int, VAL::time_spec>> &addedBy = effectsToActions[mutexGroup->first];

            list<pair<int, VAL::time_spec>>::const_iterator addItr = addedBy.begin();
            const list<pair<int, VAL::time_spec>>::const_iterator addEnd = addedBy.end();

            for (; addItr != addEnd; ++addItr)
            {
                if (addItr->second != VAL::E_AT_END)
                {
                    break;
                }
                insItr = adders.insert(insItr, addItr->first);
            }
            if (addItr != addEnd)
                continue;
        }

        //只有当adders是potentiallySelfMutexActionsDueToFact中动作的子集时，才能保证动作时自我互斥的
        // now we check that the set of actions that add the fact are a subset or equal to those in the set
        // if any aren't accounted for, we can't guarantee a self mutex
        set<int> notAccountedFor;
        std::set_difference(adders.begin(), adders.end(), mutexGroup->second.begin(), mutexGroup->second.end(),
                            std::insert_iterator<set<int>>(notAccountedFor, notAccountedFor.begin()));

        if (notAccountedFor.empty())
        {
            set<int>::const_iterator gItr = mutexGroup->second.begin();
            const set<int>::const_iterator gEnd = mutexGroup->second.end();

            for (; gItr != gEnd; ++gItr)
            {
                selfMutexes[*gItr] = true;
            }
        }
    }
};

//确定动作i的文字是否只在该动作中出现（one-shot），确定oneShotLiterals以及maybeOneShotLiteral
void RPGBuilder::kshotInferForAction(const int &i, MinimalState &refState, LiteralSet &maybeOneShotLiteral, vector<double> &initialFluents, const int &fluentCount)
{
    int oldKShotLimit = INT_MAX;

    if (kShotFormulae[i])
        oldKShotLimit = kShotFormulae[i]->getLimit(refState);

    if (oldKShotLimit > 1)
    {
        //(逻辑)删除效果同时是前提，但不被添加：可以被看成是oneshot，修改kShotFormulae[i]
        { // first, let's see if there's a simple propositional reason for it being oneshot
            // look for a delete effect not added by anything else, and required as a precond.

            LiteralSet allPreconditions; //所有命题条件，开始、不变、结束
            LiteralSet allDeletes;       //所有删除效果，开始、结束

            copyLiteralListToSet(actionsToStartPreconditions[i], allPreconditions);
            copyLiteralListToSet(actionsToInvariants[i], allPreconditions);
            copyLiteralListToSet(actionsToEndPreconditions[i], allPreconditions);

            copyLiteralListToSet(actionsToStartNegativeEffects[i], allDeletes);
            copyLiteralListToSet(actionsToEndNegativeEffects[i], allDeletes);

            //确定那些被删除同时也是前提的fact，即theIntersection
            set<int> theIntersection;
            {
                LiteralSet::iterator apItr = allPreconditions.begin();
                const LiteralSet::iterator apEnd = allPreconditions.end();

                LiteralSet::iterator adItr = allDeletes.begin();
                const LiteralSet::iterator adEnd = allDeletes.end();

                while (apItr != apEnd && adItr != adEnd)
                {
                    const int idOne = (*apItr)->getStateID();
                    const int idTwo = (*adItr)->getStateID();
                    if (idOne < idTwo)
                    {
                        ++apItr;
                    }
                    else if (idTwo < idOne)
                    {
                        ++adItr;
                    }
                    else
                    {
                        theIntersection.insert(idOne);
                        ++apItr;
                        ++adItr;
                    }
                };
            }

            //检查theIntersection是否被其他动作/one-shot添加，不是的话将其放入toWatch
            list<int> toWatch;
            {
                set<int>::iterator adItr = theIntersection.begin();
                const set<int>::iterator adEnd = theIntersection.end();

                for (; adItr != adEnd; ++adItr)
                {
                    const int currLitID = (*adItr);
                    if (effectsToActions[currLitID].empty())
                    {
                        toWatch.push_back(currLitID);
                    }
                    else if (oneShotLiterals[currLitID])
                    {
                        toWatch.push_back(currLitID);
                    }
                    else
                    {
                        //cout << "\t" << *(getLiteral(*adItr)) << " is added by actions, and isn't one-shot\n";
                    }
                }
            }

            if (!toWatch.empty())
            {
                //cout << "Have shown that " << *(instantiatedOps[i]) << " is one-shot\n";
                kShotFormulae[i] = new OneShotKShotFormula(toWatch);
            }
        }

        //（数值）数值变量v逐渐减小，前提条件为v > c，c为常值，动作效果为v - d，则该变量最多被k = (v-c)/d个动作利用
        if (!kShotFormulae[i])
        {
            // next case
            // - precondition says v > c where c is constant, probably 0 in any reasonable encoding, but may as well generalise
            // - v is strictly decreasing (ask TIM)
            // - the action decreases v by some amount d, where d is constant or strictly increasing (again, ask TIM)
            // - and thus, k = a formula (v - c) / d
            // this is weaker than the previous case, as the previous determines a bound of 1 or 0 depending on logical information
            // rather than k based on numeric information

            //actionsToRPGNumericStartPreconditions = vector<list<int> >(opCount);
            //actionsToRPGNumericInvariants = vector<list<int> >(opCount);
            //actionsToRPGNumericEndPreconditions = vector<list<int> >(opCount);

            //RHSVariable == -1， LHSVariable < fluentCount并且不等于-1
            //等同于 右值是常值，左值是变量？
            list<int> candidatePreconditions;
            {
                for (int pass = 0; pass < 3; ++pass)
                {
                    list<int> &currNP = (pass == 0 ? actionsToRPGNumericStartPreconditions[i] : (pass == 1 ? actionsToRPGNumericInvariants[i] : actionsToRPGNumericEndPreconditions[i]));
                    list<int>::iterator npItr = currNP.begin();
                    const list<int>::iterator npEnd = currNP.end();

                    for (; npItr != npEnd; ++npItr)
                    {
                        RPGNumericPrecondition &currPrec = rpgNumericPreconditions[*npItr];

                        if (currPrec.RHSVariable != -1)
                            break;

                        const int LHSVariable = currPrec.LHSVariable;
                        if (LHSVariable == -1)
                            break;
                        if (LHSVariable >= fluentCount)
                            break;

                        candidatePreconditions.push_back(*npItr);
                    }
                }
            }

            list<ShotCalculator> shotFormulae; // more than one, take min over
            {
                list<int>::iterator cpItr = candidatePreconditions.begin();
                const list<int>::iterator cpEnd = candidatePreconditions.end();

                for (; cpItr != cpEnd; ++cpItr)
                {

                    RPGNumericPrecondition &currPrec = rpgNumericPreconditions[*cpItr];

                    const double RHSConstant = currPrec.RHSConstant;
                    const int LHSVariable = currPrec.LHSVariable;

                    bool foundDecreaser = false;
                    double decreaseBy = 0.0;

                    //根据数值效果（加法、减法）确定要增加/减少的量，decreaseBy
                    for (int pass = 0; pass < 2; ++pass)
                    {
                        list<NumericEffect> &currNE = (pass == 0 ? actionsToStartNumericEffects[i] : actionsToEndNumericEffects[i]);
                        list<NumericEffect>::iterator neItr = currNE.begin();
                        const list<NumericEffect>::iterator neEnd = currNE.end();

                        //根据数值效果（加法、减法）确定要增加/减少的量
                        for (; neItr != neEnd; ++neItr)
                        {
                            if (neItr->fluentIndex == LHSVariable)
                            {
                                double decVal;

                                if (constOnlyCalculate(neItr->formula, initialFluents, decVal))
                                {
                                    if (neItr->op == VAL::E_DECREASE)
                                    {
                                        if (decVal > 0)
                                        {
                                            if (!foundDecreaser)
                                            {
                                                decreaseBy = decVal;
                                                foundDecreaser = true;
                                            }
                                            else
                                            {
                                                decreaseBy += decVal; // must have a start then end dec effect
                                            }
                                        }
                                    }
                                    else if (neItr->op == VAL::E_INCREASE)
                                    {
                                        if (decVal < 0)
                                        {
                                            if (!foundDecreaser)
                                            {
                                                decreaseBy = -decVal;
                                                foundDecreaser = true;
                                            }
                                            else
                                            {
                                                decreaseBy -= decVal; // must have a start then end dec effect
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }

                    //计算k值：构造shotFormulae
                    if (foundDecreaser && decreaseBy > 0.000000001)
                    {
                        PNE *const currPNE = getPNE(LHSVariable);

                        if (EFT(currPNE->getHead())->onlyGoingDown())
                        { //该函数数值变量一定减小
                            /*cout << "Have shown that " << *(instantiatedOps[i]) << " is k-shot\n where ";
                            if (RHSConstant) {
                                cout << "k = ceil(" << *(currPNE) << " - " << (RHSConstant - decreaseBy) << ")";
                            } else {
                                cout << "k = " << *(currPNE);
                            }
                            if (decreaseBy != 1.0) {
                                cout << " / " << decreaseBy << "\n";
                            } else {
                                cout << "\n";
                            }*/
                            shotFormulae.push_back(ShotCalculator(LHSVariable, (RHSConstant - decreaseBy), decreaseBy));
                        }
                    }
                }
            }

            if (!shotFormulae.empty())
            {
                kShotFormulae[i] = new KShotKShotFormula(shotFormulae);
            }
        }

        // otherwise, if we can't prove anything useful, it's unlimited

        if (!kShotFormulae[i])
        {
            kShotFormulae[i] = new UnlimitedKShotFormula();
        }
        else
        {
            //cout << "Have an analysis now - says limit is " << kShotFormulae[i]->getLimit(refState) << "\n";
        }

        //确定oneShotLiterals以及maybeOneShotLiteral
        if (kShotFormulae[i]->getLimit(refState) <= 1)
        {
            LiteralSet startAdds;
            LiteralSet endDeletes;

            copyLiteralListToSet(actionsToStartEffects[i], startAdds);
            copyLiteralListToSet(actionsToEndNegativeEffects[i], endDeletes);

            set<int> theIntersection;
            {
                LiteralSet::iterator apItr = startAdds.begin();
                const LiteralSet::iterator apEnd = startAdds.end();

                LiteralSet::iterator adItr = endDeletes.begin();
                const LiteralSet::iterator adEnd = endDeletes.end();

                while (apItr != apEnd && adItr != adEnd)
                {
                    const int idOne = (*apItr)->getStateID();
                    const int idTwo = (*adItr)->getStateID();
                    if (idOne < idTwo)
                    {
                        ++apItr;
                    }
                    else if (idTwo < idOne)
                    {
                        ++adItr;
                    }
                    else
                    {
                        theIntersection.insert(idOne);
                        ++apItr;
                        ++adItr;
                    }
                };
            }

            if (theIntersection.empty())
            {
                //cout << "Intersection of start adds and end deletes is empty\n";
            }

            set<int>::iterator tiItr = theIntersection.begin();
            const set<int>::iterator tiEnd = theIntersection.end();

            //确定oneShotLiterals（maybeOneShotLiteral）以及对应的actionsToEndOneShots
            for (; tiItr != tiEnd; ++tiItr)
            {
                //只有一个动作在开始添加fact然后在结尾删除
                if (effectsToActions[*tiItr].size() == 1 && refState.first.find(*tiItr) == refState.first.end())
                { // only added by one thing, i.e. this action
                    oneShotLiterals[*tiItr] = true;
                    maybeOneShotLiteral.insert(getLiteral(*tiItr));
                    list<pair<int, VAL::time_spec>> &listToUse = processedPreconditionsToActions[*tiItr];
                    list<pair<int, VAL::time_spec>>::iterator affectedItr = listToUse.begin();
                    const list<pair<int, VAL::time_spec>>::iterator affectedEnd = listToUse.end();

                    for (; affectedItr != affectedEnd; ++affectedItr)
                    {
                        if (affectedItr->second == VAL::E_AT_END)
                        {
                            actionsToEndOneShots[affectedItr->first].insert(getLiteral(*tiItr));
                            //cout << "Has " << *(getLiteral(*tiItr)) << " as a one-shot wrapped literal on which an end is dependent\n";
                        }
                    }
                }
                else
                {
                    //cout << *(getLiteral(*tiItr)) << " isn't one-shot wrapped in the action";
                    //cout << "Is added by " << effectsToActions[*tiItr].size() << " actions\n";
                    //if (refState.first.find(*tiItr) != refState.first.end()) cout << "Is in initial state\n";
                }
            }

            {
                list<Literal *> &currEffectsList = actionsToStartEffects[i];

                list<Literal *>::iterator effItr = currEffectsList.begin();
                const list<Literal *>::iterator effEnd = currEffectsList.end();

                for (; effItr != effEnd; ++effItr)
                {
                    //cout << *(*effItr) << " is maybe one shot\n";
                    maybeOneShotLiteral.insert(*effItr);
                }
            }

            {
                list<Literal *> &currEffectsList = actionsToEndEffects[i];

                list<Literal *>::iterator effItr = currEffectsList.begin();
                const list<Literal *>::iterator effEnd = currEffectsList.end();

                for (; effItr != effEnd; ++effItr)
                {
                    //cout << *(*effItr) << " is maybe one shot\n";
                    maybeOneShotLiteral.insert(*effItr);
                }
            }
        }
        else
        {
            //cout << " is > 1 shot, so can't do extra one-shot-literal-esque inference\n";
        }
    }
}

//由TIL补充preconditionsToActions集合
void RPGBuilder::oneShotInferForTILs()
{
    const int tilCount = timedInitialLiteralsVector.size();

    map<int, set<int>> &tilAdds = tilsThatAddFact;
    map<int, set<int>> &tilDels = tilsThatDeleteFact;

    //填充数据结构，tilAdds，tilDels
    for (int t = 0; t < tilCount; ++t)
    {
        FakeTILAction *const currTIL = timedInitialLiteralsVector[t];

        {
            list<Literal *> &effs = currTIL->delEffects;

            list<Literal *>::iterator effItr = effs.begin();
            const list<Literal *>::iterator effEnd = effs.end();

            for (; effItr != effEnd; ++effItr)
            {
                tilDels[(*effItr)->getStateID()].insert(t);
            }
        }

        {
            list<Literal *> &effs = currTIL->addEffects;

            list<Literal *>::iterator effItr = effs.begin();
            const list<Literal *>::iterator effEnd = effs.end();

            for (; effItr != effEnd; ++effItr)
            {
                tilAdds[(*effItr)->getStateID()].insert(t);
            }
        }
    }

    map<int, set<int>>::iterator delsItr = tilDels.begin();
    const map<int, set<int>>::iterator delsEnd = tilDels.end();

    for (; delsItr != delsEnd; ++delsItr)
    {
        //没有动作添加该fact，也没有其他TIL添加它，但是它被该TIL删除，因此这种情况可以理解为deadline
        if (tilAdds.find(delsItr->first) == tilAdds.end() && effectsToActions[delsItr->first].empty())
        {
            // if nothing adds this fact, and this TIL deletes it, the it's simple deadline fact
            // and anything that needs it must happen before now; i.e. if it's an end precondition
            // we can shove（推开） that back to being an over all too, hence allowing start--end skipping

            list<pair<int, VAL::time_spec>> &affects = preconditionsToActions[delsItr->first];

            set<int> asOverAll;

            //找到以该fact为不变量前提的动作（over_all）
            { // first pass - collect actions for which it's an invariant
                list<pair<int, VAL::time_spec>>::iterator affItr = affects.begin();
                const list<pair<int, VAL::time_spec>>::iterator affEnd = affects.end();

                for (; affItr != affEnd; ++affItr)
                {
                    if (affItr->second == VAL::E_OVER_ALL)
                        asOverAll.insert(affItr->first);
                }
            }

            //找到以该fact为结束前提的动作（at_end），但该动作不在不变量前提动作中，则作为不变量动作新加入集合preconditionsToActions
            { // second pass - for actions having it as an end precondition, but not as an invariant
                // add it as an invariant, too
                list<pair<int, VAL::time_spec>>::iterator affItr = affects.begin();
                const list<pair<int, VAL::time_spec>>::iterator affEnd = affects.end();

                for (; affItr != affEnd; ++affItr)
                {
                    if (affItr->second == VAL::E_AT_END && asOverAll.find(affItr->first) == asOverAll.end())
                    {
                        affects.insert(affItr, pair<int, VAL::time_spec>(affItr->first, VAL::E_OVER_ALL));
                    }
                }
            }
        }
    }
}

//确定oneShotLiterals、actionsToEndOneShots（开始添加，最后删除该fact），调用函数kshotInferForAction（）
void RPGBuilder::doSomeUsefulMetricRPGInference()
{
    const int opCount = instantiatedOps.size();
    const int litCount = literals.size();

    kShotFormulae = vector<KShotFormula *>(opCount, (KShotFormula *)0);
    actionsToEndOneShots = vector<LiteralSet>(opCount);

    oneShotLiterals = vector<bool>(litCount, false);

    LiteralSet initialState;
    vector<double> initialFluents;

    getInitialState(initialState, initialFluents);

    const int fluentCount = initialFluents.size();

    MinimalState refState;
    refState.insertFacts(initialState.begin(), initialState.end(), StepAndBeforeOrAfter());

    refState.secondMin = initialFluents;
    refState.secondMax = initialFluents;

    LiteralSet maybeOneShotLiteral;

    for (int i = 0; i < opCount; ++i)
    {
        if (!rogueActions[i])
        {
            //cout << "Considering whether " << *(getInstantiatedOp(i)) << " is one shot\n";
            kshotInferForAction(i, refState, maybeOneShotLiteral, initialFluents, fluentCount);
        }
    };

    set<int> revisit;

    while (!maybeOneShotLiteral.empty())
    {

        revisit.clear();

        LiteralSet::iterator litItr = maybeOneShotLiteral.begin();
        const LiteralSet::iterator litEnd = maybeOneShotLiteral.end();

        //确定oneShotLiterals、actionsToEndOneShots（开始添加，最后删除该fact）、revisit（以可疑one-shot literal为前提的动作）
        for (; litItr != litEnd; ++litItr)
        {

            const int lID = (*litItr)->getStateID();

            list<pair<int, VAL::time_spec>> &eta = effectsToActions[lID];

            if (eta.size() == 1 && refState.first.find(lID) == refState.first.end())
            { //只有一个动作添加该fact
                const int actID = eta.front().first;
                if (kShotFormulae[actID]->getLimit(refState) <= 1)
                {
                    oneShotLiterals[lID] = true;
                    //cout << "Have shown that literal " << *(*litItr) << " is one shot: only added by " << *(getInstantiatedOp(actID)) << "\n";
                    list<pair<int, VAL::time_spec>>::iterator depItr = preconditionsToActions[lID].begin();
                    const list<pair<int, VAL::time_spec>>::iterator depEnd = preconditionsToActions[lID].end();

                    for (; depItr != depEnd; ++depItr)
                    {
                        revisit.insert(depItr->first);
                    }

                    if (eta.front().second == VAL::E_AT_START)
                    {
                        list<Literal *> &ene = actionsToEndNegativeEffects[actID];
                        list<Literal *>::iterator eneItr = ene.begin();
                        const list<Literal *>::iterator eneEnd = ene.end();

                        for (; eneItr != eneEnd; ++eneItr)
                        {
                            if (*eneItr == *litItr)
                            { //one-shot文字也是某动作的删除效果
                                //cout << "Literal is one-shot wrapped\n";
                                actionsToEndOneShots[actID].insert(*eneItr); //唯一的动作先添加后删除fact
                                break;
                            }
                        }
                    }
                }
                else
                {
                    //cout << *(*litItr) << " isn't one-shot: the single achieving action, " << *(getInstantiatedOp(actID)) << ", can be applied " << kShotFormulae[actID]->getLimit(refState) << " times\n";
                }
            }
            else
            {
                //if (eta.size() > 1) cout << *(*litItr) << " isn't one shot: is added by " << eta.size() << " actions\n";
            }
        }

        maybeOneShotLiteral.clear();

        set<int>::iterator riItr = revisit.begin();
        const set<int>::iterator riEnd = revisit.end();

        for (; riItr != riEnd; ++riItr)
        {
            if (!rogueActions[*riItr])
            {
                //cout << "Revisiting " << *(getInstantiatedOp(*riItr)) << " due to one-shot literal\n";
                kshotInferForAction(*riItr, refState, maybeOneShotLiteral, initialFluents, fluentCount);
            }
        }
    }
};

bool RPGBuilder::isInteresting(const int &act, const StateFacts &facts, const map<int, set<int>> &started)
{
    const map<int, int>::iterator intrItr = uninterestingnessCriteria.find(act);
    if (intrItr == uninterestingnessCriteria.end())
        return true;
    const int criterion = intrItr->second;
    if (criterion == -1)
        return false;
    if (facts.find(criterion) != facts.end())
        return false;
    if (started.find(act) != started.end())
        return false;

    return true;
};

template <typename T>
bool removeFirst(list<T> &from, const T &toRemove)
{
    typedef typename list<T>::iterator iterator;

    iterator fItr = from.begin();
    const iterator fEnd = from.end();

    for (; fItr != fEnd; ++fItr)
    {
        if (*fItr == toRemove)
        {
            from.erase(fItr);
            return true;
        }
    }

    return false;
};

//确定动作operatorID是否需要被删除，并更新revisit（加入那些新增的无动作支持的fact）
//考虑两种情况删除该动作：1-动作前提是静态的且为false；2-动作前提非静态但是没有其他动作实现该前提
bool RPGBuilder::considerAndFilter(LiteralSet &initialState, LiteralSet &revisit, const int &operatorID)
{

    bool localDebug = (Globals::globalVerbosity & 131072);

    if (localDebug)
        cout << "Considering pruning " << *(getInstantiatedOp(operatorID)) << "\n";

    bool revisitUpdated = false;

    bool eliminate = false;

    //考虑两种情况删除该动作：1-动作前提是静态的且为false；2-动作前提非静态但是没有其他动作实现该前提
    for (int pass = 0; pass < 3; ++pass)
    {

        list<Literal *> *currList = 0;

        switch (pass)
        {
        case 0:
        {
            currList = &actionsToStartPreconditions[operatorID];
            if (localDebug)
                cout << "Start Pres:\n";
            break;
        }
        case 1:
        {
            currList = &actionsToInvariants[operatorID];
            if (localDebug)
                cout << "Invs:\n";
            break;
        }
        case 2:
        {
            currList = &actionsToEndPreconditions[operatorID];
            if (localDebug)
                cout << "End Pres:\n";
            break;
        }
        };
        list<Literal *>::iterator llItr = currList->begin();
        const list<Literal *>::iterator llEnd = currList->end();

        for (; llItr != llEnd; ++llItr)
        {
            pair<bool, bool> &currStatic = isStatic(*llItr); //是static，真值为TRUE
            if (currStatic.first)
            {
                if (!currStatic.second)
                {
#ifdef ENABLE_DEBUGGING_HOOKS
                    {
                        ostringstream s;
                        s << "Has a precondition " << *(*llItr) << " that is static and false";
                        Globals::eliminatedAction(operatorID, s.str().c_str());
                    }
#endif

                    if (localDebug)
                        cout << *(*llItr) << " [" << (*llItr)->getStateID() << "] is static and initially false\n";
                    eliminate = true;
                    break;
                }
            }
            else
            {
                if (initialState.find(*llItr) == initialState.end())
                {
                    if (effectsToActions[(*llItr)->getStateID()].empty())
                    {
#ifdef ENABLE_DEBUGGING_HOOKS
                        {
                            ostringstream s;
                            s << "Has a precondition " << *(*llItr) << " that is false in the initial state, and never added by an action\n";
                            Globals::eliminatedAction(operatorID, s.str().c_str());
                        }
#endif

                        if (localDebug)
                            cout << "Nothing adds " << *(*llItr) << " and it isn't in the initial state\n";
                        eliminate = true;
                        break;
                    }
                }
            }
            if (localDebug)
                cout << "\t" << *(*llItr) << " is okay\n";
        }
        if (eliminate)
            break;
    }

    if (eliminate)
    {
        if (localDebug || (Globals::globalVerbosity & 16))
            cout << "Pruning action " << *(getInstantiatedOp(operatorID)) << "\n";
        set<int> noLongerGet; //没有动作添加该fact

        //开始添加效果，移除effectsToActions中的该动作
        {
            list<Literal *> &currEffectsList = actionsToStartEffects[operatorID];

            list<Literal *>::iterator effItr = currEffectsList.begin();
            const list<Literal *>::iterator effEnd = currEffectsList.end();

            for (; effItr != effEnd; ++effItr)
            {
                const int effID = (*effItr)->getStateID();
                const bool rv = removeFirst(effectsToActions[effID], pair<int, VAL::time_spec>(operatorID, VAL::E_AT_START));
                if (!rv)
                {
                    std::cerr << "Fatal internal error: action start-adds " << *(*effItr) << " but it isn't in effects-to-actions\n";
                    assert(rv);
                }
                if (effectsToActions[effID].empty())
                {
                    noLongerGet.insert(effID);
                }
            }
            currEffectsList.clear();
        }

        //开始负效果，移除negativeEffectsToActions中的该动作
        {
            list<Literal *> &currEffectsList = actionsToStartNegativeEffects[operatorID];

            list<Literal *>::iterator effItr = currEffectsList.begin();
            const list<Literal *>::iterator effEnd = currEffectsList.end();

            for (; effItr != effEnd; ++effItr)
            {
                const int effID = (*effItr)->getStateID();

                const bool rv = removeFirst(negativeEffectsToActions[effID], pair<int, VAL::time_spec>(operatorID, VAL::E_AT_START));
                if (!rv)
                {
                    std::cerr << "Fatal internal error: action start-deletes " << *(*effItr) << " but it isn't in negative-effects-to-actions\n";
                    assert(rv);
                }
            }
            currEffectsList.clear();
        }

        //结束添加效果，移除effectsToActions中的该动作
        {
            list<Literal *> &currEffectsList = actionsToEndEffects[operatorID];

            list<Literal *>::iterator effItr = currEffectsList.begin();
            const list<Literal *>::iterator effEnd = currEffectsList.end();

            for (; effItr != effEnd; ++effItr)
            {
                const int effID = (*effItr)->getStateID();
                const bool rv = removeFirst(effectsToActions[effID], pair<int, VAL::time_spec>(operatorID, VAL::E_AT_END));
                if (!rv)
                {
                    std::cerr << "Fatal internal error: action end-adds " << *(*effItr) << " but it isn't in effects-to-actions\n";
                    assert(rv);
                }
                if (effectsToActions[effID].empty())
                {
                    noLongerGet.insert(effID);
                }
            }
            currEffectsList.clear();
        }

        //结束负效果，移除negativeEffectsToActions中的该动作
        {
            list<Literal *> &currEffectsList = actionsToEndNegativeEffects[operatorID];

            list<Literal *>::iterator effItr = currEffectsList.begin();
            const list<Literal *>::iterator effEnd = currEffectsList.end();

            for (; effItr != effEnd; ++effItr)
            {
                const int effID = (*effItr)->getStateID();
                const bool rv = removeFirst(negativeEffectsToActions[effID], pair<int, VAL::time_spec>(operatorID, VAL::E_AT_END));
                if (!rv)
                {
                    std::cerr << "Fatal internal error: action end-deletes " << *(*effItr) << " but it isn't in negative-effects-to-actions\n";
                    assert(rv);
                }
            }
            currEffectsList.clear();
        }

        //开始前提，移除preconditionsToActions中的该动作
        {
            list<Literal *> &currPreconditionsList = actionsToStartPreconditions[operatorID];

            list<Literal *>::iterator precItr = currPreconditionsList.begin();
            const list<Literal *>::iterator precEnd = currPreconditionsList.end();

            for (; precItr != precEnd; ++precItr)
            {

                if (isStatic(*precItr).first)
                {
                    continue;
                }

                const int precID = (*precItr)->getStateID();
                const bool rv = removeFirst(preconditionsToActions[precID], pair<int, VAL::time_spec>(operatorID, VAL::E_AT_START));
                if (!rv)
                {
                    std::cerr << "Fatal internal error: action has a start pre " << *(*precItr) << " but it isn't in preconditions-to-actions\n";
                    assert(rv);
                }
            }
            currPreconditionsList.clear();
        }

        //不变量前提，移除preconditionsToActions中的该动作
        {
            list<Literal *> &currPreconditionsList = actionsToInvariants[operatorID];

            list<Literal *>::iterator precItr = currPreconditionsList.begin();
            const list<Literal *>::iterator precEnd = currPreconditionsList.end();

            for (; precItr != precEnd; ++precItr)
            {

                if (isStatic(*precItr).first)
                {
                    continue;
                }

                const int precID = (*precItr)->getStateID();
                const bool rv = removeFirst(preconditionsToActions[precID], pair<int, VAL::time_spec>(operatorID, VAL::E_OVER_ALL));
                if (!rv)
                {
                    std::cerr << "Fatal internal error: action has an over all " << *(*precItr) << " but it isn't in preconditions-to-actions\n";
                    assert(rv);
                }
            }
            currPreconditionsList.clear();
        }

        //结束前提，移除preconditionsToActions、processedPreconditionsToActions、preconditionlessActions中的该动作
        {
            list<Literal *> &currPreconditionsList = actionsToEndPreconditions[operatorID];

            list<Literal *>::iterator precItr = currPreconditionsList.begin();
            const list<Literal *>::iterator precEnd = currPreconditionsList.end();

            for (; precItr != precEnd; ++precItr)
            {

                if (isStatic(*precItr).first)
                {
                    continue;
                }

                const int precID = (*precItr)->getStateID();
                const bool rv1 = removeFirst(preconditionsToActions[precID], pair<int, VAL::time_spec>(operatorID, VAL::E_AT_END));
                if (!rv1)
                {
                    std::cerr << "Fatal internal error: action has an end pre " << *(*precItr) << " but it isn't in preconditions-to-actions\n";
                    assert(rv1);
                }

                const bool rv2 = removeFirst(processedPreconditionsToActions[precID], pair<int, VAL::time_spec>(operatorID, VAL::E_AT_END));
                if (!rv2)
                {
                    std::cerr << "Fatal internal error: action has an end pre " << *(*precItr) << " but it isn't in processed-preconditions-to-actions\n";
                    assert(rv2);
                }
            }

            if (currPreconditionsList.empty())
            {
                const bool rv = removeFirst(preconditionlessActions, pair<int, VAL::time_spec>(operatorID, VAL::E_AT_END));
                assert(rv);
            }
            currPreconditionsList.clear();
        }

        //新增开始前提，移除preconditionlessActions、processedPreconditionsToActions中的该动作
        {
            list<Literal *> &newStartPrecs = actionsToProcessedStartPreconditions[operatorID];
            if (newStartPrecs.empty())
            {
                const bool rv = removeFirst(preconditionlessActions, pair<int, VAL::time_spec>(operatorID, VAL::E_AT_START));
                assert(rv);
            }

            list<Literal *>::iterator precItr = newStartPrecs.begin();
            const list<Literal *>::iterator precEnd = newStartPrecs.end();

            for (; precItr != precEnd; ++precItr)
            {

                if (isStatic(*precItr).first)
                {
                    continue;
                }

                const int precID = (*precItr)->getStateID();
                const bool rv = removeFirst(processedPreconditionsToActions[precID], pair<int, VAL::time_spec>(operatorID, VAL::E_AT_START));
                if (!rv)
                {
                    std::cerr << "Fatal internal error: action has a processed start pre " << *(*precItr) << " but it isn't in processed-preconditions-to-actions\n";
                    assert(rv);
                }
            }
            newStartPrecs.clear();
        }

        set<int>::iterator nlgItr = noLongerGet.begin();
        const set<int>::iterator nlgEnd = noLongerGet.end();

        //将不再有任何动作添加的fact加入revisit
        for (; nlgItr != nlgEnd; ++nlgItr)
        {
            revisit.insert(literals[*nlgItr]);
            //是不是需要加上这句？revisitUpdated = true;
        }

#ifdef ENABLE_DEBUGGING_HOOKS
        {
            Globals::eliminatedAction(operatorID, "Has one or more unreachable preconditions");
        }
#endif

        realRogueActions[operatorID] = true;
    }
    else
    {
        if (localDebug)
            cout << "Keeping it\n";
    }

    return revisitUpdated;
};

//调用函数considerAndFilter（）.后续处理revisit（查看是否有以其为新增前提条件的动作）
void RPGBuilder::postFilterUnreachableActions()
{

    const int opCount = instantiatedOps.size();

    LiteralSet initialState;
    vector<double> initialFluents;

    getInitialState(initialState, initialFluents);

    cout << "Post filtering unreachable actions: ";
    cout.flush();

    const int percentageAt = (opCount / 10);

    LiteralSet revisit;
    for (int operatorID = 0; operatorID < opCount; ++operatorID)
    {
        if (percentageAt)
        {
            if (!((operatorID + 1) % percentageAt))
            {
                cout << " [" << ((operatorID + 1) / percentageAt) << "0%]";
                cout.flush();
            }
        }
        if (!rogueActions[operatorID])
        {
            considerAndFilter(initialState, revisit, operatorID);
        }
    }

    cout << "\n";

    set<int> opRevisit; //revisit（无动作提供支撑的fact）中每个fact对应的processedPreconditionsToActions
    set<int> dpRevisit;

    {
        LiteralSet::iterator rvItr = revisit.begin();
        const LiteralSet::iterator rvEnd = revisit.end();

        for (; rvItr != rvEnd; ++rvItr)
        {
            list<pair<int, VAL::time_spec>>::iterator depItr = processedPreconditionsToActions[(*rvItr)->getStateID()].begin();
            const list<pair<int, VAL::time_spec>>::iterator depEnd = processedPreconditionsToActions[(*rvItr)->getStateID()].end();

            for (; depItr != depEnd; ++depItr)
            {
                opRevisit.insert(depItr->first);
            }
        }
    }

    //重新考虑opRevisit中的动作是否需要被删除，直至该集合为空
    set<int>::iterator rvItr = opRevisit.begin();
    set<int>::iterator rvEnd = opRevisit.end();
    while (rvItr != rvEnd)
    {
        const int operatorID = *rvItr;
        if (!rogueActions[operatorID])
        {
            if (considerAndFilter(initialState, revisit, operatorID))
            {
                opRevisit.erase(rvItr);

                {
                    LiteralSet::iterator rvItr = revisit.begin();
                    const LiteralSet::iterator rvEnd = revisit.end();

                    for (; rvItr != rvEnd; ++rvItr)
                    {
                        list<pair<int, VAL::time_spec>>::iterator depItr = processedPreconditionsToActions[(*rvItr)->getStateID()].begin();
                        const list<pair<int, VAL::time_spec>>::iterator depEnd = processedPreconditionsToActions[(*rvItr)->getStateID()].end();

                        for (; depItr != depEnd; ++depItr)
                        {
                            opRevisit.insert(depItr->first);
                        }
                    }
                }

                revisit.clear();

                rvItr = opRevisit.begin();
            }
            else
            {
                set<int>::iterator rvPrev = rvItr;
                ++rvItr;
                opRevisit.erase(rvPrev);
            }
        }
        else
        {
            set<int>::iterator rvPrev = rvItr;
            ++rvItr;
            opRevisit.erase(rvPrev);
        }
    }
};

pair<bool, bool> &RPGBuilder::isStatic(Literal *l)
{
    static pair<bool, bool> dummyPair(true, true);

    static int ID;

    ID = l->getStateID();
    if (ID < 0)
    {
        return dummyPair;
    }

    return staticLiterals[ID];
}

//没有动作效果添加或删除该fact，同时也没有TIL删除或者添加它：填充staticLiterals
void RPGBuilder::findStaticLiterals()
{
    LiteralSet initialState;
    vector<double> initialFluents;

    getInitialState(initialState, initialFluents);

    LiteralSet tilAdds;
    LiteralSet tilDels;

    list<RPGBuilder::FakeTILAction> &tilActs = RPGBuilder::getTILs();

    list<RPGBuilder::FakeTILAction>::iterator tilItr = tilActs.begin();
    const list<RPGBuilder::FakeTILAction>::iterator tilEnd = tilActs.end();

    for (; tilItr != tilEnd; ++tilItr)
    {
        tilAdds.insert(tilItr->addEffects.begin(), tilItr->addEffects.end());
        tilDels.insert(tilItr->delEffects.begin(), tilItr->delEffects.end());
    }

    const int litCount = literals.size();

    staticLiterals = vector<pair<bool, bool>>(litCount);

    for (int i = 0; i < litCount; ++i)
    {
        if (effectsToActions[i].empty() && negativeEffectsToActions[i].empty() && tilAdds.find(literals[i]) == tilAdds.end() && tilDels.find(literals[i]) == tilDels.end())
        {
            staticLiterals[i] = pair<bool, bool>(true, initialState.find(literals[i]) != initialState.end());
            /*cout << *(literals[i]) << " is static";
            if (!staticLiterals[i].second) {
            cout << ", initially false\n";
            } else {
            cout << ", initially true\n";
            }*/
            preconditionsToActions[i].clear();
            processedPreconditionsToActions[i].clear();
            negativePreconditionsToActions[i].clear();
            processedNegativePreconditionsToActions[i].clear();
        }
        else
        {
            staticLiterals[i] = pair<bool, bool>(false, false);
        }
    }
}

//toPrune:前提条件，toDec:初始不满足的前提条件数量
void RPGBuilder::pruneStaticPreconditions(list<Literal *> &toPrune, int &toDec)
{
    list<Literal *>::iterator tpItr = toPrune.begin();
    const list<Literal *>::iterator tpEnd = toPrune.end();

    while (tpItr != tpEnd)
    {
        if (isStatic(*tpItr).first)
        {
            list<Literal *>::iterator tpPrev = tpItr;
            ++tpItr;
            toPrune.erase(tpPrev);
            --toDec;
        }
        else
        {
            ++tpItr;
        }
    }
}

void RPGBuilder::pruneStaticPreconditions()
{
    const int opCount = instantiatedOps.size();
    for (int i = 0; i < opCount; ++i)
    {
        if (!rogueActions[i])
        {
            {
                int &toDec = initialUnsatisfiedStartPreconditions[i];
                pruneStaticPreconditions(actionsToStartPreconditions[i], toDec);
            }
            {
                int dummy = 0;
                pruneStaticPreconditions(actionsToStartNegativePreconditions[i], dummy);
            }
            {
                int &toDec = initialUnsatisfiedProcessedStartPreconditions[i];
                const int before = toDec;
                pruneStaticPreconditions(actionsToProcessedStartPreconditions[i], toDec);
                if (!toDec && before)
                {
                    preconditionlessActions.push_back(pair<int, VAL::time_spec>(i, VAL::E_AT_START));
                }
            }
            {
                int dummy = 0;
                pruneStaticPreconditions(actionsToProcessedStartNegativePreconditions[i], dummy);
            }

            {
                int &toDec = initialUnsatisfiedInvariants[i];
                pruneStaticPreconditions(actionsToInvariants[i], toDec);
            }
            {
                int dummy = 0;
                pruneStaticPreconditions(actionsToNegativeInvariants[i], dummy);
            }

            {
                int &toDec = initialUnsatisfiedEndPreconditions[i];
                const int before = toDec;
                pruneStaticPreconditions(actionsToEndPreconditions[i], toDec);
                if (!toDec && before)
                {
                    preconditionlessActions.push_back(pair<int, VAL::time_spec>(i, VAL::E_AT_END));
                }
            }
            {
                int dummy = 0;
                pruneStaticPreconditions(actionsToEndNegativePreconditions[i], dummy);
            }
        }
    }
};

struct NextRegress
{
    int fact;
    int fluent;
    double ts;
    set<int> forGoal;

    NextRegress(const int &a, const int &b, const double &c) : fact(a), fluent(b), ts(c){};
    NextRegress(const int &a, const int &b, const double &c, const set<int> &d) : fact(a), fluent(b), ts(c), forGoal(d){};

    bool operator<(const NextRegress &o) const
    {
        if (ts > o.ts)
            return true;
        if (ts < o.ts)
            return true; //写错了？？？

        if (fact < o.fact)
            return true;
        if (fact < o.fact)
            return false;

        if (fluent < o.fluent)
            return true;
        if (fluent > o.fluent)
            return false;

        return false;
    }
};

class RPGBuilder::CommonRegressionData
{

private:
    const int fluentCount;

    vector<map<int, double>> literalSeenForGoalAtTime;
    vector<map<int, double>> fluentSeenForGoalAtTime;
    vector<map<int, double>> opAppliedForGoalAtTime;
    vector<map<int, double>> dpAppliedForGoalAtTime;
    vector<map<int, set<VAL::time_spec>>> fluentAffectedBy;

    set<NextRegress> expansionQueue;

    vector<bool> interestingNumericEffects;

    bool haveDeterminedWhetherAllInterestingEffectsAreAtTheEnd;
    bool allInterestingEffectsAreAtTheEnd;

    //判断动作添加效果是否在动作结束时完成
    bool keepDeadlinesOnPreconditions()
    {
        if (haveDeterminedWhetherAllInterestingEffectsAreAtTheEnd)
        {
            return allInterestingEffectsAreAtTheEnd;
        }

        allInterestingEffectsAreAtTheEnd = true;
        haveDeterminedWhetherAllInterestingEffectsAreAtTheEnd = true;

        const vector<list<pair<int, VAL::time_spec>>> &presToActions = RPGBuilder::getRawPresToActions();

        const int factCount = presToActions.size();

        //有动作需要该fact作为前提，但是添加它的动作时机不是在动作结束时，则 allInterestingEffectsAreAtTheEnd = false;
        for (int f = 0; f < factCount; ++f)
        {
            if (!presToActions[f].empty())
            {
                const list<pair<int, VAL::time_spec>> &achievers = RPGBuilder::getEffectsToActions(f);

                list<pair<int, VAL::time_spec>>::const_iterator acItr = achievers.begin();
                const list<pair<int, VAL::time_spec>>::const_iterator acEnd = achievers.end();

                for (; acItr != acEnd; ++acItr)
                {
                    if (acItr->second != VAL::E_AT_END)
                    {
                        allInterestingEffectsAreAtTheEnd = false;
                        return false;
                    }
                }
            }
        }

        const int neCount = interestingNumericEffects.size();

        //若数值效果不在时结束时发生，返回false
        for (int ne = 0; ne < neCount; ++ne)
        {
            if (interestingNumericEffects[ne])
            {
                const list<pair<int, VAL::time_spec>> &achievers = rpgNumericEffectsToActions[ne];

                list<pair<int, VAL::time_spec>>::const_iterator acItr = achievers.begin();
                const list<pair<int, VAL::time_spec>>::const_iterator acEnd = achievers.end();

                for (; acItr != acEnd; ++acItr)
                {
                    if (acItr->second != VAL::E_AT_END)
                    {
                        allInterestingEffectsAreAtTheEnd = false;
                        return false;
                    }
                }
            }
        }

        return true;
    }

    //新加入的时间timeIn 与 原有时间（literalSeenForGoalAtTime）对比，若timeIn更大，更新原有结果，否则删除该时间对应的目标
    //并将新加入的forGOals等存入expansionQueue，等待进一步处理
    void requestVisitHandler(const int &literal, const int &fluent, const double &timeIn, set<int> forGoal)
    {
        const double time = (keepDeadlinesOnPreconditions() ? timeIn : DBL_MAX);

        if (time < 0.0)
            return;

        map<int, double> &bestSeen = (literal != -1 ? literalSeenForGoalAtTime[literal] : fluentSeenForGoalAtTime[fluent]);

        set<int>::iterator whittle = forGoal.begin();

        while (whittle != forGoal.end())
        {
            double &oldTime = bestSeen.insert(make_pair(*whittle, -1.0)).first->second;
            if (oldTime < time)
            {
                oldTime = time;
                ++whittle;
            }
            else
            {
                set<int>::iterator toDel = whittle++;
                forGoal.erase(toDel);
            }
        }

        if (forGoal.empty())
            return;

        NextRegress newNR(literal, fluent, time, forGoal);
        pair<set<NextRegress>::iterator, bool> ins = expansionQueue.insert(newNR);
        if (!ins.second)
        {
            const_cast<set<int> *>(&(ins.first->forGoal))->insert(forGoal.begin(), forGoal.end());
        }
    }

public:
    CommonRegressionData(const int &lc, const int &fc, const int &ac, const int &dc)
        : fluentCount(fc), literalSeenForGoalAtTime(lc), fluentSeenForGoalAtTime(fc), opAppliedForGoalAtTime(ac), dpAppliedForGoalAtTime(dc), fluentAffectedBy(fc),
          interestingNumericEffects(rpgNumericEffectsToActions.size(), false), haveDeterminedWhetherAllInterestingEffectsAreAtTheEnd(false)
{
//处理数值添加效果，判断效果是否有进一步被处理的需要
//填充interestingNumericEffects、fluentAffectedBy
{
    vector<list<pair<int, VAL::time_spec>>>::const_iterator numEffItr = rpgNumericEffectsToActions.begin();
    const vector<list<pair<int, VAL::time_spec>>>::const_iterator numEffEnd = rpgNumericEffectsToActions.end();

    for (int i = 0; numEffItr != numEffEnd; ++numEffItr, ++i)
    {
        const int affFluent = rpgNumericEffects[i].fluentIndex;

        bool proceed = false;//继续，前进

        if (NumericAnalysis::getDominanceConstraints()[affFluent] == NumericAnalysis::E_NODOMINANCE)
        {
            proceed = true;
        }
        else if (NumericAnalysis::getDominanceConstraints()[affFluent] == NumericAnalysis::E_BIGGERISBETTER)
        {
            RPGNumericEffect &currEff = rpgNumericEffects[i];

            proceed = (currEff.isAssignment || (currEff.constant > 0) || (currEff.size > 0));
        }
        else if (NumericAnalysis::getDominanceConstraints()[affFluent] == NumericAnalysis::E_SMALLERISBETTER)
        {
            RPGNumericEffect &currEff = rpgNumericEffects[i];

            proceed = (currEff.isAssignment || (currEff.constant < 0) || (currEff.size > 0));
        }

        //该数值效果有进一步需要，interestingNumericEffects[i] = true;
        //找到该数值变量对应的添加动作，fluentAffectedBy[affFluent]
        if (proceed)
        {
            interestingNumericEffects[i] = true;

            map<int, set<VAL::time_spec>> &destSet = fluentAffectedBy[affFluent];

            const list<pair<int, VAL::time_spec>> &achievers = *numEffItr;
            list<pair<int, VAL::time_spec>>::const_iterator accItr = achievers.begin();
            const list<pair<int, VAL::time_spec>>::const_iterator accEnd = achievers.end();
            for (; accItr != accEnd; ++accItr)
            {
                destSet[accItr->first].insert(accItr->second);
            }
        }
        else
        {
            //cout << "Effect " << i << " is not interesting in its own right\n";
        }
    }
}

//处理线性连续效果，填充fluentAffectedBy
{
    for (int i = 0; i < ac; ++i)
    {
        LinearEffects *const currLE = linearDiscretisation[i];
        if (!rogueActions[i] && currLE)
        {
            const int looplim = currLE->vars.size();
            for (int s = 0; s < looplim; ++s)
            {
                const int currVar = currLE->vars[s];
                fluentAffectedBy[currVar][i].insert(VAL::E_AT_START);
            }
        }
    }
}

}; // namespace Planner

void requestLiteralVisit(const int &literal, const double &time, const set<int> &forGoal)
{
    requestVisitHandler(literal, -1, time, forGoal);
};

//更新时间和目标
void requestLiteralVisit(const int &literal, const double &time, const int &forGoal)
{
    set<int> tmp;
    tmp.insert(forGoal);
    requestLiteralVisit(literal, time, tmp);
};

void requestFluentVisit(const int &fluent, const double &time, const set<int> &forGoal)
{
    requestVisitHandler(-1, fluent, time, forGoal);
};

void requestFluentVisit(const int &fluent, const double &time, const int &forGoal)
{
    set<int> tmp;
    tmp.insert(forGoal);
    requestFluentVisit(fluent, time, tmp);
};

typedef set<NextRegress>::iterator iterator;

iterator begin()
{
    return expansionQueue.begin();
};
const iterator end()
{
    return expansionQueue.end();
};
void erase(const iterator &i)
{
    expansionQueue.erase(i);
};

bool empty() const
{
    return expansionQueue.empty();
};

//返回动作
map<int, set<VAL::time_spec>> &relevantToFluent(const int &currVar)
{
    return fluentAffectedBy[currVar];
}

//该动作需要实现NextRegress中的fact，若是，更新时间和可能的新目标
void regressThroughAction(const int &actID, const VAL::time_spec &ts, const NextRegress &inAidOf)
{

    static const bool debug = false;

    //如果动作是TIL，不能回溯
    if (ts == VAL::E_AT)
        return;

    //如果是开始动作，且其发生时间在fact实现之后，出错
    if (ts == VAL::E_AT_START)
    {
        if (TemporalAnalysis::getActionTSBounds()[actID][0].first > inAidOf.ts)
            return;
    }
    else
    {//如果是结束动作，且其发生时间在fact实现之后，出错
        if (TemporalAnalysis::getActionTSBounds()[actID][1].first > inAidOf.ts)
            return;
    }

    //（开始动作最早开始时间，inAidOf.ts）或者（结束动作最晚结束时间，inAidOf.ts）按时间顺序排列
    set<int> forGoal(inAidOf.forGoal);

    {
        double atTime = inAidOf.ts;
        if (ts == VAL::E_AT_END && atTime != DBL_MAX)
            atTime -= getOpMinDuration(actID, -1);

        pair<double, double> &tsBounds = TemporalAnalysis::getActionTSBounds()[actID][0];

        if (atTime < tsBounds.first)
            return;
        if (atTime > tsBounds.second)
            atTime = tsBounds.second;

        set<int>::iterator fgItr = forGoal.begin();
        const set<int>::iterator fgEnd = forGoal.end();

        while (fgItr != fgEnd)
        {
            double &insAt = opAppliedForGoalAtTime[actID].insert(make_pair(*fgItr, -DBL_MAX)).first->second;
            if (insAt >= atTime)
            {
                set<int>::iterator fgDel = fgItr++;
                forGoal.erase(fgDel);
            }
            else
            {
                insAt = atTime;
                ++fgItr;
            }
        }
    }

    if (forGoal.empty())
        return;

    for (int pass = 0; pass < 3; ++pass)
    {
        list<Literal *> *currList = 0;
        list<int> *currNumList = 0;
        double atTime = inAidOf.ts;
        switch (pass)
        {
        case 0:
        {
            currList = &actionsToProcessedStartPreconditions[actID];
            currNumList = &actionsToRPGNumericStartPreconditions[actID];
            if (ts == VAL::E_AT_START)
            {
                if (atTime != DBL_MAX)
                    atTime -= EPSILON;
            }
            else
            {
                if (atTime != DBL_MAX)
                {
                    if (debug)
                        cout << "Duration of " << *(getInstantiatedOp(actID)) << " = " << getOpMinDuration(actID, -1) << "\n";
                    atTime -= getOpMinDuration(actID, -1);
                }
            }
            if (debug)
            {
                cout << "Adding pres for start of " << *(getInstantiatedOp(actID)) << " at time ";
                if (atTime == DBL_MAX)
                {
                    cout << "infinity\n";
                }
                else
                {
                    cout << atTime << "\n";
                }
            }
            break;
        }
        case 1:
        {
            currList = 0;
            currNumList = &actionsToRPGNumericInvariants[actID];
            /*if (ts == VAL::E_AT_START) {
                    if (atTime != DBL_MAX) atTime += getOpMaxDuration(actID, -1);
                } else {
                    if (atTime != DBL_MAX) atTime -= EPSILON;
                }*/

            if (ts == VAL::E_AT_START)
            {
                if (debug)
                {
                    cout << "Adding pres for invariants from start of " << *(getInstantiatedOp(actID)) << " at time ";
                    if (atTime == DBL_MAX)
                    {
                        cout << "infinity\n";
                    }
                    else
                    {
                        cout << atTime << "\n";
                    }
                }
            }
            else
            {
                if (atTime != DBL_MAX)
                {
                    atTime -= getOpMinDuration(actID, -1) + EPSILON;
                }
                if (debug)
                {
                    cout << "Adding pres for invariants from end of " << *(getInstantiatedOp(actID));
                    cout << ", duration = " << getOpMinDuration(actID, -1);
                    cout << " at time ";
                    if (atTime == DBL_MAX)
                    {
                        cout << "infinity\n";
                    }
                    else
                    {
                        cout << atTime << "\n";
                    }
                }
            }

            break;
        }
        case 2:
        {
            currList = &actionsToEndPreconditions[actID];
            currNumList = &actionsToRPGNumericEndPreconditions[actID];
            if (ts == VAL::E_AT_START)
            {
                if (atTime != DBL_MAX)
                    atTime += getOpMaxDuration(actID, -1);
            }
            else
            {
                if (atTime != DBL_MAX)
                    atTime -= EPSILON;
            }
            if (debug)
            {
                cout << "Adding pres for end of " << *(getInstantiatedOp(actID)) << " at time ";
                if (atTime == DBL_MAX)
                {
                    cout << "infinity\n";
                }
                else
                {
                    cout << atTime << "\n";
                }
            }
            break;
        }
        };
        if (currList)
        {
            list<Literal *>::iterator preItr = currList->begin();
            const list<Literal *>::iterator preEnd = currList->end();

            for (; preItr != preEnd; ++preItr)
            {
                const int litID = (*preItr)->getStateID();
                requestLiteralVisit(litID, atTime, forGoal);
            }
        }
        list<int>::iterator numPreItr = currNumList->begin();
        const list<int>::iterator numPreEnd = currNumList->end();

        for (; numPreItr != numPreEnd; ++numPreItr)
        {
            int fID = rpgNumericPreconditions[*numPreItr].LHSVariable;
            if (fID < 0)
            {
            }
            else if (fID < fluentCount)
            {
                requestFluentVisit(fID, atTime, forGoal);
            }
            else if (fID < (2 * fluentCount))
            {
                fID -= fluentCount;
                assert(fID < fluentCount);
                requestFluentVisit(fID, atTime, forGoal);
            }
            else
            {
                ArtificialVariable &currAV = getArtificialVariable(fID);

                const int size = currAV.size;
                for (int i = 0; i < size; ++i)
                {
                    int afID = currAV.fluents[i];

                    if (afID >= fluentCount)
                        afID -= fluentCount;
                    requestFluentVisit(afID, atTime, forGoal);
                }
            }
        }
    }
}

/*  void regressThroughDerivationRule(const int & ruleID, const NextRegress & inAidOf) {

        set<int> forGoal(inAidOf.forGoal);

        {
        const double atTime = inAidOf.ts;

        if (atTime < 0.0) return;

        set<int>::iterator fgItr = forGoal.begin();
        const set<int>::iterator fgEnd = forGoal.end();

        while (fgItr != fgEnd) {
        double & insAt = dpAppliedForGoalAtTime[ruleID].insert(make_pair(*fgItr,-DBL_MAX)).first->second;
        if (insAt >= atTime) {
        set<int>::iterator fgDel = fgItr++;
        forGoal.erase(fgDel);
    } else {
        insAt = atTime;
        ++fgItr;
    }
    }
    }

        if (forGoal.empty()) return;

        {
        list<int> & currList = DerivedPredicatesEngine::getPreLiterals(ruleID);

        list<int>::iterator preItr = currList.begin();
        const list<int>::iterator preEnd = currList.end();

        for (; preItr != preEnd; ++preItr) {
        const int litID = (*preItr);
        requestLiteralVisit(litID, inAidOf.ts, forGoal);
    }
    }
        {
        list<int> * currList = &(DerivedPredicatesEngine::getPreNums(ruleID));
        list<int>::iterator preItr = currList->begin();
        const list<int>::iterator preEnd = currList->end();

        for (; preItr != preEnd; ++preItr) {
        int fID = rpgNumericPreconditions[*preItr].LHSVariable;
        if (fID < 0) {

    } else if (fID < fluentCount) {
        assert(fID < fluentCount);
        requestFluentVisit(fID, inAidOf.ts, forGoal);
    } else if (fID < (2 * fluentCount)) {
        fID -= fluentCount;
        assert(fID < fluentCount);
        requestFluentVisit(fID, inAidOf.ts, inAidOf.forGoal);
    } else {
        ArtificialVariable & currAV = getArtificialVariable(fID);

        const int size = currAV.size;
        for (int i = 0; i < size; ++i) {
        int afID = currAV.fluents[i];

        if (afID >= fluentCount) afID -= fluentCount;

        assert(afID < fluentCount);
        requestFluentVisit(afID, inAidOf.ts, forGoal);
    }
    }
    }
    }
    }
    */
bool opNeverApplied(const int &i) const
{
    return (opAppliedForGoalAtTime[i].empty());
};

//返回应用的动作中最晚的时间
double latestUsefulPoint(const int &op)
{
    double toReturn = 0.0;
    map<int, double>::iterator fgItr = opAppliedForGoalAtTime[op].begin();
    const map<int, double>::iterator fgEnd = opAppliedForGoalAtTime[op].end();

    for (; fgItr != fgEnd; ++fgItr)
    {
        const double &currT = fgItr->second;
        if (currT == DBL_MAX)
            return DBL_MAX;
        if (currT > toReturn)
            toReturn = currT;
    }

    return toReturn;
}
}
;

//因其他原因才被迫删除的动作处理，realRogueActions[operatorID] = true;
void RPGBuilder::pruneIrrelevant(const int &operatorID)
{

#ifdef ENABLE_DEBUGGING_HOOKS
    Globals::eliminatedAction(operatorID, "No reason known - has been passed to pruneIrrelevant");
#endif

    realRogueActions[operatorID] = true;

    //删除动作的开始效果以及与该效果相关的动作（effectsToActions）
    {
        list<Literal *> &currEffectsList = actionsToStartEffects[operatorID];

        list<Literal *>::iterator effItr = currEffectsList.begin();
        const list<Literal *>::iterator effEnd = currEffectsList.end();

        for (; effItr != effEnd; ++effItr)
        {
            const int effID = (*effItr)->getStateID();
            effectsToActions[effID].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_START));
        }
        currEffectsList.clear();
    }

    //删除动作的开始负效果以及与该效果相关的动作（negativeEffectsToActions）
    {
        list<Literal *> &currEffectsList = actionsToStartNegativeEffects[operatorID];

        list<Literal *>::iterator effItr = currEffectsList.begin();
        const list<Literal *>::iterator effEnd = currEffectsList.end();

        for (; effItr != effEnd; ++effItr)
        {
            const int effID = (*effItr)->getStateID();
            negativeEffectsToActions[effID].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_START));
        }
        currEffectsList.clear();
    }

    //删除动作的结束效果以及与该效果相关的动作（EffectsToActions）
    {
        list<Literal *> &currEffectsList = actionsToEndEffects[operatorID];

        list<Literal *>::iterator effItr = currEffectsList.begin();
        const list<Literal *>::iterator effEnd = currEffectsList.end();

        for (; effItr != effEnd; ++effItr)
        {
            const int effID = (*effItr)->getStateID();
            effectsToActions[effID].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_END));
        }
        currEffectsList.clear();
    }

    //删除动作的结束负效果以及与该效果相关的动作（negativeEffectsToActions）
    {
        list<Literal *> &currEffectsList = actionsToEndNegativeEffects[operatorID];

        list<Literal *>::iterator effItr = currEffectsList.begin();
        const list<Literal *>::iterator effEnd = currEffectsList.end();

        for (; effItr != effEnd; ++effItr)
        {
            const int effID = (*effItr)->getStateID();
            negativeEffectsToActions[effID].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_END));
        }
        currEffectsList.clear();
    }

    //删除动作的开始前提以及与该前提相关的动作（preconditionsToActions）
    {
        list<Literal *> &currPreconditionsList = actionsToStartPreconditions[operatorID];

        list<Literal *>::iterator precItr = currPreconditionsList.begin();
        const list<Literal *>::iterator precEnd = currPreconditionsList.end();

        for (; precItr != precEnd; ++precItr)
        {
            const int precID = (*precItr)->getStateID();
            preconditionsToActions[precID].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_START));
        }
        currPreconditionsList.clear();
    }

    //删除动作的不变量以及与该前提相关的动作（preconditionsToActions）
    {
        list<Literal *> &currPreconditionsList = actionsToInvariants[operatorID];

        list<Literal *>::iterator precItr = currPreconditionsList.begin();
        const list<Literal *>::iterator precEnd = currPreconditionsList.end();

        for (; precItr != precEnd; ++precItr)
        {
            const int precID = (*precItr)->getStateID();
            preconditionsToActions[precID].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_OVER_ALL));
        }
        currPreconditionsList.clear();
    }

    //删除动作的结束前提以及与该前提相关的动作（preconditionsToActions、processedPreconditionsToActions）
    //（preconditionlessActions、onlyNumericPreconditionActions）
    {
        list<Literal *> &currPreconditionsList = actionsToEndPreconditions[operatorID];

        list<Literal *>::iterator precItr = currPreconditionsList.begin();
        const list<Literal *>::iterator precEnd = currPreconditionsList.end();

        for (; precItr != precEnd; ++precItr)
        {
            const int precID = (*precItr)->getStateID();
            preconditionsToActions[precID].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_END));
            processedPreconditionsToActions[precID].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_END));
        }

        if (currPreconditionsList.empty())
        {
            preconditionlessActions.remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_END));
            onlyNumericPreconditionActions.remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_END));
        }
        currPreconditionsList.clear();
    }

    //删除动作的处理开始前提（由不变量推断出的新增前提）以及与该前提相关的动作（processedPreconditionsToActions）
    //（preconditionlessActions、onlyNumericPreconditionActions）
    {
        list<Literal *> &newStartPrecs = actionsToProcessedStartPreconditions[operatorID];
        if (newStartPrecs.empty())
        {
            preconditionlessActions.remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_START));
            onlyNumericPreconditionActions.remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_START));
        }

        list<Literal *>::iterator precItr = newStartPrecs.begin();
        const list<Literal *>::iterator precEnd = newStartPrecs.end();

        for (; precItr != precEnd; ++precItr)
        {
            const int precID = (*precItr)->getStateID();
            processedPreconditionsToActions[precID].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_START));
        }

        newStartPrecs.clear();
    }

    //删除动作的RPG数值前提以及相关动作（rpgNumericPreconditionsToActions）
    {
        list<int> &currPreconditionsList = actionsToRPGNumericStartPreconditions[operatorID];

        list<int>::iterator precItr = currPreconditionsList.begin();
        const list<int>::iterator precEnd = currPreconditionsList.end();
        for (; precItr != precEnd; ++precItr)
        {
            const int precID = *precItr;
            rpgNumericPreconditionsToActions[precID].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_START));
        }
        currPreconditionsList.clear();
    }

    //删除动作的RPG数值不变量以及相关动作（rpgNumericPreconditionsToActions）
    {
        list<int> &currPreconditionsList = actionsToRPGNumericInvariants[operatorID];

        list<int>::iterator precItr = currPreconditionsList.begin();
        const list<int>::iterator precEnd = currPreconditionsList.end();
        for (; precItr != precEnd; ++precItr)
        {
            const int precID = *precItr;
            rpgNumericPreconditionsToActions[precID].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_OVER_ALL));
        }
        currPreconditionsList.clear();
    }

    //删除动作的新增开始RPG数值条件以及相关动作（processedRPGNumericPreconditionsToActions）
    {
        list<int> &currPreconditionsList = actionsToProcessedStartRPGNumericPreconditions[operatorID];

        list<int>::iterator precItr = currPreconditionsList.begin();
        const list<int>::iterator precEnd = currPreconditionsList.end();
        for (; precItr != precEnd; ++precItr)
        {
            const int precID = *precItr;
            processedRPGNumericPreconditionsToActions[precID].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_START));
        }

        currPreconditionsList.clear();
    }

    //删除动作的RPG数值结束前提以及相关动作（rpgNumericPreconditionsToActions、processedRPGNumericPreconditionsToActions）
    {
        list<int> &currPreconditionsList = actionsToRPGNumericEndPreconditions[operatorID];

        list<int>::iterator precItr = currPreconditionsList.begin();
        const list<int>::iterator precEnd = currPreconditionsList.end();
        for (; precItr != precEnd; ++precItr)
        {
            const int precID = *precItr;
            rpgNumericPreconditionsToActions[precID].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_END));
            processedRPGNumericPreconditionsToActions[precID].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_END));
        }

        currPreconditionsList.clear();
    }

    //删除动作的开始数值效果以及相关动作（rpgNumericEffectsToActions）
    {
        list<int> &currEffList = getStartEffNumerics()[operatorID];

        list<int>::iterator effItr = currEffList.begin();
        const list<int>::iterator effEnd = currEffList.end();
        for (; effItr != effEnd; ++effItr)
        {
            rpgNumericEffectsToActions[*effItr].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_START));
        }

        currEffList.clear();
    }

    //删除动作的结束数值效果以及相关动作（rpgNumericEffectsToActions）
    {
        list<int> &currEffList = getEndEffNumerics()[operatorID];

        list<int>::iterator effItr = currEffList.begin();
        const list<int>::iterator effEnd = currEffList.end();
        for (; effItr != effEnd; ++effItr)
        {
            rpgNumericEffectsToActions[*effItr].remove(pair<int, VAL::time_spec>(operatorID, VAL::E_AT_END));
        }

        currEffList.clear();
    }

    //删除动作的线性连续效果
    delete linearDiscretisation[operatorID];
    linearDiscretisation[operatorID] = 0;
}

//过滤那些动作效果与目标实现无关的动作
void RPGBuilder::postFilterIrrelevantActions()
{
    const int opCount = instantiatedOps.size();
    const int dpCount = 0; // DerivedPredicatesEngine::getRuleCount();
    const int litCount = literals.size();
    const int fluentCount = pnes.size();

    CommonRegressionData data(litCount, fluentCount, opCount, dpCount);

    //  interestingActionUntilWeHaveLiteral = vector<set<int> >(opCount);
    //  interestingActionUntilWeHaveNumeric = vector<set<int> >(opCount);

    //更新集合中的时间和逻辑目标
    {
        list<Literal *>::iterator afItr = literalGoals.begin();
        const list<Literal *>::iterator afEnd = literalGoals.end();

        list<double>::iterator gdItr = literalGoalDeadlines.begin();

        for (int i = 0; afItr != afEnd; ++afItr, ++gdItr, ++i)
        {
            data.requestLiteralVisit((*afItr)->getStateID(), *gdItr, i);
        }
    }

    //更新集合中的时间和数值目标
    {
        list<pair<int, int>>::iterator afItr = numericRPGGoals.begin();
        const list<pair<int, int>>::iterator afEnd = numericRPGGoals.end();

        for (int i = -1; afItr != afEnd; ++afItr, --i)
        {
            for (int pass = 0; pass < 2; ++pass)
            {
                const int local = (pass ? afItr->second : afItr->first);
                if (local != -1)
                {
                    int fID = rpgNumericPreconditions[local].LHSVariable;
                    if (fID < 0)
                    {
                    }
                    else if (fID < fluentCount)
                    {
                        data.requestFluentVisit(fID, DBL_MAX, i);
                    }
                    else if (fID < (2 * fluentCount))
                    {
                        fID -= fluentCount;
                        assert(fID < fluentCount);
                        data.requestFluentVisit(fID, DBL_MAX, i);
                    }
                    else
                    {
                        ArtificialVariable &currAV = getArtificialVariable(fID);
                        const int size = currAV.size;
                        for (int j = 0; j < size; ++j)
                        {
                            int afID = currAV.fluents[j];

                            if (afID >= fluentCount)
                                afID -= fluentCount;

                            assert(afID < fluentCount);
                            data.requestFluentVisit(afID, DBL_MAX, i);
                        }
                    }
                }
            }
        }
    }

    //迭代更新集合中的目标时间和新目标，直至集合为空
    while (!data.empty())
    {
        const CommonRegressionData::iterator dItr = data.begin();//set<NextRegress> expansionQueue;

        NextRegress currPair = *dItr;

        data.erase(dItr);

        if (currPair.fact != -1)
        {//在currPair.ts（时间）确定实现currPair.fact的动作
            const int currLit = currPair.fact;

            if (Globals::globalVerbosity & 16)
            {
                cout << COLOUR_light_blue << "Finding achievers for " << *(getLiteral(currLit)) << " at time ";
                if (currPair.ts == DBL_MAX)
                {
                    cout << "infinity\n";
                }
                else
                {
                    cout << currPair.ts << "\n";
                }
                cout << COLOUR_default;
            }

            list<pair<int, VAL::time_spec>> &achievers = effectsToActions[currLit];
            //set<int> & ruleAchievers = DerivedPredicatesEngine::rulesWillDerive(currLit);

            list<pair<int, VAL::time_spec>>::iterator accItr = achievers.begin();
            const list<pair<int, VAL::time_spec>>::iterator accEnd = achievers.end();

            for (; accItr != accEnd; ++accItr)
            {
                data.regressThroughAction(accItr->first, accItr->second, currPair);
            }
            /*
                        set<int>::iterator raItr = ruleAchievers.begin();
                        const set<int>::iterator raEnd = ruleAchievers.end();

                        for (; raItr != raEnd; ++raItr) {
                        data.regressThroughDerivationRule(*raItr, currPair);
                    }
            */
        }
        else if (currPair.fluent != -1)
        {
            const int currVar = currPair.fluent;

            map<int, set<VAL::time_spec>>::iterator faItr = data.relevantToFluent(currVar).begin();
            const map<int, set<VAL::time_spec>>::iterator faEnd = data.relevantToFluent(currVar).end();

            for (; faItr != faEnd; ++faItr)
            {
                set<VAL::time_spec>::iterator tsItr = faItr->second.begin();
                const set<VAL::time_spec>::iterator tsEnd = faItr->second.end();

                for (; tsItr != tsEnd; ++tsItr)
                {
                    data.regressThroughAction(faItr->first, *tsItr, currPair);
                }
            }
        }
        else
        {
            cout << "For some reason, the goal of achieving precisely nothing has worked its way onto the regression filter stack\n";
            assert(false);
        }
    }

    //过滤没有用到的动作
    for (int i = 0; i < opCount; ++i)
    {
        if (!rogueActions[i] && data.opNeverApplied(i))
        {

        #ifdef ENABLE_DEBUGGING_HOOKS
            {
                Globals::eliminatedAction(i, "Can never be usefully applied on any path to the goal");
            }
        #endif

            if (Globals::globalVerbosity & 16)
                cout << *(instantiatedOps[i]) << " is irrelevant\n";
            pruneIrrelevant(i);
        }
    }

    //更新剩余动作的时间上下界
    for (int i = 0; i < opCount; ++i)
    {
        if (!rogueActions[i])
        {
            const double startBound = data.latestUsefulPoint(i);
            const double endBound = startBound + getOpMaxDuration(i, -1);

            double &oldStart = TemporalAnalysis::getActionTSBounds()[i][0].second;
            double &oldEnd = TemporalAnalysis::getActionTSBounds()[i][1].second;

            if (oldStart > startBound)
            {
                //              cout << *getInstantiatedOp(i) << " is interesting no later than " << startBound << "\n";
                oldStart = startBound;
            }
            if (oldEnd > endBound)
            {
                oldEnd = endBound;
            }
        }
    }

    /*for (int i = 0; i < opCount; ++i) {
    if (!rogueActions[i]) {
    interestingActionUntilWeHaveLiteral[i] = opApplied[i];
    {
    set<int>::iterator ggItr = interestingActionUntilWeHaveLiteral[i].begin();
    const set<int>::iterator ggEnd = interestingActionUntilWeHaveLiteral[i].end();
    bool killAfter = false;
    while (ggItr != ggEnd) {
    if (*ggItr < 0) {
    interestingActionUntilWeHaveNumeric[i].insert(-1 - *ggItr);
    set<int>::iterator ggPrev = ggItr;
    ++ggItr;
    interestingActionUntilWeHaveLiteral[i].erase(ggPrev);
    // sort this out later
    killAfter = true;
    } else {
    assert(*ggItr < (int) goalLiteralsSafe.size());
    if (!goalLiteralsSafe[*ggItr]) {
    killAfter = true;
    }
    ++ggItr;
    }
    }
    if (killAfter) {
    interestingActionUntilWeHaveLiteral[i].clear();
    interestingActionUntilWeHaveNumeric[i].clear();
    } else if (false) {
    cout << *(instantiatedOps[i]) << " is uninteresting once goals";
    ggItr = interestingActionUntilWeHaveLiteral[i].begin();
    for (; ggItr != ggEnd; ++ggItr) cout << " " << *ggItr;
    cout << " are achieved\n";

    }
    }

    {
    set<int>::iterator ggItr = interestingActionUntilWeHaveNumeric[i].begin();
    const set<int>::iterator ggEnd = interestingActionUntilWeHaveNumeric[i].end();
    bool killAfter = false;
    while (ggItr != ggEnd) {
    if (!goalNumericsSafe[*ggItr]) {
    killAfter = true;
    break;
    }
    ++ggItr;

    }
    if (killAfter) {
    interestingActionUntilWeHaveLiteral[i].clear();
    interestingActionUntilWeHaveNumeric[i].clear();
    }
    }
    }
    }*/
};

//无论删除还是添加，只要有一个动作需要其作为前提，就把他加入optimisationTimedInitialLiterals
//最终填充allTimedInitialLiteralsVector
void RPGBuilder::separateOptimisationTILs()
{
    list<FakeTILAction>::iterator tilItr = timedInitialLiterals.begin();
    const list<FakeTILAction>::iterator tilEnd = timedInitialLiterals.end();

    //确定optimisationTimedInitialLiterals
    for (int ti = 0; tilItr != tilEnd; ++ti)
    {

        FakeTILAction metricParts(tilItr->duration, LiteralSet(), LiteralSet()); //发生时间，添加效果，删除效果

        bool metricOnly = true;
        bool anyMetric = false;

        //添加效果处理，若TIL的添加fact不被其他动作作为前提需要：移除以他为效果的动作、删除该添加效果、anyMetric = true；否则metricOnly = false;
        {
            list<Literal *> &effList = tilItr->addEffects;

            list<Literal *>::iterator elItr = effList.begin();
            const list<Literal *>::iterator elEnd = effList.end();

            while (elItr != elEnd)
            {
                if (!preconditionsToActions[(*elItr)->getStateID()].empty() || !negativePreconditionsToActions[(*elItr)->getStateID()].empty())
                { //有动作需要该fact作为前提
                    metricOnly = false;
                    ++elItr;
                }
                else
                {
                    effectsToActions[(*elItr)->getStateID()].remove(make_pair(ti, VAL::E_AT));
                    metricParts.addEffects.push_back(*elItr);
                    const list<Literal *>::iterator elDel = elItr++;
                    effList.erase(elDel);
                    anyMetric = true;
                }
            }
        }

        //删除效果处理，若TIL的删除fact不被其他动作作为前提需要：移除以他为效果的动作、删除该添加效果、anyMetric = true；否则metricOnly = false;
        {
            list<Literal *> &effList = tilItr->delEffects;

            list<Literal *>::iterator elItr = effList.begin();
            const list<Literal *>::iterator elEnd = effList.end();

            while (elItr != elEnd)
            {
                if (!preconditionsToActions[(*elItr)->getStateID()].empty() || !negativePreconditionsToActions[(*elItr)->getStateID()].empty())
                {

                    metricOnly = false;
                    ++elItr;
                }
                else
                {
                    negativeEffectsToActions[(*elItr)->getStateID()].remove(make_pair(ti, VAL::E_AT));
                    metricParts.delEffects.push_back(*elItr);
                    const list<Literal *>::iterator elDel = elItr++;
                    effList.erase(elDel);
                    anyMetric = true;
                }
            }
        }

        //无论删除还是添加，只要有一个动作需要其作为前提，就把他加入optimisationTimedInitialLiterals
        if (metricOnly)
        {
            optimisationTimedInitialLiterals.push_back(*tilItr);
            const list<FakeTILAction>::iterator tilDel = tilItr++;
            timedInitialLiterals.erase(tilDel);
        }
        else
        {
            if (anyMetric)
            {
                optimisationTimedInitialLiterals.push_back(metricParts);
            }
            ++tilItr;
        }
    }

    //填充timedInitialLiteralsVector，确定tilLimit = timedInitialLiterals.size() - 1
    {
        const int tilCount = timedInitialLiterals.size();
        timedInitialLiteralsVector.resize(tilCount);

        list<FakeTILAction>::iterator tilcItr = timedInitialLiterals.begin();
        const list<FakeTILAction>::iterator tilcEnd = timedInitialLiterals.end();

        for (int i = 0; tilcItr != tilcEnd; ++tilcItr, ++i)
        {
            timedInitialLiteralsVector[i] = &(*tilcItr);
        }

        FFEvent::tilLimit = ActionSegment::tilLimit = tilCount - 1;
    }

    //填充optimisationTimedInitialLiteralsVector
    {
        const int tilCount = optimisationTimedInitialLiterals.size();
        optimisationTimedInitialLiteralsVector.resize(tilCount);

        list<FakeTILAction>::iterator tilcItr = optimisationTimedInitialLiterals.begin();
        const list<FakeTILAction>::iterator tilcEnd = optimisationTimedInitialLiterals.end();

        for (int i = 0; tilcItr != tilcEnd; ++tilcItr, ++i)
        {
            optimisationTimedInitialLiteralsVector[i] = &(*tilcItr);
        }
    }

    //填充allTimedInitialLiteralsVector
    {
        const int tilCount = timedInitialLiteralsVector.size();
        const int optTilCount = optimisationTimedInitialLiteralsVector.size();

        allTimedInitialLiteralsVector.resize(tilCount + optTilCount); //按照时间先后顺序排列所有TIL

        int ti = 0;
        int oti = 0;
        int cti = 0;
        while (ti < tilCount && oti < optTilCount)
        {
            if (timedInitialLiteralsVector[ti]->duration < optimisationTimedInitialLiteralsVector[oti]->duration)
            {
                allTimedInitialLiteralsVector[cti] = timedInitialLiteralsVector[ti];
                ++ti;
            }
            else
            {
                allTimedInitialLiteralsVector[cti] = optimisationTimedInitialLiteralsVector[oti];
                ++oti;
            }
            ++cti;
        }
        for (; ti < tilCount; ++ti, ++cti)
        {
            allTimedInitialLiteralsVector[cti] = timedInitialLiteralsVector[ti];
        }
        for (; oti < optTilCount; ++oti, ++cti)
        {
            allTimedInitialLiteralsVector[cti] = optimisationTimedInitialLiteralsVector[oti];
        }
    }
}

LiteralSet RPGBuilder::factsWithOnlyPointlessEffects;
map<int, map<Literal *, RPGBuilder::pointless_effect, LiteralLT>> RPGBuilder::pointlessStartEffects; //<动作ID，map<无意义的fact，无意义效果阶段> >
map<int, map<Literal *, RPGBuilder::pointless_effect, LiteralLT>> RPGBuilder::pointlessEndEffects;
map<int, map<Literal *, RPGBuilder::pointless_effect, LiteralLT>> RPGBuilder::pointlessTILEffects;

//fact不被当成前提需要即被认为是无意义的
void RPGBuilder::removePointlessEffects()
{
    LiteralSet newlyPointlessEffects;

    const int literalCount = preconditionsToActions.size();

    //对于那些不被任何动作需要作为前提的literal，加入factsWithOnlyPointlessEffects、newlyPointlessEffects
    {
        LiteralSet::iterator insItr = factsWithOnlyPointlessEffects.begin();
        LiteralSet::iterator ins2Itr = newlyPointlessEffects.begin();
        for (int lit = 0; lit < literalCount; ++lit)
        {
            if (preconditionsToActions[lit].empty() && negativePreconditionsToActions[lit].empty())
            {
                insItr = factsWithOnlyPointlessEffects.insert(insItr, literals[lit]);
                ins2Itr = newlyPointlessEffects.insert(ins2Itr, literals[lit]);
            }
        }
    }

    //对上面处理的结果，排除目标集合中的文字
    {
        list<Literal *>::const_iterator lgItr = literalGoals.begin();
        const list<Literal *>::const_iterator lgEnd = literalGoals.end();

        for (; lgItr != lgEnd; ++lgItr)
        {
            factsWithOnlyPointlessEffects.erase(*lgItr);
            newlyPointlessEffects.erase(*lgItr);
        }
    }

    if (factsWithOnlyPointlessEffects.empty())
        return;

    LiteralSet literalGoalSet;

    literalGoalSet.insert(literalGoals.begin(), literalGoals.end());

    map<int, bool> actionsThatDeleteThisFactNeedIt; //<删除无意义fact后的动作的结束添加效果，该动作的删除效果被某个动作的前提需要>

    while (!newlyPointlessEffects.empty())
    {

        LiteralSet previousPointlessEffects;
        previousPointlessEffects.swap(newlyPointlessEffects);

        set<int> actionsToCheckIfPointlessAfterStrippingEffects;

        LiteralSet::const_iterator fItr = previousPointlessEffects.begin();
        const LiteralSet::const_iterator fEnd = previousPointlessEffects.end();

        //填充数据结构pointlessStartEffects、pointlessEndEffects、pointlessTILEffects
        //并相应的删除startEffs、endEffs、timedInitialLiteralsVector中的无意义fact相关的东西
        //并需要检查fact删除后的动作是否还有意义，即actionsToCheckIfPointlessAfterStrippingEffects
        for (; fItr != fEnd; ++fItr)
        {
            //enum pointless_effect { PE_ADDED=1, PE_DELETED=2, PE_DELETED_THEN_ADDED=3 };
            for (pointless_effect eff = PE_ADDED; eff < PE_DELETED_THEN_ADDED; eff = (eff == PE_ADDED ? PE_DELETED : PE_DELETED_THEN_ADDED))
            {
                list<pair<int, VAL::time_spec>> &eta = (eff == PE_DELETED ? negativeEffectsToActions[(*fItr)->getStateID()]
                                                                          : effectsToActions[(*fItr)->getStateID()]);

                vector<list<Literal *>> &startEffs = (eff == PE_DELETED ? actionsToStartNegativeEffects
                                                                        : actionsToStartEffects);

                vector<list<Literal *>> &endEffs = (eff == PE_DELETED ? actionsToEndNegativeEffects
                                                                      : actionsToEndEffects);

                if (Globals::globalVerbosity & 16384)
                {
                    if (!eta.empty())
                    {
                        if (eff == PE_ADDED)
                        {
                            cout << "Add effects on " << *(*fItr) << " are pointless - number of actions with this precondition: " << preconditionsToActions[(*fItr)->getStateID()].size() << endl;
                        }
                        else
                        {
                            cout << "Delete effects on " << *(*fItr) << " are pointless\n";
                        }
                    }
                }

                list<pair<int, VAL::time_spec>>::const_iterator etaItr = eta.begin();
                const list<pair<int, VAL::time_spec>>::const_iterator etaEnd = eta.end();

                for (; etaItr != etaEnd; ++etaItr)
                {
                    switch (etaItr->second)
                    {
                    case VAL::E_AT_START:
                    {
                        if (Globals::globalVerbosity & 16384)
                        {
                            cout << " - Removed effect from start of " << *(RPGBuilder::getInstantiatedOp(etaItr->first)) << endl;
                        }
                        pointless_effect &toUpdate = pointlessStartEffects[etaItr->first].insert(make_pair(*fItr, eff)).first->second;
                        toUpdate = (pointless_effect)(toUpdate | eff);
                        const bool rv = removeFirst(startEffs[etaItr->first], *fItr);
                        actionsToCheckIfPointlessAfterStrippingEffects.insert(etaItr->first);
                        assert(rv);
                        break;
                    }
                    case VAL::E_AT_END:
                    {
                        if (Globals::globalVerbosity & 16384)
                        {
                            cout << " - Removed effect from end of " << *(RPGBuilder::getInstantiatedOp(etaItr->first)) << endl;
                        }

                        pointless_effect &toUpdate = pointlessEndEffects[etaItr->first].insert(make_pair(*fItr, eff)).first->second;
                        toUpdate = (pointless_effect)(toUpdate | eff);
                        const bool rv = removeFirst(endEffs[etaItr->first], *fItr);
                        actionsToCheckIfPointlessAfterStrippingEffects.insert(etaItr->first);
                        assert(rv);
                        break;
                    }
                    case VAL::E_AT:
                    {
                        pointless_effect &toUpdate = pointlessTILEffects[etaItr->first].insert(make_pair(*fItr, eff)).first->second;
                        toUpdate = (pointless_effect)(toUpdate | eff);
                        if (toUpdate == PE_ADDED)
                        {
                            const bool rv = removeFirst(timedInitialLiteralsVector[etaItr->first]->addEffects, *fItr);
                            assert(rv);
                        }
                        else
                        {
                            const bool rv = removeFirst(timedInitialLiteralsVector[etaItr->first]->delEffects, *fItr);
                            assert(rv);
                        }
                        break;
                    }
                    default:
                    {
                        std::cerr << "Internal error: facts should always be added by one of an action start, an action end, or a TIL\n";
                        exit(1);
                    }
                    }
                }
                eta.clear();
            }
        }

        set<int>::const_iterator actCheckItr = actionsToCheckIfPointlessAfterStrippingEffects.begin();
        const set<int>::const_iterator actCheckEnd = actionsToCheckIfPointlessAfterStrippingEffects.end();

        for (; actCheckItr != actCheckEnd; ++actCheckItr)
        {

            //动作有开始添加效果，则它有意义，检查下一个动作
            if (!RPGBuilder::getStartPropositionAdds()[*actCheckItr].empty())
            {
                if (Globals::globalVerbosity & 16384)
                {
                    cout << "Still keeping " << *(RPGBuilder::getInstantiatedOp(*actCheckItr)) << " as it has start add effects\n";
                }
                // action has start adds - is not pointless
                continue;
            }

            if (Globals::globalVerbosity & 16384)
            {
                cout << "i) " << *(RPGBuilder::getInstantiatedOp(*actCheckItr)) << " has no start add effects\n";
            }

            list<Literal *> &endAdds = RPGBuilder::getEndPropositionAdds()[*actCheckItr];

            //根据逻辑判断该动作是否有无意义的效果
            if (!endAdds.empty())
            {

                //map<int,bool> actionsThatDeleteThisFactNeedIt;

                list<Literal *>::const_iterator effItr = endAdds.begin();
                const list<Literal *>::const_iterator effEnd = endAdds.end();

                for (; effItr != effEnd; ++effItr)
                {

                    const pair<map<int, bool>::iterator, bool> insPair = actionsThatDeleteThisFactNeedIt.insert(make_pair((*effItr)->getStateID(), true));

                    //判断 删除无意义fact后的动作的结束添加效果，是否是 某个要删除它的动作的前提，若是，该效果有意义
                    if (insPair.second)
                    { //插入操作成功
                        // not worked out whether it follows the 'only deleted immediately after inspection' idiom

                        const list<pair<int, VAL::time_spec>> &deletors = negativeEffectsToActions[(*effItr)->getStateID()];

                        list<pair<int, VAL::time_spec>>::const_iterator dItr = deletors.begin();
                        const list<pair<int, VAL::time_spec>>::const_iterator dEnd = deletors.end();

                        for (; dItr != dEnd; ++dItr)
                        {
                            // looking for a counter example: delete not coupled to a precondition

                            list<Literal *> *accompanyingPres = 0;

                            if (dItr->second == VAL::E_AT_START)
                            {
                                accompanyingPres = &(actionsToStartPreconditions[dItr->first]);
                            }
                            else if (dItr->second == VAL::E_AT_END)
                            {
                                accompanyingPres = &(actionsToEndPreconditions[dItr->first]);
                            }
                            else
                            {
                                assert(dItr->second == VAL::E_AT);
                                // is deleted by a TIL, therefore no coupled precondition
                                insPair.first->second = false;
                                break;
                            }

                            list<Literal *>::const_iterator pItr = accompanyingPres->begin();
                            const list<Literal *>::const_iterator pEnd = accompanyingPres->end();

                            for (; pItr != pEnd; ++pItr)
                            {
                                //删除无意义fact后的动作的结束添加效果 刚好是 某个要删除它的动作的前提
                                if ((*pItr)->getStateID() == (*effItr)->getStateID())
                                {
                                    break;
                                }
                            }
                            if (pItr == pEnd)
                            {
                                // could not find matching precondition - is a counter-example
                                if (Globals::globalVerbosity & 16384)
                                {
                                    cout << *(RPGBuilder::getInstantiatedOp(dItr->first)) << " deletes " << *(*effItr) << " without needing it\n";
                                }
                                insPair.first->second = false;
                                break;
                            }
                        }
                    }

                    if (!insPair.first->second)
                    { //该效果有意义
                        if (Globals::globalVerbosity & 16384)
                        {
                            cout << "Still keeping " << *(RPGBuilder::getInstantiatedOp(*actCheckItr)) << " as it end-adds " << *(*effItr) << endl;
                        }
                        break;
                    }
                    else
                    { //该效果没有匹配的前提条件需求
                        // if this action needed it at the start, the add effect on it isn't interesting

                        bool everNeeded = false;

                        for (int enPass = 0; !everNeeded && enPass < 2; ++enPass)
                        {

                            list<Literal *> &lookat = (enPass ? actionsToEndPreconditions[*actCheckItr] : actionsToStartPreconditions[*actCheckItr]);

                            list<Literal *>::const_iterator spItr = lookat.begin();
                            const list<Literal *>::const_iterator spEnd = lookat.end();
                            for (; spItr != spEnd; ++spItr)
                            {
                                if ((*spItr) == (*effItr))
                                {
                                    everNeeded = true;
                                    break;
                                }
                            }
                        }

                        if (!everNeeded)
                        {
                            if (Globals::globalVerbosity & 16384)
                            {
                                cout << "Still keeping " << *(RPGBuilder::getInstantiatedOp(*actCheckItr)) << " as it end-adds " << *(*effItr) << " without having needed it earlier\n";
                            }

                            break;
                        }
                        else
                        {
                            if (Globals::globalVerbosity & 16384)
                            {
                                cout << "ii) " << *(RPGBuilder::getInstantiatedOp(*actCheckItr)) << " end-adds " << *(*effItr) << ", but actions that delete this fact need it\n";
                            }
                        }
                    }
                }
                if (effItr != effEnd)
                {
                    continue;
                }
            }

            bool numericEffectsAreOnlyBad = true;

            // first double: constant effect, second double: multiplier applied to ?duration
            map<int, pair<double, double>> accruedSimpleEffectOnPNE;

            for (int pass = 0; numericEffectsAreOnlyBad && pass < 2; ++pass)
            {

                const list<int> &numericEffs = (pass ? RPGBuilder::getEndEffNumerics()[*actCheckItr] : RPGBuilder::getStartEffNumerics()[*actCheckItr]);

                {
                    list<int>::const_iterator nEffItr = numericEffs.begin();
                    const list<int>::const_iterator nEffEnd = numericEffs.end();
                    for (; numericEffectsAreOnlyBad && nEffItr != nEffEnd; ++nEffItr)
                    {
                        const RPGBuilder::RPGNumericEffect &currEff = RPGBuilder::getNumericEff()[*nEffItr];
                        switch (NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex])
                        {
                        case NumericAnalysis::E_NODOMINANCE:
                        {
                            if (Globals::globalVerbosity & 16384)
                            {
                                cout << "Still keeping " << *(RPGBuilder::getInstantiatedOp(*actCheckItr)) << " as it has effects on a non-dominated numeric variable\n";
                            }

                            numericEffectsAreOnlyBad = false;
                            break;
                        }
                        case NumericAnalysis::E_IRRELEVANT:
                        case NumericAnalysis::E_METRICTRACKING:
                        {
                            break;
                        }
                        case NumericAnalysis::E_BIGGERISBETTER:
                        case NumericAnalysis::E_SMALLERISBETTER:
                        {
                            if (currEff.isAssignment || currEff.size > 1)
                            {
                                // all bets are off - assignment could make it worse or better
                                // and multi-variable-based effects, based on something other than ?duration
                                // have non-predicable outcomes
                                if (Globals::globalVerbosity & 16384)
                                {
                                    cout << "Still keeping " << *(RPGBuilder::getInstantiatedOp(*actCheckItr)) << " as it an assignment effect or multi-variable effect on a variable\n";
                                }

                                numericEffectsAreOnlyBad = false;
                                break;
                            }
                            pair<double, double> effInFormConstantAndDurationCoefficient(currEff.constant, 0.0);

                            if (currEff.size)
                            {
                                assert(currEff.size == 1);
                                if (currEff.variables[0] == -3)
                                {
                                    // +?duration
                                    effInFormConstantAndDurationCoefficient.second = currEff.weights[0];
                                }
                                else if (currEff.variables[0] == -19)
                                {
                                    // -?duration
                                    effInFormConstantAndDurationCoefficient.second = -currEff.weights[0];
                                }
                                else
                                {
                                    if (Globals::globalVerbosity & 16384)
                                    {
                                        cout << "Still keeping " << *(RPGBuilder::getInstantiatedOp(*actCheckItr)) << " as it has a variable-dependent effect on a variable\n";
                                    }

                                    numericEffectsAreOnlyBad = false;
                                    break;
                                }
                            }

                            // now we've shown the effect is of the form v += constant + k * ?duration
                            // find bounds on this, accounting for anything that happened at the start (if we're on the second pass, for end effects)

                            if (pass == 1)
                            {
                                const map<int, pair<double, double>>::const_iterator startEffOnThisVar = accruedSimpleEffectOnPNE.find(currEff.fluentIndex);

                                if (startEffOnThisVar != accruedSimpleEffectOnPNE.end())
                                {
                                    effInFormConstantAndDurationCoefficient.first += startEffOnThisVar->second.first;
                                    effInFormConstantAndDurationCoefficient.second += startEffOnThisVar->second.second;
                                }
                            }

                            double minValueOfEffect = effInFormConstantAndDurationCoefficient.first;
                            double maxValueOfEffect = effInFormConstantAndDurationCoefficient.first;

                            if (effInFormConstantAndDurationCoefficient.second > 0.0)
                            {
                                // positive duration coefficient - small as possible duration for min, big as possible for max
                                minValueOfEffect += effInFormConstantAndDurationCoefficient.second * RPGBuilder::getOpMinDuration(*actCheckItr, 0);
                                maxValueOfEffect += effInFormConstantAndDurationCoefficient.second * RPGBuilder::getOpMaxDuration(*actCheckItr, 0);
                            }
                            else if (effInFormConstantAndDurationCoefficient.second > 0.0)
                            {
                                // negative duration coefficient - big as possible duration for min, small as possible for max
                                minValueOfEffect += effInFormConstantAndDurationCoefficient.second * RPGBuilder::getOpMaxDuration(*actCheckItr, 0);
                                maxValueOfEffect += effInFormConstantAndDurationCoefficient.second * RPGBuilder::getOpMinDuration(*actCheckItr, 0);
                            }

                            if (NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] == NumericAnalysis::E_BIGGERISBETTER)
                            {
                                // the 'bigger is better' case
                                // this is a good effect if the maximum effect is positive, i.e. there's some way it can muster an increase
                                if (maxValueOfEffect > 0.0)
                                {
                                    // possible to have net gain - effect could be good
                                    if (Globals::globalVerbosity & 16384)
                                    {
                                        cout << "Still keeping " << *(RPGBuilder::getInstantiatedOp(*actCheckItr)) << " as it has a beneficial effect on " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << endl;
                                    }

                                    numericEffectsAreOnlyBad = false;
                                }
                                else
                                {
                                    if (pass == 0)
                                    {
                                        // if it's a start effect, even if it's bad, note it for later
                                        // as we want to check if the action has a net gain.  e.g. decrease by 2 at start,
                                        // increase by <= 2 at end is an effect in the right direction, but it's not net gain

                                        accruedSimpleEffectOnPNE[currEff.fluentIndex] = effInFormConstantAndDurationCoefficient;
                                    }
                                }
                            }
                            else
                            {
                                // the 'smaller is better' case
                                // this is a good effect if the minimum effect is negative, i.e. there's some way it can muster a decrease
                                if (minValueOfEffect < 0.0)
                                {
                                    // possible to have net loss - effect could be good
                                    numericEffectsAreOnlyBad = false;
                                    if (Globals::globalVerbosity & 16384)
                                    {
                                        cout << "Still keeping " << *(RPGBuilder::getInstantiatedOp(*actCheckItr)) << " as it has a beneficial effect on " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << endl;
                                    }
                                }
                                else
                                {
                                    if (pass == 0)
                                    {
                                        accruedSimpleEffectOnPNE[currEff.fluentIndex] = effInFormConstantAndDurationCoefficient;
                                        accruedSimpleEffectOnPNE[currEff.fluentIndex] = effInFormConstantAndDurationCoefficient;
                                    }
                                }
                            }

                            break;
                        }
                        }
                    }
                }

                if (numericEffectsAreOnlyBad && pass == 0)
                {
                    RPGBuilder::LinearEffects *const currLE = RPGBuilder::getLinearDiscretisation()[*actCheckItr];
                    if (currLE)
                    {
                        const int ceCount = currLE->vars.size();
                        for (int cei = 0; numericEffectsAreOnlyBad && cei < ceCount; ++cei)
                        {
                            switch (NumericAnalysis::getDominanceConstraints()[currLE->vars[cei]])
                            {
                            case NumericAnalysis::E_NODOMINANCE:
                            {
                                numericEffectsAreOnlyBad = false;
                                break;
                            }
                            case NumericAnalysis::E_IRRELEVANT:
                            case NumericAnalysis::E_METRICTRACKING:
                            {
                                break;
                            }
                            case NumericAnalysis::E_BIGGERISBETTER:
                            case NumericAnalysis::E_SMALLERISBETTER:
                            {

                                pair<double, double> effInFormConstantAndDurationCoefficient(0.0, currLE->effects[0][cei].constant);

                                const map<int, pair<double, double>>::const_iterator startEffOnThisVar = accruedSimpleEffectOnPNE.find(currLE->vars[cei]);

                                if (startEffOnThisVar != accruedSimpleEffectOnPNE.end())
                                {
                                    effInFormConstantAndDurationCoefficient.first += startEffOnThisVar->second.first;
                                    effInFormConstantAndDurationCoefficient.second += startEffOnThisVar->second.second;
                                }

                                double minValueOfEffect = effInFormConstantAndDurationCoefficient.first;
                                double maxValueOfEffect = effInFormConstantAndDurationCoefficient.first;

                                if (effInFormConstantAndDurationCoefficient.second > 0.0)
                                {
                                    // positive duration coefficient - small as possible duration for min, big as possible for max
                                    minValueOfEffect += effInFormConstantAndDurationCoefficient.second * RPGBuilder::getOpMinDuration(*actCheckItr, 0);
                                    maxValueOfEffect += effInFormConstantAndDurationCoefficient.second * RPGBuilder::getOpMaxDuration(*actCheckItr, 0);
                                }
                                else if (effInFormConstantAndDurationCoefficient.second > 0.0)
                                {
                                    // negative duration coefficient - big as possible duration for min, small as possible for max
                                    minValueOfEffect += effInFormConstantAndDurationCoefficient.second * RPGBuilder::getOpMaxDuration(*actCheckItr, 0);
                                    maxValueOfEffect += effInFormConstantAndDurationCoefficient.second * RPGBuilder::getOpMinDuration(*actCheckItr, 0);
                                }

                                if (NumericAnalysis::getDominanceConstraints()[currLE->vars[cei]] == NumericAnalysis::E_BIGGERISBETTER)
                                {
                                    // the 'bigger is better' case
                                    // this is a good effect if the maximum effect is positive, i.e. there's some way it can muster an increase
                                    if (maxValueOfEffect > 0.0)
                                    {
                                        // possible to have net gain - effect could be good
                                        numericEffectsAreOnlyBad = false;
                                    }
                                    else
                                    {
                                        accruedSimpleEffectOnPNE[currLE->vars[cei]] = effInFormConstantAndDurationCoefficient;
                                    }
                                }
                                else
                                {
                                    // the 'smaller is better' case
                                    // this is a good effect if the minimum effect is negative, i.e. there's some way it can muster a decrease
                                    if (minValueOfEffect < 0.0)
                                    {
                                        // possible to have net loss - effect could be good
                                        numericEffectsAreOnlyBad = false;
                                    }
                                    else
                                    {
                                        accruedSimpleEffectOnPNE[currLE->vars[cei]] = effInFormConstantAndDurationCoefficient;
                                    }
                                }
                                break;
                            }
                            }
                        }
                    }
                }
            }

            if (numericEffectsAreOnlyBad)
            {
                // the action doesn't add any facts, and it's numeric effects are not a good idea

                if (Globals::globalVerbosity & 16384)
                {
                    cout << "Marking " << *(RPGBuilder::getInstantiatedOp(*actCheckItr)) << " as rogue\n";
                }

#ifdef ENABLE_DEBUGGING_HOOKS
                {
                    Globals::eliminatedAction(*actCheckItr, "Only has pointless effects");
                }
#endif

                realRogueActions[*actCheckItr] = true;

                // as we aren't clearing the register of this action's start propositional add effects, assert none exist
                assert(actionsToStartEffects[*actCheckItr].empty());

                {
                    list<Literal *> &currEffectsList = actionsToStartNegativeEffects[*actCheckItr];

                    list<Literal *>::iterator effItr = currEffectsList.begin();
                    const list<Literal *>::iterator effEnd = currEffectsList.end();

                    for (; effItr != effEnd; ++effItr)
                    {
                        const int effID = (*effItr)->getStateID();

                        const bool rv = removeFirst(negativeEffectsToActions[effID], pair<int, VAL::time_spec>(*actCheckItr, VAL::E_AT_START));
                        assert(rv);
                    }
                    currEffectsList.clear();
                }

                {
                    list<Literal *> &currEffectsList = actionsToStartEffects[*actCheckItr];

                    list<Literal *>::iterator effItr = currEffectsList.begin();
                    const list<Literal *>::iterator effEnd = currEffectsList.end();

                    for (; effItr != effEnd; ++effItr)
                    {
                        const int effID = (*effItr)->getStateID();
                        const bool rv = removeFirst(effectsToActions[effID], pair<int, VAL::time_spec>(*actCheckItr, VAL::E_AT_START));
                        assert(rv);
                    }
                    currEffectsList.clear();
                }

                {
                    list<Literal *> &currEffectsList = actionsToEndNegativeEffects[*actCheckItr];

                    list<Literal *>::iterator effItr = currEffectsList.begin();
                    const list<Literal *>::iterator effEnd = currEffectsList.end();

                    for (; effItr != effEnd; ++effItr)
                    {
                        const int effID = (*effItr)->getStateID();
                        const bool rv = removeFirst(negativeEffectsToActions[effID], pair<int, VAL::time_spec>(*actCheckItr, VAL::E_AT_END));
                        assert(rv);
                    }
                    currEffectsList.clear();
                }

                for (int pass = 0; pass < 2; ++pass)
                {

                    list<int> &currEffectsList = (pass ? actionsToRPGNumericEndEffects[*actCheckItr] : actionsToRPGNumericStartEffects[*actCheckItr]);

                    list<int>::iterator effItr = currEffectsList.begin();
                    const list<int>::iterator effEnd = currEffectsList.end();

                    for (; effItr != effEnd; ++effItr)
                    {
                        const bool rv = removeFirst(rpgNumericEffectsToActions[*effItr], pair<int, VAL::time_spec>(*actCheckItr, pass ? VAL::E_AT_END : VAL::E_AT_START));
                        assert(rv);
                    }

                    currEffectsList.clear();
                }

                {

                    list<Literal *> &currPreconditionsList = actionsToStartPreconditions[*actCheckItr];

                    list<Literal *>::iterator precItr = currPreconditionsList.begin();
                    const list<Literal *>::iterator precEnd = currPreconditionsList.end();

                    for (; precItr != precEnd; ++precItr)
                    {
                        const int precID = (*precItr)->getStateID();
                        const bool rv = removeFirst(preconditionsToActions[precID], pair<int, VAL::time_spec>(*actCheckItr, VAL::E_AT_START));
                        assert(rv);

                        if (preconditionsToActions[precID].empty() && literalGoalSet.find(*precItr) == literalGoalSet.end())
                        {
                            newlyPointlessEffects.insert(*precItr);
                        }
                    }

                    currPreconditionsList.clear();
                }

                {
                    list<Literal *> &currPreconditionsList = actionsToInvariants[*actCheckItr];

                    list<Literal *>::iterator precItr = currPreconditionsList.begin();
                    const list<Literal *>::iterator precEnd = currPreconditionsList.end();

                    for (; precItr != precEnd; ++precItr)
                    {
                        const int precID = (*precItr)->getStateID();
                        const bool rv = removeFirst(preconditionsToActions[precID], pair<int, VAL::time_spec>(*actCheckItr, VAL::E_OVER_ALL));
                        assert(rv);
                        if (preconditionsToActions[precID].empty() && literalGoalSet.find(*precItr) == literalGoalSet.end())
                        {
                            newlyPointlessEffects.insert(*precItr);
                        }
                    }
                    currPreconditionsList.clear();
                }

                {
                    list<Literal *> &currPreconditionsList = actionsToEndPreconditions[*actCheckItr];

                    list<Literal *>::iterator precItr = currPreconditionsList.begin();
                    const list<Literal *>::iterator precEnd = currPreconditionsList.end();

                    for (; precItr != precEnd; ++precItr)
                    {
                        const int precID = (*precItr)->getStateID();
                        const bool rv1 = removeFirst(preconditionsToActions[precID], pair<int, VAL::time_spec>(*actCheckItr, VAL::E_AT_END));
                        assert(rv1);
                        const bool rv2 = removeFirst(processedPreconditionsToActions[precID], pair<int, VAL::time_spec>(*actCheckItr, VAL::E_AT_END));
                        assert(rv2);

                        if (preconditionsToActions[precID].empty() && literalGoalSet.find(*precItr) == literalGoalSet.end())
                        {
                            newlyPointlessEffects.insert(*precItr);
                        }
                    }

                    if (currPreconditionsList.empty())
                    {

                        if (actionsToRPGNumericEndPreconditions[*actCheckItr].empty())
                        {
                            const bool rv = removeFirst(preconditionlessActions, pair<int, VAL::time_spec>(*actCheckItr, VAL::E_AT_END));
                            assert(rv);
                        }
                        else
                        {
                            const bool rv = removeFirst(onlyNumericPreconditionActions, pair<int, VAL::time_spec>(*actCheckItr, VAL::E_AT_END));
                            assert(rv);
                        }
                    }

                    currPreconditionsList.clear();
                }

                {
                    list<Literal *> &newStartPrecs = actionsToProcessedStartPreconditions[*actCheckItr];
                    if (newStartPrecs.empty())
                    {
                        if (actionsToProcessedStartRPGNumericPreconditions[*actCheckItr].empty())
                        {
                            const bool rv = removeFirst(preconditionlessActions, pair<int, VAL::time_spec>(*actCheckItr, VAL::E_AT_START));
                            assert(rv);
                        }
                        else
                        {
                            const bool rv = removeFirst(onlyNumericPreconditionActions, pair<int, VAL::time_spec>(*actCheckItr, VAL::E_AT_START));
                            assert(rv);
                        }
                    }

                    list<Literal *>::iterator precItr = newStartPrecs.begin();
                    const list<Literal *>::iterator precEnd = newStartPrecs.end();

                    for (; precItr != precEnd; ++precItr)
                    {
                        const int precID = (*precItr)->getStateID();
                        const bool rv = removeFirst(processedPreconditionsToActions[precID], pair<int, VAL::time_spec>(*actCheckItr, VAL::E_AT_START));
                        assert(rv);
                    }

                    newStartPrecs.clear();
                }

                for (int pass = 0; pass < 2; ++pass)
                {
                    list<int> &currPreconditionsList = (pass ? actionsToRPGNumericInvariants[*actCheckItr] : actionsToRPGNumericStartPreconditions[*actCheckItr]);

                    list<int>::iterator precItr = currPreconditionsList.begin();
                    const list<int>::iterator precEnd = currPreconditionsList.end();

                    for (; precItr != precEnd; ++precItr)
                    {
                        const bool rv = removeFirst(rpgNumericPreconditionsToActions[*precItr], pair<int, VAL::time_spec>(*actCheckItr, pass ? VAL::E_OVER_ALL : VAL::E_AT_START));
                        assert(rv);
                    }

                    currPreconditionsList.clear();
                }

                {
                    list<int> &currPreconditionsList = actionsToRPGNumericEndPreconditions[*actCheckItr];

                    list<int>::iterator precItr = currPreconditionsList.begin();
                    const list<int>::iterator precEnd = currPreconditionsList.end();

                    for (; precItr != precEnd; ++precItr)
                    {
                        const bool rv1 = removeFirst(rpgNumericPreconditionsToActions[*precItr], pair<int, VAL::time_spec>(*actCheckItr, VAL::E_AT_END));
                        assert(rv1);
                        const bool rv2 = removeFirst(processedRPGNumericPreconditionsToActions[*precItr], pair<int, VAL::time_spec>(*actCheckItr, VAL::E_AT_END));
                        assert(rv2);
                    }

                    currPreconditionsList.clear();
                }

                {
                    list<int> &currPreconditionsList = actionsToProcessedStartRPGNumericPreconditions[*actCheckItr];

                    list<int>::iterator precItr = currPreconditionsList.begin();
                    const list<int>::iterator precEnd = currPreconditionsList.end();

                    for (; precItr != precEnd; ++precItr)
                    {
                        const bool rv = removeFirst(processedRPGNumericPreconditionsToActions[*precItr], pair<int, VAL::time_spec>(*actCheckItr, VAL::E_AT_START));
                        assert(rv);
                    }

                    currPreconditionsList.clear();
                }
            }
        }
    }
}
}
;
