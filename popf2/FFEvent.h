#ifndef FFEVENT_H
#define FFEVENT_H

#include <unistd.h>
#include <ptree.h>

namespace Inst {
    class instantiatedOp;
};

using Inst::instantiatedOp;

#include <set>
using std::set;

namespace Planner {

#ifdef STOCHASTICDURATIONS
class StochasticTimestampData;
#endif


class FFEvent
{

public:

    static int tilLimit;//时间初始化文字的数量

    instantiatedOp* action;
    VAL::time_spec time_spec; //例如 VAL::E_AT_START
    double minDuration;
    double maxDuration;
    int pairWithStep;//该动作的开始步骤ID
//  ScheduleNode* wait;
    bool getEffects;//true:可以立即获取，false:从future end获取
    double lpTimestamp;
    double lpMinTimestamp;
    double lpMaxTimestamp;
    int divisionID; //时间初始化文字TIL的序号
    set<int> needToFinish;
    
    #ifdef STOCHASTICDURATIONS
    StochasticTimestampData * stochasticTimestamp;
    #endif
    
    FFEvent(instantiatedOp* a, const double & dMin, const double & dMax);//FFEvent 开始，time_spec(VAL::E_AT_START)，pairWithStep(-1)
    FFEvent(instantiatedOp* a, const int & pw, const double & dMin, const double & dMax);//FFEvent 结束，time_spec(VAL::E_AT_END)，pairWithStep(pw)
    FFEvent(instantiatedOp* a, const int & s, const int & pw, const double & dMin, const double & dMax);//FFevent 结束, time_spec(VAL::E_OVER_ALL), pairWithStep(pw), divisionID(s)
    FFEvent(const int & t);//FFEvent 开始

    virtual ~FFEvent();
    
    virtual void passInMinMax(const double & a, const double & b) {
        lpMinTimestamp = a;
        lpMaxTimestamp = b;
    }

    FFEvent(const FFEvent & f);
//  FFEvent(ScheduleNode* s, const bool & b);
    FFEvent();//action(0)
    FFEvent & operator=(const FFEvent & f);
    bool operator==(const FFEvent & f) const {
        if (time_spec != VAL::E_AT_START && pairWithStep != f.pairWithStep) return false;
        return (action == f.action && time_spec == f.time_spec && minDuration == f.minDuration && maxDuration == f.maxDuration && pairWithStep == f.pairWithStep && getEffects == f.getEffects && divisionID == f.divisionID);
    }


    static void printPlan(const list<FFEvent> & toPrint);

};

};

#endif
