package solver

// Controls the solution process

import (
	"fmt"
	"lp"
	"math"
	"math/rand"
	"sort"
	"strconv"
	"time"
	//"sync"
	//"os"
)

//var WG sync.WaitGroup // sets up a waitgroup

// Package global variables
var PrintLevel int     // controls the level of printing. Setting it equal to zero turns printing off
var plinfy float64     // plus infinity
var featol float64     // feasibility tolerance
var Alpha float64      // Feasibility distance tolerance
var Beta float64       // Movement tolerance
var MaxItns int        // Maximum number of iterations
var Point []float64    // A point
var FinalBox int       // Captures the last box commenced so it can be printed out
var FinalPointType int // Captures the type of the final point.

var MaxSwarmPts int        // Maximum number of points in a swarm
var MaxPts int             // The number of points this time around. Equals NumSpecialPts or MaxSwarmPts
var Swarm [][]float64      // Collection of points in the current swarm of points
var SwarmMaxViol []float64 // Maximum violation associated with a swarm point
var SwarmSINF []float64    // SINF associated with a swarm point
var SwarmNINF []int        // NINF associated with a swarm point
var SwarmSFD []float64     // Sum of feasibility distances associated with a swarm point
var SwarmDescrip []string  // Description of swarm point

var WorstNINF int   // Worst NINF for any swarm point
var WorstNINFel int // Element number for worst NINF point in the swarm

var IncumbentPt []float64 // Incumbent point (lowest SFD seen yet)
var IncumbentSINF float64 // SINF for incumbent point
var IncumbentSFD float64  // Sum of feasibility distances for incumbent point
var IncumbentNINF int     // NINF for incumbent point

var NIncumbentPt []float64 // NINF incumbent point
var NIncumbentSINF float64 // SINF at NINF incumbent point
var NIncumbentSFD float64  // SFD at NINF incumbent point
var NIncumbentNINF int     // NINF at NINF incumbent point

var SmallestNINF int // Smallest NINF encountered

var BoxBndLo []float64 // Sample box lower bounds
var BoxBndUp []float64 // Sample box upper bounds

var NumUpdate []int                   // Number of incumbent updates provided by LHC
var FracUpdate []float64              // Average fractional incumbent update
var TotUpdates int                    // The total number of incumbent updates (excludes the initial incumbent)
var UpdatesAtRoundStart int           // The total number of incumbent updates when a round starts
var FailedRounds int	// Makes note of the number of rounds that have failed to produce an improved incumbent
var LinProjSucceeds, LinProjFails int // Number of successes and failures for augmentation
var LinProjFrac float64               // Average fractional augmentation successes.
var QuadProjSucceeds, QuadProjFails int
var QuadProjFrac float64

// Structures needed for sorting the impact list
type IMPACT struct {
	Row   int
	Sum   int
}
type BySum []IMPACT
var ImpactList []int // Holds the constraint id number for row constraints sorted from most to least impact

type POINTDATA struct {
	Point []float64
	SFD float64
	NINF int
}

//var IncumbentUp, IncumbentDown, IncumbentSame []int // When incumbent changes, the variable might go up, down, or stay the same. Count the changes.

//var LPPtr *lp.LPOBJ
//var NumEls, NumRows, NumGRows, NumLRows, NumERows, NumNRows, NumCols, NumICols, NumRCols int
//var AvgElsPerRow float64
//var MaxElsInRow int
//var AvgElsPerCol float64
//var MaxElsInCol int

//=======================================================================================
// Returns the violation (with sign) for a given constraint (but not bounds)
// FVStatus: 0:(success), 1:(numerical problem)
// ViolStatus: 0:(violated), 1:(oversatisfied), 2:(tight within tolerance)
func GetViolation(icon int, CCPoint []float64) (FVStatus int, ViolStatus int, Violation float64) {

	var BodyVal float64 = 0
	var Status int

	//Check violation status
	BodyVal, Status = lp.ConBodyValue(icon, CCPoint)
	if Status == 1 { // Nonbinding constraint
		return 0, 1, 0.0
	}
	if Status == 2 { // Numerical problem
		fmt.Println("Problem evaluating body of constraint", icon, ". Aborting solver.GetViolation.")
		return 1, 0, 0.0
	}
	// Constraint body successfully evaluated. Now check for violation (sign is correct)
	switch lp.LP.Rows[icon].Type {
	case "G": // Greater than constraint
		if BodyVal >= lp.LP.Rows[icon].RHSlo-featol {
			Violation = 0.0
			ViolStatus = 1
			if BodyVal-lp.LP.Rows[icon].RHSlo <= featol {
				ViolStatus = 2
			}
		} else {
			Violation = lp.LP.Rows[icon].RHSlo - BodyVal
			ViolStatus = 0
		}
	case "L": // Less than constraint
		if BodyVal <= lp.LP.Rows[icon].RHSup+featol {
			Violation = 0.0
			ViolStatus = 1
			if lp.LP.Rows[icon].RHSup-BodyVal <= featol {
				ViolStatus = 2
			}
		} else {
			Violation = lp.LP.Rows[icon].RHSup - BodyVal
			ViolStatus = 0
		}
	case "E", "R": // equality or range constraint
		Violation = 0.0
		ViolStatus = 1
		if BodyVal <= lp.LP.Rows[icon].RHSlo-featol {
			// Violates lower bound
			Violation = lp.LP.Rows[icon].RHSlo - BodyVal
			ViolStatus = 0
		} else if BodyVal >= lp.LP.Rows[icon].RHSup+featol {
			// Violates upper bound
			Violation = lp.LP.Rows[icon].RHSup - BodyVal
			ViolStatus = 0
		}
		if ViolStatus == 1 {
			// Check whether it's tight to one of the bounds
			if lp.LP.Rows[icon].Type == "E" {
				ViolStatus = 2 // It's an equality and satisfies both bounds, so it's tight
			} else {
				// It's a range constraint so you have to check whether it's tight to either RHS
				if math.Abs(BodyVal-lp.LP.Rows[icon].RHSlo) <= featol || math.Abs(BodyVal-lp.LP.Rows[icon].RHSup) <= featol {
					ViolStatus = 2
				}
			}

		}
	} // end of the switch

	if ViolStatus >= 1 {
		return 0, ViolStatus, 0.0
	} else {
		//test
		//if math.IsNaN(Violation) {fmt.Println("Warning: NaN generated in GetViolation routine")}
		return 0, 0, Violation
	}
}

////=======================================================================================
//// The original version of CC takes in a point (PointIn) and runs until it can return a PointOut
//// Status values: 0:(success), 1:(max iterations reached), 2:(movement tolerance violated), 3:(numerical problem)
//func CCOriginal(PointIn []float64) (CCPoint []float64, Status int) {
//
//	var NINF int = 0                         // Number of violated constraints
//	var Violation float64                    // The constraint violation
//	NumViol := make([]int, len(PointIn))     // Number of violations
//	SumViol := make([]float64, len(PointIn)) // Sum of violations (in terms of feasibility vector components)
//	CCPoint = make([]float64, len(PointIn))  // Constraint consensus point
//	CV := make([]float64, len(PointIn))      // Consensus Vector
//	var FVStatus int = 0
//	var ViolStatus int = 0
//	var ElNum int  // Element number
//	var ColNum int // Column number
//	var rhold, rhold1 float64
//
//	//test
//	//fmt.Println("In CCOriginal. MaxItns:",MaxItns)
//
//	Status = 0
//	CCPoint = PointIn
//	for itn := 0; itn < MaxItns; itn++ {
//		// Zero the accumulators
//		NINF = 0
//		for i := range PointIn {
//			NumViol[i] = 0
//			SumViol[i] = 0.0
//			CV[i] = 0.0
//		}
//
//		// Run through the constraints
//		for icon := 0; icon < lp.NumRows; icon++ {
//			// Get the feasibility vector, if there is one
//			FVStatus, ViolStatus, Violation = GetViolation(icon, CCPoint)
//
//			//test
//			//fmt.Println("After GetViolation call for con",icon,"Violation:",Violation,"FVStatus:",FVStatus,"ViolStatus:",ViolStatus)
//
//			if FVStatus > 0 {
//				fmt.Println("Error evaluating feasibility status for constraint", icon, ". Skipping it.")
//				continue
//			}
//			if ViolStatus > 0 {
//				// not violated, so skip
//				continue
//			}
//			// Constraint is violated, so update counters if feasibility vector is long enough
//			// First check length of feasibility vector
//
//			//test
//			//fmt.Println("In CCOriginal. GradVecLenSq for con",icon,":",lp.LP.Rows[icon].GradVecLenSq)
//
//			rhold = 0.0 // Accumulates length of feasibility vector
//			for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
//				ElNum = lp.LP.Rows[icon].ElList[iel]
//				ColNum = lp.Element[ElNum].Col
//
//				//test
//				//fmt.Println("In CCOriginal. Con:",icon,"element:",ElNum,"Col:",ColNum,"Value:",lp.Element[ElNum].Value)
//
//				rhold1 = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
//				rhold = rhold + rhold1*rhold1
//			}
//			//test
//			//fmt.Println("In CCOriginal. rhold:",rhold,"Alpha:",Alpha)
//
//			if rhold < Alpha*Alpha {
//				// Feasibility vector is too short
//
//				//test
//				fmt.Println("In CCOriginal. Skipping con", icon, "at itn", itn, "because feasibility vector is too short")
//
//				continue
//			}
//			NINF++
//			for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
//				ElNum = lp.LP.Rows[icon].ElList[iel]
//				ColNum = lp.Element[ElNum].Col
//				NumViol[ColNum]++
//				SumViol[ColNum] = SumViol[ColNum] + Violation*lp.Element[ElNum].Value/lp.LP.Rows[icon].GradVecLenSq
//			}
//		}
//
//		// Run through the bounds looking for violations and making appropriate updates
//		for ivar := 0; ivar < lp.NumCols; ivar++ {
//			if CCPoint[ivar] >= lp.LP.Cols[ivar].BndLo-featol {
//				// greater than lower bound
//				if CCPoint[ivar] <= lp.LP.Cols[ivar].BndUp+featol {
//					// less than upper bound
//					continue
//				} else if CCPoint[ivar]-lp.LP.Cols[ivar].BndUp > Alpha { // upper bound violated by large enough amount
//					NINF++
//					NumViol[ivar]++
//					SumViol[ivar] = SumViol[ivar] + lp.LP.Cols[ivar].BndUp - CCPoint[ivar]
//				}
//			} else if lp.LP.Cols[ivar].BndLo-CCPoint[ivar] > Alpha { // lower bound violated by large enough amount
//				NINF++
//				NumViol[ivar]++
//				SumViol[ivar] = SumViol[ivar] + lp.LP.Cols[ivar].BndLo - CCPoint[ivar]
//			}
//		}
//
//		if NINF == 0 {
//			// Exit successfully
//			//test
//			fmt.Println("Exiting CCOriginal successfully after", itn, "iterations.")
//
//			return CCPoint, 0
//		}
//		// Calculate the feasibility vector and it's length
//		rhold = 0.0 // Accumulates the squared elements of the consensus vector
//		for ivar := 0; ivar < lp.NumCols; ivar++ {
//			if NumViol[ivar] == 0 {
//				CV[ivar] = 0.0
//				continue
//			}
//			CV[ivar] = SumViol[ivar] / float64(NumViol[ivar])
//			rhold = rhold + CV[ivar]*CV[ivar]
//		}
//		// Check whether the consensus vector is too short
//
//		//test
//		//fmt.Println("In CCOriginal. CV:",CV)
//
//		if rhold < Beta*Beta {
//			return CCPoint, 2
//		}
//		// Update the point and continue
//		for ivar := 0; ivar < lp.NumCols; ivar++ {
//			CCPoint[ivar] = CCPoint[ivar] + CV[ivar]
//		}
//	}
//	// Too many iterations
//	return CCPoint, 1
//}

//==========================================================================================
//Parallel version of CCOriginal so it communicates via channels instead of returning values
func CCOriginal1(PointIn []float64, chPoint chan []float64, PointID int) {

	var NINF int = 0 // Number of violated constraints
	//var SINF float64 = 0.0                           // Sum of LHS-RHS violations
	var SFD float64 = 0.0 // Sum of the feasibility distance vectors
	//	var SFDLast float64	// Sum of the feasibility distances in the last CC iteration
	var Violation float64                            // The constraint violation
	var FVLength float64                             // Length of the feasibility vector
	NumViol := make([]int, len(PointIn))             // Number of violations
	SumViol := make([]float64, len(PointIn))         // Sum of violations (in terms of feasibility vector components)
	SumWeightedViol := make([]float64, len(PointIn)) // Sum of the weighted violations (weighted by violation)
	SumWeights := make([]float64, len(PointIn))      // Sum of the weights
	CCPoint := make([]float64, len(PointIn))         // Constraint consensus point
	CV := make([]float64, len(PointIn))              // Consensus Vector
	BestPt := make([]float64, len(PointIn))          // The best point seen in this CC run
	var BestPtSFD float64 = plinfy
	FVMaxViol := make([]float64, len(PointIn))     // Captures the individual feasibility vector associated with the maximum LHS-RHS violation
	FVMaxFVLength := make([]float64, len(PointIn)) // Captures the individual feasibility vector associated with the largest feasibility vector
	var MaxViol float64                            // Captures the maximum LHS-RHS violation seen
	var MaxFVLength float64                        // Catures the maximum feasibility vector length seen
	var NewMaxViol bool                            // Boolean to notice when a larger MaxViol is seen
	var NewMaxFVLength bool                        // Boolean to notice when a large MaxFVLength is seen
	var Status int
	var FVStatus int = 0
	var ViolStatus int = 0
	var ElNum int  // Element number
	var ColNum int // Column number
	var rhold, rhold1 float64
	var CVLength float64
	var CVLengthLast float64
	//	var MaxMultiplier float64
	//	var NumMultipliers int
	//	var FDFar bool = false
	//var rhold1 float64

	//var Status int = 0

	//test
	//fmt.Println("In CCOriginal. MaxItns:",MaxItns)

	//Status=0
	//defer WG.Done()
	copy(CCPoint, PointIn)
	for itn := 0; itn < MaxItns; itn++ {
		// Zero the accumulators
		NINF = 0
		SFD = 0.0
		MaxViol = -plinfy
		MaxFVLength = -plinfy
		for i := range PointIn {
			NumViol[i] = 0
			SumViol[i] = 0.0
			CV[i] = 0.0
			FVMaxViol[i] = 0.0
			FVMaxFVLength[i] = 0.0
			SumWeightedViol[i] = 0.0
			SumWeights[i] = 0.0
		}

		// Run through the constraints
		for icon := 0; icon < lp.NumRows; icon++ {
			// Get the feasibility vector, if there is one

			//test
			if math.IsNaN(CCPoint[0]) {
				fmt.Println("***1 GetViolation called with NaN CCPoint, line 307 in CCOriginal1 at itn", itn)
				//os.Exit(1)}
			}
			FVStatus, ViolStatus, Violation = GetViolation(icon, CCPoint)

			//test
			//fmt.Println("After GetViolation call for con",icon,"Violation:",Violation,"FVStatus:",FVStatus,"ViolStatus:",ViolStatus)

			if FVStatus > 0 {
				fmt.Println("Error evaluating feasibility status for constraint", icon, ". Skipping it.")
				continue
			}
			if ViolStatus > 0 {
				// not violated, so skip
				continue
			}
			// Check length of feasibility vector
			rhold = 0.0 // Accumulates length of feasibility vector
			for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
				ElNum = lp.LP.Rows[icon].ElList[iel]
				ColNum = lp.Element[ElNum].Col
				rhold1 = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
				rhold = rhold + rhold1*rhold1
			}
			if rhold < Alpha*Alpha {
				// Feasibility vector is too short so skip this constraint
				continue
			}
			FVLength = math.Sqrt(rhold)
			SFD = SFD + FVLength

			//			// Instead of classing a constraint as violated if the feasibility vector is too long,
			//			// use the classical LHS-RHS violation tolerance
			//			if math.Abs(Violation) <= featol {
			//				continue
			//			}

			// Constraint is violated
			NINF++
			// If using SINF
			NewMaxViol = false
			if math.Abs(Violation) > MaxViol {
				// There's a new maximum violation
				MaxViol = math.Abs(Violation)
				NewMaxViol = true
				// Empty the old FVMaxViol vector, fill it in the following step
				for j := 0; j < lp.LP.NumCols; j++ {
					FVMaxViol[j] = 0.0
				}
			}
			// If using SFD
			NewMaxFVLength = false
			if FVLength > MaxFVLength {
				// There is a new longest feasibility vector
				MaxFVLength = FVLength
				NewMaxFVLength = true
				// Empty the old FVMaxFVLength, fill it in the next step
				for j := 0; j < lp.NumCols; j++ {
					FVMaxFVLength[j] = 0.0
				}
			}

			// Calculate the relevant elements of the feasibility vector
			for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
				ElNum = lp.LP.Rows[icon].ElList[iel]
				ColNum = lp.Element[ElNum].Col
				NumViol[ColNum]++
				SumViol[ColNum] = SumViol[ColNum] + Violation*lp.Element[ElNum].Value/lp.LP.Rows[icon].GradVecLenSq
				SumWeightedViol[ColNum] = SumWeightedViol[ColNum] + Violation*lp.Element[ElNum].Value/lp.LP.Rows[icon].GradVecLenSq*math.Abs(Violation)
				SumWeights[ColNum] = SumWeights[ColNum] + math.Abs(Violation)
				if NewMaxViol {
					FVMaxViol[ColNum] = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
				}
				if NewMaxFVLength {
					FVMaxFVLength[ColNum] = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
				}
			}
		}

		// Run through the bounds looking for violations and making appropriate updates
		for ivar := 0; ivar < lp.NumCols; ivar++ {
			if CCPoint[ivar] >= lp.LP.Cols[ivar].BndLo-Alpha {
				// greater than lower bound
				if CCPoint[ivar] <= lp.LP.Cols[ivar].BndUp+Alpha {
					// less than upper bound
					continue
				} else if CCPoint[ivar]-lp.LP.Cols[ivar].BndUp > Alpha {
					// upper bound violated by large enough amount
					NINF++
					NumViol[ivar]++
					rhold = lp.LP.Cols[ivar].BndUp - CCPoint[ivar]
					SumViol[ivar] = SumViol[ivar] + rhold
					SFD = SFD + math.Abs(rhold)
					SumWeightedViol[ivar] = SumViol[ivar]
					SumWeights[ivar] = SumWeights[ivar] + rhold

					if CCPoint[ivar]-lp.LP.Cols[ivar].BndUp > MaxViol {
						// There's a new maximum violation
						MaxViol = CCPoint[ivar] - lp.LP.Cols[ivar].BndUp
						// Empty the old FVMaxViol vector, fill it in the following step
						for j := 0; j < lp.LP.NumCols; j++ {
							FVMaxViol[j] = 0.0
						}
						FVMaxViol[ivar] = lp.LP.Cols[ivar].BndUp - CCPoint[ivar]
					}
					if math.Abs(rhold) > MaxFVLength {
						// There's a new longest FV
						MaxFVLength = math.Abs(rhold)
						// Empty the old FVMaxFVLength and fill it in following step
						for j := 0; j < lp.NumCols; j++ {
							FVMaxFVLength[j] = 0.0
						}
						FVMaxFVLength[ivar] = lp.LP.Cols[ivar].BndUp - CCPoint[ivar]
					}

				}
			} else if lp.LP.Cols[ivar].BndLo-CCPoint[ivar] > Alpha {
				// lower bound violated by large enough amount
				NINF++
				NumViol[ivar]++
				rhold = lp.LP.Cols[ivar].BndLo - CCPoint[ivar]
				SumViol[ivar] = SumViol[ivar] + rhold
				SFD = SFD + rhold
				SumWeightedViol[ivar] = SumViol[ivar]
				SumWeights[ivar] = SumWeights[ivar] + lp.LP.Cols[ivar].BndLo - CCPoint[ivar]

				if lp.LP.Cols[ivar].BndLo-CCPoint[ivar] > MaxViol {
					// There's a new maximum violation
					MaxViol = lp.LP.Cols[ivar].BndLo - CCPoint[ivar]
					// Empty the old FVMaxViol vector, fill it in the following step
					for j := 0; j < lp.LP.NumCols; j++ {
						FVMaxViol[j] = 0.0
					}
					FVMaxViol[ivar] = lp.LP.Cols[ivar].BndLo - CCPoint[ivar]
				}
				if rhold > MaxFVLength {
					// There's a new longest FV
					MaxFVLength = rhold
					//Empty the old FVMaxFVLength and fill it in the following step
					for j := 0; j < lp.NumCols; j++ {
						FVMaxFVLength[j] = 0.0
					}
					FVMaxFVLength[ivar] = rhold
				}

			}
		}

		if NINF == 0 {
			// Exit successfully
			if PrintLevel > 0 {
				fmt.Println("CC exiting successfully after", itn, "iterations. Started at point type", PointID)
			}

			//test: check versus the usual LHS-RHS exit conditions
			//_, NINF, _, _, SINF, MaxViol, AvgViol := TestPoint(CCPoint)
			//fmt.Println("    NINF:", NINF, "SINF:", SINF, "MaxViol:", MaxViol, "AvgViol:", AvgViol)
			FinalPointType = PointID
			chPoint <- CCPoint //status was 0
			return
		}
		// Calculate the consensus vector vector and it's length
		rhold = 0.0 // Accumulates the squared elements of the consensus vector
		for ivar := 0; ivar < lp.NumCols; ivar++ {
			if NumViol[ivar] == 0 {
				CV[ivar] = 0.0
				continue
			}
			CV[ivar] = SumViol[ivar] / float64(NumViol[ivar]) // For standard basic CC
			//CV[ivar] = SumViol[ivar] // For the SUM method
			// CV[ivar] = SumWeightedViol[ivar] / SumWeights[ivar] // For violation-weighted CC
			rhold = rhold + CV[ivar]*CV[ivar]
		}
		CVLength = math.Sqrt(rhold)

		// Check relative size of SFD vs. last iteration
		//		if itn > 0 {
		//			if SFD > SFDLast {fmt.Println(PointID,itn, "Point SFD has increased from",SFDLast,"to",SFD)}
		//			if SFD == SFDLast {fmt.Println(PointID,itn,"Point SFD stalled at",SFD)}
		//		}

		// Is this the best point seen yet? If so, remember it
		if SFD < BestPtSFD {
			BestPtSFD = SFD
			copy(BestPt, CCPoint)
		}

		// Try projecting the point.
		//TEST: turning this off
		//Status, CCPoint = Project(CCPoint, CV)
		Status=2
		
		if Status == 1 {
			// Feasible point found
			if PrintLevel > 0 {
				fmt.Println("CC on point type", PointID, "finds feasible solution during projection at iteration", itn)
			}
			FinalPointType = PointID
			chPoint <- CCPoint
			//WG.Done()
			return
		}
		
		if Status > 1 {
			// Projection failed, so apply the consensus vector to update the point
			// Check whether the consensus vector is too short
			//FDFar = false
			if itn > 0 && (CVLength < Beta || CVLength/CVLengthLast > 1.0) {
				//if rhold < 0.001 {
				// Consensus vector is too short
				//fmt.Println("CC: consensus vector too short after", itn, "iterations.")
				//chPoint <- CCPoint // status was
				// NEW: if CV too short, then substitute the FV vector from the maximum violation
				//				fmt.Println(PointID, itn, "CV too short or length ratio too high: substituting FV for most violated constraint")
				//fmt.Println("CV too short or CV length ratio too large at itn",itn)
				// SINF vs. SFD
				//copy(CV, FVMaxViol)
				//copy(CV, FVMaxFVLength)
				//This version imposes the longest FV vector onto the overall CV
				for ivar := 0; ivar < lp.NumCols; ivar++ {
					if FVMaxFVLength[ivar] != 0.0 {
						CV[ivar] = FVMaxFVLength[ivar]
					}
				}
				//			FDFar = true
			}

			// convert to FDfar by overwriting elements of the consensus vector by the elements
			// of the FVMaxViol
			//		for ivar:=0; ivar<lp.NumCols; ivar++ {
			//			if FVMaxViol[ivar] != 0.0 {CV[ivar] = FVMaxViol[ivar]}
			//		}

			// Now that the CV is known we can do an augmentation step. We are looking for the
			// largest (or average) multiplier to apply to the CV.
			// Reuse SumViol to stand in for X1

			//		for ivar := 0; ivar < lp.NumCols; ivar++ {
			//			SumViol[ivar] = CCPoint[ivar] + CV[ivar]
			//		}
			//		NumMultipliers = 0
			//		MaxMultiplier = 0.0
			//		for icon:=0; icon<lp.NumRows; icon++ {
			//			ViolStatus, rhold = GetMultiplier(CCPoint, SumViol, icon, 0)
			//			if ViolStatus > 0 {continue}
			//			NumMultipliers++
			//			MaxMultiplier = MaxMultiplier + rhold
			//			//if rhold > MaxMultiplier {MaxMultiplier = rhold}
			//		}
			//		for ivar:=0; ivar<lp.NumCols; ivar++ {
			//			ViolStatus, rhold = GetMultiplier(CCPoint, SumViol, ivar, 1)
			//			if ViolStatus > 0 {continue}
			//			NumMultipliers++
			//			MaxMultiplier = MaxMultiplier + rhold
			//			//if rhold > MaxMultiplier {MaxMultiplier = rhold}
			//		}
			//		MaxMultiplier = MaxMultiplier / float64(NumMultipliers) // the average version
			//		if MaxMultiplier < 1.0 {MaxMultiplier = 1.0}
			//		if MaxMultiplier > 1000.0 {MaxMultiplier = 1000.0}
			//		if CVLength >1000.0 {
			//			MaxMultiplier = 1.0
			//		}
			//		if CVLength*MaxMultiplier > 1e6 {fmt.Println("CVLength * MaxMultiplier is large:",CVLength*MaxMultiplier)}
			//		//test
			//		if math.IsNaN(MaxMultiplier) {fmt.Println("Multiplier is NaN at CC iteration", itn)}

			// Update the point and continue
			for ivar := 0; ivar < lp.NumCols; ivar++ {
				CCPoint[ivar] = CCPoint[ivar] + CV[ivar] //* MaxMultiplier
			}
		}
		
		// try enforcing the variable bounds
		//CCPoint = EnforceBounds(CCPoint)

		//		if itn > 0 && !FDFar && CVLength/CVLengthLast > 1.0 {
		//			fmt.Println("CV Length not improving. Bailing out at CC itn",itn,"on point",PointID)
		//			_,SFD,_,_,_,NINF = GetSFD(CCPoint)
		//			_ = UpdateIncumbentSFD(CCPoint, SFD, NINF, PointID)
		//			chPoint <- CCPoint //status was 0
		//			return
		//		}
		CVLengthLast = CVLength
		//		SFDLast = SFD

	} // End of loop on CC iterations

	// Too many iterations
	//fmt.Println("CC: too many iterations (", MaxItns, "). Exiting.")

	//SINF vs. SFD
	//	Status, NINF, _, _, SINF, _, _ = TestPoint(CCPoint)
	//
	//	//test: TODO deal with bad point properly
	//	if Status > 0 {
	//		fmt.Println("***TestPoint Status > 0 after call in CCOriginal1.")
	//	}

	//	Status = UpdateIncumbent(CCPoint, SINF, NINF, PointID)

	_ = UpdateIncumbentSFD(CCPoint, SFD, NINF, PointID)
	//	_ = UpdateIncumbents(CCPoint, SFD, SINF, NINF, PointID

	//chPoint <- CCPoint
	chPoint <- BestPt
	//WG.Done()
	return
}

//==========================================================================================
// Parallel version of CCOriginal so it communicates via channels instead of returning values
// This version calls GetCV1 and can adjust the type of CV used depending on various factors
// such as the Round and the PointID
func CCOriginal2(PointIn []float64, chPoint chan []float64, Round int, PointID int) {

	var NINF int = 0 // Number of violated constraints
	//var SINF float64 = 0.0                           // Sum of LHS-RHS violations
	var SFD float64 = 0.0 // Sum of the feasibility distance vectors
	//	var SFDLast float64	// Sum of the feasibility distances in the last CC iteration
	//var Violation float64                            // The constraint violation
	//var FVLength float64                             // Length of the feasibility vector
	//NumViol := make([]int, len(PointIn))             // Number of violations
	//SumViol := make([]float64, len(PointIn))         // Sum of violations (in terms of feasibility vector components)
	//SumWeightedViol := make([]float64, len(PointIn)) // Sum of the weighted violations (weighted by violation)
	//SumWeights := make([]float64, len(PointIn))      // Sum of the weights
	CCPoint := make([]float64, len(PointIn)) // Constraint consensus point
	CV := make([]float64, len(PointIn))      // Consensus Vector
	CV1 := make([]float64, len(PointIn))     // Alternate Consensus Vector
	BestPt := make([]float64, len(PointIn))  // The best point seen in this CC run
	var BestPtSFD float64 = plinfy
	//FVMaxViol := make([]float64, len(PointIn))     // Captures the individual feasibility vector associated with the maximum LHS-RHS violation
	//FVMaxFVLength := make([]float64, len(PointIn)) // Captures the individual feasibility vector associated with the largest feasibility vector
	//var MaxViol float64                            // Captures the maximum LHS-RHS violation seen
	//var MaxFVLength float64                        // Catures the maximum feasibility vector length seen
	//var NewMaxViol bool                            // Boolean to notice when a larger MaxViol is seen
	//var NewMaxFVLength bool                        // Boolean to notice when a large MaxFVLength is seen
	var Status int
	//var FVStatus int = 0
	//var ViolStatus int = 0
	//var ElNum int  // Element number
	//var ColNum int // Column number
	var rhold float64
	var CVLength float64
	var CVLengthLast float64
	var CVShort bool //notes whether the returned CV is too short

	copy(CCPoint, PointIn)
	for itn := 0; itn < MaxItns; itn++ {

		if Round == 0 {
			Status, CV, _, _, _, CVShort, _, _, _, SFD, _, NINF = GetCV1(CCPoint)
		} else {
			if PointID == 0 || PointID > 3 { // Normal CV
				Status, CV, CV1, _, _, CVShort, _, _, _, SFD, _, NINF = GetCV1(CCPoint)
			}
			if PointID == 1 { // Normal CV with longest FV imposed
				Status, _, CV, _, _, _, CVShort, _, _, SFD, _, NINF = GetCV1(CCPoint)
			}
			if PointID == 2 { // CV weighted by infeas vector lengths
				Status, _, CV1, CV, _, _, _, CVShort, _, SFD, _, NINF = GetCV1(CCPoint)
			}
			if PointID == 3 { // SUM method
				Status, _, CV1, _, CV, _, _, _, CVShort, SFD, _, NINF = GetCV1(CCPoint)
			}
		}

		if Status == 2 {
			fmt.Println("Error obtaining CV at iteration", itn, ". Aborting the CC run.")
			chPoint <- CCPoint
			return
		}

		if Status == 1 || NINF == 0 {
			// Exit successfully
			if PrintLevel > 0 {
				fmt.Println("CC exiting successfully after", itn, "iterations. Started at point type", PointID)
			}

			//test: check versus the usual LHS-RHS exit conditions
			//_, NINF, _, _, SINF, MaxViol, AvgViol := TestPoint(CCPoint)
			//fmt.Println("    NINF:", NINF, "SINF:", SINF, "MaxViol:", MaxViol, "AvgViol:", AvgViol)
			FinalPointType = PointID
			chPoint <- CCPoint //status was 0
			return
		}

		// Is this the best point seen yet? If so, remember it
		if SFD < BestPtSFD {
			BestPtSFD = SFD
			copy(BestPt, CCPoint)
		}

		// Try projecting the point.
		Status, CCPoint = Project(CCPoint, CV)
		if Status == 1 {
			// Feasible point found
			if PrintLevel > 0 {
				fmt.Println("CC on point type", PointID, "finds feasible solution during projection at iteration", itn)
			}
			FinalPointType = PointID
			chPoint <- CCPoint
			//WG.Done()
			return
		}
		if Status > 1 {
			// Projection failed, so apply the consensus vector to update the point
			// First calculate and check length of consensus vector
			rhold = 0.0
			for i := 0; i < lp.NumCols; i++ {
				rhold = rhold + CV[i]*CV[i]
			}
			CVLength = math.Sqrt(rhold)

			if itn > 0 && (CVShort || CVLength/CVLengthLast > 1.0) {
				copy(CV, CV1)
			}

			// Update the point and continue
			for ivar := 0; ivar < lp.NumCols; ivar++ {
				CCPoint[ivar] = CCPoint[ivar] + CV[ivar]
			}
		}

		CVLengthLast = CVLength

	} // End of loop on CC iterations

	_ = UpdateIncumbentSFD(CCPoint, SFD, NINF, PointID)

	chPoint <- BestPt

	return
}
//==========================================================================================
//Parallel version of CCOriginal so it communicates via channels instead of returning values.
//This version superimposes the FV that has the most impact on top of the consensus CV.
//"Most impact" means the row constraint has the largest sum of votes for variables that
//it contains
func CCImpact(PointIn []float64, chPoint chan []float64, PointID int) {

	var NINF int = 0 // Number of violated constraints
	//var SINF float64 = 0.0                           // Sum of LHS-RHS violations
	var SFD float64 = 0.0 // Sum of the feasibility distance vectors
	//	var SFDLast float64	// Sum of the feasibility distances in the last CC iteration
	var Violation float64                            // The constraint violation
	var FVLength float64                             // Length of the feasibility vector
	NumViol := make([]int, len(PointIn))             // Number of violations
	SumViol := make([]float64, len(PointIn))         // Sum of violations (in terms of feasibility vector components)
	SumWeightedViol := make([]float64, len(PointIn)) // Sum of the weighted violations (weighted by violation)
	SumWeights := make([]float64, len(PointIn))      // Sum of the weights
	CCPoint := make([]float64, len(PointIn))         // Constraint consensus point
	CV := make([]float64, len(PointIn))              // Consensus Vector
	CVImpact := make([]float64, len(PointIn))	// Max impact FV imposed on regular CV
	BestPt := make([]float64, len(PointIn))          // The best point seen in this CC run
	var BestPtSFD float64 = plinfy
	FVMaxViol := make([]float64, len(PointIn))     // Captures the individual feasibility vector associated with the maximum LHS-RHS violation
	FVMaxFVLength := make([]float64, len(PointIn)) // Captures the individual feasibility vector associated with the largest feasibility vector
	ConViolated := make([]bool, lp.NumRows)		// Status of row constraints. false(nonbinding or not violated), true(violated)
	var ImpactCon int	// Row number of highest impact row constraint
	var MaxViol float64                            // Captures the maximum LHS-RHS violation seen
	var MaxFVLength float64                        // Catures the maximum feasibility vector length seen
	var NewMaxViol bool                            // Boolean to notice when a larger MaxViol is seen
	var NewMaxFVLength bool                        // Boolean to notice when a large MaxFVLength is seen
	var Status int
	var FVStatus int = 0
	var ViolStatus int = 0
	var ElNum int  // Element number
	var ColNum int // Column number
	var rhold, rhold1 float64
	var ihold, ihold1 int
	var CVLength float64
	var CVImpactLength float64
	var CVLengthLast float64

	copy(CCPoint, PointIn)
	for itn := 0; itn < MaxItns; itn++ {
		// Zero the accumulators
		NINF = 0
		SFD = 0.0
		MaxViol = -plinfy
		MaxFVLength = -plinfy
		for i := range PointIn {
			NumViol[i] = 0
			SumViol[i] = 0.0
			CV[i] = 0.0
			FVMaxViol[i] = 0.0
			FVMaxFVLength[i] = 0.0
			SumWeightedViol[i] = 0.0
			SumWeights[i] = 0.0
		}

		// Run through the constraints
		for icon := 0; icon < lp.NumRows; icon++ {
			// Get the feasibility vector, if there is one

			//test
			if math.IsNaN(CCPoint[0]) {
				fmt.Println("***1 GetViolation called with NaN CCPoint, line 307 in CCOriginal1 at itn", itn)
				//os.Exit(1)}
			}
			FVStatus, ViolStatus, Violation = GetViolation(icon, CCPoint)

			//test
			//fmt.Println("After GetViolation call for con",icon,"Violation:",Violation,"FVStatus:",FVStatus,"ViolStatus:",ViolStatus)

			if FVStatus > 0 {
				fmt.Println("Error evaluating feasibility status for constraint", icon, ". Skipping it.")
				continue
			}
			if ViolStatus > 0 {
				// not violated, so skip
				ConViolated[icon] = false
				continue
			}
			// Check length of feasibility vector
			rhold = 0.0 // Accumulates length of feasibility vector
			for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
				ElNum = lp.LP.Rows[icon].ElList[iel]
				ColNum = lp.Element[ElNum].Col
				rhold1 = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
				rhold = rhold + rhold1*rhold1
			}
			if rhold < Alpha*Alpha {
				// Feasibility vector is too short so skip this constraint
				ConViolated[icon] = false
				continue
			}
			
			// Constraint is violated
			ConViolated[icon] = true
			FVLength = math.Sqrt(rhold)
			SFD = SFD + FVLength
			NINF++
			// If using SINF
			NewMaxViol = false
			if math.Abs(Violation) > MaxViol {
				// There's a new maximum violation
				MaxViol = math.Abs(Violation)
				NewMaxViol = true
				// Empty the old FVMaxViol vector, fill it in the following step
				for j := 0; j < lp.LP.NumCols; j++ {
					FVMaxViol[j] = 0.0
				}
			}
			// If using SFD
			NewMaxFVLength = false
			if FVLength > MaxFVLength {
				// There is a new longest feasibility vector
				MaxFVLength = FVLength
				NewMaxFVLength = true
				// Empty the old FVMaxFVLength, fill it in the next step
				for j := 0; j < lp.NumCols; j++ {
					FVMaxFVLength[j] = 0.0
				}
			}

			// Calculate the relevant elements of the feasibility vector
			for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
				ElNum = lp.LP.Rows[icon].ElList[iel]
				ColNum = lp.Element[ElNum].Col
				NumViol[ColNum]++
				SumViol[ColNum] = SumViol[ColNum] + Violation*lp.Element[ElNum].Value/lp.LP.Rows[icon].GradVecLenSq
				SumWeightedViol[ColNum] = SumWeightedViol[ColNum] + Violation*lp.Element[ElNum].Value/lp.LP.Rows[icon].GradVecLenSq*math.Abs(Violation)
				SumWeights[ColNum] = SumWeights[ColNum] + math.Abs(Violation)
				if NewMaxViol {
					FVMaxViol[ColNum] = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
				}
				if NewMaxFVLength {
					FVMaxFVLength[ColNum] = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
				}
			}
		}

		// Run through the bounds looking for violations and making appropriate updates
		for ivar := 0; ivar < lp.NumCols; ivar++ {
			if CCPoint[ivar] >= lp.LP.Cols[ivar].BndLo-Alpha {
				// greater than lower bound
				if CCPoint[ivar] <= lp.LP.Cols[ivar].BndUp+Alpha {
					// less than upper bound
					continue
				} else if CCPoint[ivar]-lp.LP.Cols[ivar].BndUp > Alpha {
					// upper bound violated by large enough amount
					NINF++
					NumViol[ivar]++
					rhold = lp.LP.Cols[ivar].BndUp - CCPoint[ivar]
					SumViol[ivar] = SumViol[ivar] + rhold
					SFD = SFD + math.Abs(rhold)
					SumWeightedViol[ivar] = SumViol[ivar]
					SumWeights[ivar] = SumWeights[ivar] + rhold

					if CCPoint[ivar]-lp.LP.Cols[ivar].BndUp > MaxViol {
						// There's a new maximum violation
						MaxViol = CCPoint[ivar] - lp.LP.Cols[ivar].BndUp
						// Empty the old FVMaxViol vector, fill it in the following step
						for j := 0; j < lp.LP.NumCols; j++ {
							FVMaxViol[j] = 0.0
						}
						FVMaxViol[ivar] = lp.LP.Cols[ivar].BndUp - CCPoint[ivar]
					}
					if math.Abs(rhold) > MaxFVLength {
						// There's a new longest FV
						MaxFVLength = math.Abs(rhold)
						// Empty the old FVMaxFVLength and fill it in following step
						for j := 0; j < lp.NumCols; j++ {
							FVMaxFVLength[j] = 0.0
						}
						FVMaxFVLength[ivar] = lp.LP.Cols[ivar].BndUp - CCPoint[ivar]
					}

				}
			} else if lp.LP.Cols[ivar].BndLo-CCPoint[ivar] > Alpha {
				// lower bound violated by large enough amount
				NINF++
				NumViol[ivar]++
				rhold = lp.LP.Cols[ivar].BndLo - CCPoint[ivar]
				SumViol[ivar] = SumViol[ivar] + rhold
				SFD = SFD + rhold
				SumWeightedViol[ivar] = SumViol[ivar]
				SumWeights[ivar] = SumWeights[ivar] + lp.LP.Cols[ivar].BndLo - CCPoint[ivar]

				if lp.LP.Cols[ivar].BndLo-CCPoint[ivar] > MaxViol {
					// There's a new maximum violation
					MaxViol = lp.LP.Cols[ivar].BndLo - CCPoint[ivar]
					// Empty the old FVMaxViol vector, fill it in the following step
					for j := 0; j < lp.LP.NumCols; j++ {
						FVMaxViol[j] = 0.0
					}
					FVMaxViol[ivar] = lp.LP.Cols[ivar].BndLo - CCPoint[ivar]
				}
				if rhold > MaxFVLength {
					// There's a new longest FV
					MaxFVLength = rhold
					//Empty the old FVMaxFVLength and fill it in the following step
					for j := 0; j < lp.NumCols; j++ {
						FVMaxFVLength[j] = 0.0
					}
					FVMaxFVLength[ivar] = rhold
				}
			}
		}

		if NINF == 0 {
			// Exit successfully
			if PrintLevel > 0 {
				fmt.Println("CC exiting successfully after", itn, "iterations. Started at point type", PointID)
			}
			FinalPointType = PointID
			chPoint <- CCPoint //status was 0
			return
		}
		// Calculate the consensus vector vector and it's length
		rhold = 0.0 // Accumulates the squared elements of the consensus vector
		for ivar := 0; ivar < lp.NumCols; ivar++ {
			if NumViol[ivar] == 0 {
				CV[ivar] = 0.0
				continue
			}
			CV[ivar] = SumViol[ivar] / float64(NumViol[ivar]) // For standard basic CC
			//CV[ivar] = SumViol[ivar] // For the SUM method
			// CV[ivar] = SumWeightedViol[ivar] / SumWeights[ivar] // For violation-weighted CC
			rhold = rhold + CV[ivar]*CV[ivar]
		}
		CVLength = math.Sqrt(rhold)

		// Is this the best point seen yet? If so, remember it
		if SFD < BestPtSFD {
			BestPtSFD = SFD
			copy(BestPt, CCPoint)
		}
		
		// Identify the highest impact feasibility vector
		ihold = 0; ihold1 = -1; ImpactCon = -1
		for ii:=0; ii<lp.NumRows; ii++ {
			if ConViolated[ii] {
				ihold = 0
				for jj:=0; jj<lp.LP.Rows[ii].NumEl; jj++ {
					iel:=lp.LP.Rows[ii].ElList[jj]
					ivarb:=lp.Element[iel].Col
					ihold = ihold + NumViol[ivarb]
				}
				if ihold > ihold1 {
					// This constraint has a larger sum of violation votes
					ihold1 = ihold
					ImpactCon = ii
				}
			}
		}
		// Now creat CV1, which overwrites the CV with the highest impact FV terms
		copy(CVImpact, CV) 
		if ImpactCon > -1 {
			FVStatus, ViolStatus, Violation = GetViolation(ImpactCon, CCPoint)
			for iel := 0; iel < lp.LP.Rows[ImpactCon].NumEl; iel++ {
				ElNum = lp.LP.Rows[ImpactCon].ElList[iel]
				ColNum = lp.Element[ElNum].Col
				CVImpact[ColNum] = Violation * lp.Element[ElNum].Value / lp.LP.Rows[ImpactCon].GradVecLenSq
			}
			//test
			//fmt.Println("Highest impact constraint at iteration",itn,"is",ImpactCon)
			// Recalculate CV length
			rhold = 0.0 // Accumulates the squared elements of the consensus vector
			for ivar := 0; ivar < lp.NumCols; ivar++ {
				rhold = rhold + CVImpact[ivar]*CVImpact[ivar]
			}
			CVImpactLength = math.Sqrt(rhold)
		}

		// Try projecting the point.
		Status, CCPoint = Project(CCPoint, CV)
		if Status == 1 {
			// Feasible point found
			if PrintLevel > 0 {
				fmt.Println("CC on point type", PointID, "finds feasible solution during projection at iteration", itn)
			}
			FinalPointType = PointID
			chPoint <- CCPoint
			//WG.Done()
			return
		}
		if Status > 1 {
			// Projection failed, so apply the consensus vector to update the point
			// Check whether the consensus vector is too short
			//fmt.Println("Using max impact at iteration", itn)
			
			if itn > 0 && (CVLength < Beta || CVLength/CVLengthLast > 1.0) {
				// Use the max impact version of the CV
				copy(CV, CVImpact)
				CVLength = CVImpactLength
			}

			// Update the point and continue
			for ivar := 0; ivar < lp.NumCols; ivar++ {
				CCPoint[ivar] = CCPoint[ivar] + CV[ivar] //* MaxMultiplier
			}
		}
		
		CVLengthLast = CVLength

	} // End of loop on CC iterations

	_ = UpdateIncumbentSFD(CCPoint, SFD, NINF, PointID)
	
	chPoint <- CCPoint
	//chPoint <- BestPt
	
	return
}
//==========================================================================================
// This version of CC runs a sequential CC method that first puts the point back inside the
// variable bounds, and then runs sequentially through the row constraints in order from
// most to least impact.
func CCSeqImpact(PointIn []float64, chPoint chan []float64, PointID int) {

	var NINF int = 0 // Number of violated constraints
	var SFD float64 = 0.0 // Sum of the feasibility distance vectors
	var Violation float64                            // The constraint violation
	var FVLength float64                             // Length of the feasibility vector
	CCPoint := make([]float64, len(PointIn))         // Constraint consensus point
	BestPt := make([]float64, len(PointIn))          // The best point seen in this CC run
	var BestPtSFD float64 = plinfy
	var MaxFVLength float64                        // Catures the maximum feasibility vector length seen
	var FVStatus int = 0
	var ViolStatus int = 0
	var ElNum int  // Element number
	var ColNum int // Column number
	var icon int // Constraint number
	var rhold, rhold1 float64

	copy(CCPoint, PointIn)
	
	// Run through the CC iterations
	for itn:=0; itn<MaxItns; itn++ {
	
		// Zero the accumulators
		NINF = 0
		SFD = 0.0
		MaxFVLength = -plinfy
	
		// First adjust the point so that it satisfies all of the constraint bounds
		for j:=0; j<lp.NumCols; j++ {
			rhold = lp.LP.Cols[j].BndLo - CCPoint[j]
			if rhold > featol {
				CCPoint[j] = lp.LP.Cols[j].BndLo
				NINF++
				SFD = SFD + rhold
				if rhold > MaxFVLength {MaxFVLength = rhold}
				continue
			}
			rhold = CCPoint[j] - lp.LP.Cols[j].BndUp
			if rhold > featol {
				CCPoint[j] = lp.LP.Cols[j].BndUp
				NINF++
				SFD = SFD + rhold
				if rhold > MaxFVLength {MaxFVLength = rhold}
			}
		}
	
		// Run through the row constraints in impact order, applying the feasiblity
		// vectors as needed.

		for icon1 := 0; icon1 < lp.NumRows; icon1++ {
			icon = ImpactList[icon1]

			// Get the feasibility vector, if there is one
			FVStatus, ViolStatus, Violation = GetViolation(icon, CCPoint)
			if FVStatus > 0 {
				fmt.Println("Error evaluating feasibility status for constraint", icon, ". Skipping it.")
				continue
			}
			if ViolStatus > 0 {
				// not violated, so skip
				continue
			}
			// Check length of feasibility vector
			rhold = 0.0 // Accumulates length of feasibility vector
			for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
				ElNum = lp.LP.Rows[icon].ElList[iel]
				ColNum = lp.Element[ElNum].Col
				rhold1 = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
				rhold = rhold + rhold1*rhold1
			}
			if rhold < Alpha*Alpha {
				// Feasibility vector is too short so skip this constraint
				continue
			}
			FVLength = math.Sqrt(rhold)
			SFD = SFD + FVLength

			// Constraint is violated
			NINF++
			// If using SFD
			if FVLength > MaxFVLength {
				// There is a new longest feasibility vector
				MaxFVLength = FVLength
			}

			// Calculate the relevant elements of the feasibility vector
			for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
				ElNum = lp.LP.Rows[icon].ElList[iel]
				ColNum = lp.Element[ElNum].Col
				CCPoint[ColNum] = CCPoint[ColNum] + Violation*lp.Element[ElNum].Value/lp.LP.Rows[icon].GradVecLenSq
			}
		}

		// Check the result of this iteration
		if NINF == 0 {
			// Exit successfully
			if PrintLevel > 0 {
				fmt.Println("CC Sequential Impact exiting successfully after", itn, "iterations. Started at point type", PointID)
			}
			FinalPointType = PointID
			chPoint <- CCPoint //status was 0
			return
		}

		// Is this the best point seen yet? If so, remember it
		if SFD < BestPtSFD {
			BestPtSFD = SFD
			copy(BestPt, CCPoint)
		}
	} // End of loop on CC iterations

	_ = UpdateIncumbentSFD(CCPoint, SFD, NINF, PointID)
	//	_ = UpdateIncumbents(CCPoint, SFD, SINF, NINF, PointID

	//chPoint <- CCPoint
	chPoint <- BestPt
	//WG.Done()
	return
}
//==========================================================================================
// This version of CC does a single iteration before returning a new point.
func CCSimple(PointIn []float64, chPointData chan POINTDATA, PointID int) {

	var NINF int = 0 // Number of violated constraints
	//var SINF float64 = 0.0                           // Sum of LHS-RHS violations
	var SFD float64 = 0.0 // Sum of the feasibility distance vectors
	//	var SFDLast float64	// Sum of the feasibility distances in the last CC iteration
	var Violation float64                            // The constraint violation
	var FVLength float64                             // Length of the feasibility vector
	NumViol := make([]int, len(PointIn))             // Number of violations
	SumViol := make([]float64, len(PointIn))         // Sum of violations (in terms of feasibility vector components)
	SumWeightedViol := make([]float64, len(PointIn)) // Sum of the weighted violations (weighted by violation)
	SumWeights := make([]float64, len(PointIn))      // Sum of the weights
	CCPoint := make([]float64, len(PointIn))         // Constraint consensus point
	CV := make([]float64, len(PointIn))              // Consensus Vector

	FVMaxViol := make([]float64, len(PointIn))     // Captures the individual feasibility vector associated with the maximum LHS-RHS violation
	FVMaxFVLength := make([]float64, len(PointIn)) // Captures the individual feasibility vector associated with the largest feasibility vector
	var FVStatus int = 0
	var ViolStatus int = 0
	var ElNum int  // Element number
	var ColNum int // Column number
	var rhold, rhold1 float64

	var PointOut POINTDATA
	PointOut.Point = make([]float64, lp.NumCols)

	copy(CCPoint, PointIn)
	
	for itn:=0; itn<10; itn++ {
		// Zero the accumulators
		NINF = 0
		SFD = 0.0
		for i := range PointIn {
			NumViol[i] = 0
			SumViol[i] = 0.0
			CV[i] = 0.0
			FVMaxViol[i] = 0.0
			FVMaxFVLength[i] = 0.0
			SumWeightedViol[i] = 0.0
			SumWeights[i] = 0.0
		}
	
		// Run through the constraints
		for icon := 0; icon < lp.NumRows; icon++ {
			// Get the feasibility vector, if there is one
			FVStatus, ViolStatus, Violation = GetViolation(icon, CCPoint)
			if FVStatus > 0 {
				fmt.Println("Error evaluating feasibility status for constraint", icon, ". Skipping it.")
				continue
			}
			if ViolStatus > 0 {
				// not violated, so skip
				continue
			}
			// Check length of feasibility vector
			rhold = 0.0 // Accumulates length of feasibility vector
			for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
				ElNum = lp.LP.Rows[icon].ElList[iel]
				ColNum = lp.Element[ElNum].Col
				rhold1 = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
				rhold = rhold + rhold1*rhold1
			}
			if rhold < Alpha*Alpha {
				// Feasibility vector is too short so skip this constraint
				continue
			}
			FVLength = math.Sqrt(rhold)
			SFD = SFD + FVLength
	
			// Constraint is violated
			NINF++
	
			// Calculate the relevant elements of the feasibility vector
			for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
				ElNum = lp.LP.Rows[icon].ElList[iel]
				ColNum = lp.Element[ElNum].Col
				NumViol[ColNum]++
				SumViol[ColNum] = SumViol[ColNum] + Violation*lp.Element[ElNum].Value/lp.LP.Rows[icon].GradVecLenSq
				SumWeightedViol[ColNum] = SumWeightedViol[ColNum] + Violation*lp.Element[ElNum].Value/lp.LP.Rows[icon].GradVecLenSq*math.Abs(Violation)
				SumWeights[ColNum] = SumWeights[ColNum] + math.Abs(Violation)
			}
		}
	
		// Run through the bounds looking for violations and making appropriate updates
		for ivar := 0; ivar < lp.NumCols; ivar++ {
			if CCPoint[ivar] >= lp.LP.Cols[ivar].BndLo-Alpha {
				// greater than lower bound
				if CCPoint[ivar] <= lp.LP.Cols[ivar].BndUp+Alpha {
					// less than upper bound
					continue
				} else if CCPoint[ivar]-lp.LP.Cols[ivar].BndUp > Alpha {
					// upper bound violated by large enough amount
					NINF++
					NumViol[ivar]++
					rhold = lp.LP.Cols[ivar].BndUp - CCPoint[ivar]
					SumViol[ivar] = SumViol[ivar] + rhold
					SFD = SFD + math.Abs(rhold)
					SumWeightedViol[ivar] = SumViol[ivar]
					SumWeights[ivar] = SumWeights[ivar] + rhold
				}
			} else if lp.LP.Cols[ivar].BndLo-CCPoint[ivar] > Alpha {
				// lower bound violated by large enough amount
				NINF++
				NumViol[ivar]++
				rhold = lp.LP.Cols[ivar].BndLo - CCPoint[ivar]
				SumViol[ivar] = SumViol[ivar] + rhold
				SFD = SFD + rhold
				SumWeightedViol[ivar] = SumViol[ivar]
				SumWeights[ivar] = SumWeights[ivar] + lp.LP.Cols[ivar].BndLo - CCPoint[ivar]
			}
		}
	
		if NINF == 0 {
			// Exit successfully
			if PrintLevel > 0 {
				fmt.Println("CC exiting successfully.")
			}
	
			FinalPointType = PointID
			copy(PointOut.Point, CCPoint)
			PointOut.SFD = 0.0
			PointOut.NINF = 0
			
			chPointData <- PointOut //status was 0
			return
		}
		// Calculate the consensus vector vector and it's length
		rhold = 0.0 // Accumulates the squared elements of the consensus vector
		for ivar := 0; ivar < lp.NumCols; ivar++ {
			if NumViol[ivar] == 0 {
				CV[ivar] = 0.0
				continue
			}
			CV[ivar] = SumViol[ivar] / float64(NumViol[ivar]) // For standard basic CC
			rhold = rhold + CV[ivar]*CV[ivar]
		}
		
		// Update the point and continue
		for ivar := 0; ivar < lp.NumCols; ivar++ {
			CCPoint[ivar] = CCPoint[ivar] + CV[ivar] //* MaxMultiplier
			}
		_ = UpdateIncumbentSFD(CCPoint, SFD, NINF, PointID)	
	} // end of CC iteration loop
	
	copy(PointOut.Point, CCPoint)
	PointOut.SFD = SFD
	PointOut.NINF = NINF

	chPointData <- PointOut
	return
}

//========================================================================================
// The overall solution control routine. Must be called first to give global variables their values
// Status values: 0:(success), 1:(max iterations reached or failure), 2:(numerical problem)
func Solve(AlphaIn float64, BetaIn float64, MaxItnsIn int, MaxSwarmPtsIn int, plinfyIn float64, featolIn float64) (PointOut []float64, Status int) {

	// Set up the swarm of points and related info
	MaxSwarmPts = MaxSwarmPtsIn
	
	var SamplePt POINTDATA
	SamplePt.Point = make([]float64, lp.NumCols)
	M := make([]float64, lp.NumCols)
	Q := make([]float64, lp.NumCols)
	var MaxWidth, AvgWidth float64
	var rhold float64
	
	Swarm = make([][]float64, MaxSwarmPts)
	for i := 0; i < MaxSwarmPts; i++ {
		Swarm[i] = make([]float64, lp.NumCols)
	}
	SwarmMaxViol = make([]float64, MaxSwarmPts)
	SwarmSINF = make([]float64, MaxSwarmPts) // SINF at each of the swarm points
	SwarmSFD = make([]float64, MaxSwarmPts)  // sum of the feasibility distances at each of the swarm points
	IncumbentPt = make([]float64, lp.NumCols)
	//	IncumbentUp = make([]int, lp.NumCols)
	//	IncumbentDown = make([]int, lp.NumCols)
	//	IncumbentSame = make([]int, lp.NumCols)
	IncumbentSINF = math.MaxFloat64 // Initial huge value
	IncumbentSFD = math.MaxFloat64  // Initial huge value
	//IncumbentNINF = -1              // Initial impossible value
	IncumbentNINF = math.MaxInt32

	// To keep statistics on updates to the incumbent
	NumUpdate = make([]int, 23)
	FracUpdate = make([]float64, 23)

	// Set up box-related data structures
	BoxBndLo = make([]float64, lp.LP.NumCols) // Sample box lower bounds
	BoxBndUp = make([]float64, lp.LP.NumCols) // Sample box upper bounds

	// Initialize some package global variables
	FinalBox = -1
	FinalPointType = -1
	WorstNINF = 0
	WorstNINFel = -1
	SmallestNINF = math.MaxInt32
	TotUpdates = 0
	LinProjSucceeds = 0
	LinProjFails = 0
	LinProjFrac = 0.0
	QuadProjSucceeds = 0
	QuadProjFails = 0
	QuadProjFrac = 0.0
	FailedRounds = 0

	// Local variables
	//CCEndPt := make([]float64, lp.NumCols)
	var NINF, NumSat, NumTight int
	var SINF, MaxViol, AvgViol float64
//	var SFD float64
//	chPoint := make(chan []float64)
	chPointData := make(chan POINTDATA)
	
	var AvgSFD, LastAvgSFD float64
	var icount int
	
	var NumCCRuns int = 0 // counts the number of CC runs that complete (some runs killed if soln found)
	//	var SomeIdentical bool
	var MaxBoxes int = 100 // The maximum number of sample boxes. TODO: pass in as proper control parameter

	//test
	//fmt.Println("In solve: CC end pt after initial definition:",CCEndPt)

	Alpha = AlphaIn
	Beta = BetaIn
	MaxItns = MaxItnsIn
	plinfy = plinfyIn
	featol = featolIn

	// test: just to satisfy the compiler that these variables are used
	NINF = NINF + 0
	NumSat = NumSat + 0
	NumTight = NumTight + 0
	SINF = SINF + 0.0
	MaxViol = MaxViol + 0.0
	AvgViol = AvgViol + 0.0
	//}
	
	// Set up the random number generator
	RandNum := rand.New(rand.NewSource(time.Now().UnixNano()))
	
	// Initialize the sample box bounds
	MaxWidth = 0.0; AvgWidth = 0.0
	for j:=0; j<lp.NumCols; j++ {
		BoxBndLo[j] = lp.LP.Cols[j].BndLo
		BoxBndUp[j] = BoxBndLo[j] + 10000.0
		if BoxBndUp[j] > lp.LP.Cols[j].BndUp {BoxBndUp[j] = lp.LP.Cols[j].BndUp}
		rhold = BoxBndUp[j] - BoxBndLo[j]
		AvgWidth = AvgWidth + rhold
		if rhold > MaxWidth {MaxWidth = rhold}
	}
	AvgWidth = AvgWidth/float64(lp.NumCols)
	LastAvgSFD = plinfy

	// Large iteration loop on rounds (boxes) starts here
	for itn := 0; itn < MaxBoxes; itn++ {
		// Zero out the statistics accumulators
		for j:=0; j<lp.NumCols; j++ {
			M[j] = 0.0
			Q[j] = 0.0
//			M[j] = plinfy
//			Q[j] = -plinfy
		}
		if PrintLevel > 0 {
			fmt.Println("ROUND",itn,"------------------------------------------------------------------")
			fmt.Println("Average sample box width:",AvgWidth,"Max width:",MaxWidth)
		}
		
		// Launch the CC runs
		for i := 0; i < 100; i++ {
			// Generate a random point
			for j:=0; j<lp.NumCols; j++ {
				SamplePt.Point[j] = BoxBndLo[j] + RandNum.Float64()*(BoxBndUp[j] - BoxBndLo[j])
			}
			go CCSimple(SamplePt.Point, chPointData, i)
		}

		// Retrieve the CC output points
		AvgSFD = 0.0
		icount = 0
		for i := 0; i < 100; i++ {
			SamplePt = <-chPointData
			AvgSFD = AvgSFD + SamplePt.SFD
			NumCCRuns++ // increment the counter on the number of CC runs
			if SamplePt.NINF == 0 {
				if PrintLevel > 0 {
					fmt.Println("\nFEASIBLE SOLUTION FOUND after", NumCCRuns, "CC runs processed.\n")
				}
				copy(IncumbentPt, SamplePt.Point)
				IncumbentSFD = 0.0
				IncumbentNINF = 0
				return IncumbentPt, 0
			}
			// Update the mean and variance accumulators
			if SamplePt.SFD <= LastAvgSFD {
				icount++
				if icount == 1 {
					for j:=0; j<lp.NumCols; j++ {
						M[j] = SamplePt.Point[j]	
						Q[j] = 0.0
					}
				} else {
					for j:=0; j<lp.NumCols; j++ {
						rhold = SamplePt.Point[j] - M[j]
						M[j] = M[j] + rhold/float64(icount)
						Q[j] = Q[j] + float64(icount-1)*rhold*rhold/float64(icount) 
					}
				}
			}
//			// Try finding smallest M and largest Q values
//			for j:=0; j<lp.NumCols; j++ {
//				if SamplePt[j] < M[j] {M[j] = SamplePt[j]}
//				if SamplePt[j] > Q[j] {Q[j] = SamplePt[j]}
//			}
		}
		LastAvgSFD = AvgSFD/100.0
		
		//Set up the new sample boxes based on the mean and standard deviation
		MaxWidth = 0.0; AvgWidth = 0.0
		for j:=0; j<lp.NumCols; j++ {
			rhold = math.Sqrt(Q[j]/float64(icount))
			
//			BoxBndLo[j] = M[j]
//			if BoxBndLo[j] > lp.LP.Cols[j].BndUp {BoxBndLo[j] = lp.LP.Cols[j].BndUp}
//			BoxBndUp[j] = Q[j]
//			if BoxBndUp[j] < lp.LP.Cols[j].BndLo {BoxBndUp[j] = lp.LP.Cols[j].BndLo}
			BoxBndLo[j] = M[j] - 1.5*rhold
			if BoxBndLo[j] > lp.LP.Cols[j].BndUp {BoxBndLo[j] = lp.LP.Cols[j].BndUp}			
//			if BoxBndLo[j] < lp.LP.Cols[j].BndLo {BoxBndLo[j] = lp.LP.Cols[j].BndLo}
			BoxBndUp[j] = M[j] + 1.5*rhold
			if BoxBndUp[j] < lp.LP.Cols[j].BndLo {BoxBndUp[j] = lp.LP.Cols[j].BndLo}
//			if BoxBndUp[j] > lp.LP.Cols[j].BndUp {BoxBndUp[j] = lp.LP.Cols[j].BndUp}
			if BoxBndUp[j] < BoxBndLo[j] {
				fmt.Println("Reversed bounds for variable",j,"corrected.")
				BoxBndUp[j] = BoxBndLo[j]
			}
			rhold = BoxBndUp[j] - BoxBndLo[j]
			AvgWidth = AvgWidth + rhold
			if rhold > MaxWidth {MaxWidth = rhold}
		}
		AvgWidth = AvgWidth/float64(lp.NumCols)
		
	} // end of large iteration loop

	return IncumbentPt, 1
}

//======================================================================================
// Tests a point in the way that a typical solver would do it: by comparing LHS and RHS
// Status: 0:(success), 1:(trouble evaluating one or more functions)
func TestPoint(PointIn []float64) (Status, NINF, NumSat, NumTight int, SINF, MaxViol, AvgViol float64) {

	var Violation float64 // The constraint violation
	var FVStatus int = 0
	var ViolStatus int = 0
	//var realhold float64 = 0.0

	//var TotBnds = 0 // Counts the total number of bounds, constraints plus variable bounds, with ranges counting as two
	Status = 0
	NumTight = 0  // Number of tight constraints, a subset of NumSat
	NumSat = 0    // Number of satisfied constraints
	NINF = 0      // Number of violated constraints
	SINF = 0.0    // Sum of violations
	MaxViol = 0.0 // Maximum violation
	AvgViol = 0.0 // Average violation over the violated constraints

	//test
	if math.IsNaN(PointIn[0]) {
		fmt.Println("***1 Point received by TestPoint is NaN.")
	}

	// Run through the constraints
	for icon := 0; icon < lp.NumRows; icon++ {

		// Get the feasibility status and violation of the constraint at the input point
		FVStatus, ViolStatus, Violation = GetViolation(icon, PointIn)
		// Direction of violation not needed, so take absolute value
		if Violation < 0.0 {
			Violation = -Violation
		}

		if FVStatus > 0 {
			fmt.Println("Error evaluating feasibility status for constraint", icon, ". Skipping it.")
			Status = 1
			Violation = 0.0
			continue
		}
		if ViolStatus > 0 {
			NumSat++
			if ViolStatus == 2 {
				NumTight++
			}
			continue
		}
		// Constraint is violated
		NINF++
		SINF = SINF + Violation
		if Violation > MaxViol {
			MaxViol = Violation
		}
	}

	// Run through the bounds testing for violations, tightness, etc.
	for ivar := 0; ivar < lp.NumCols; ivar++ {
		if lp.LP.Cols[ivar].BndLo > -plinfy {
			// There is a lower bound
			if PointIn[ivar] >= lp.LP.Cols[ivar].BndLo-featol {
				// Lower bound is satisfied, and perhaps tight
				NumSat++
				if PointIn[ivar] <= lp.LP.Cols[ivar].BndLo+featol {
					NumTight++
				}
			} else {
				// Lower bound is violated
				Violation = lp.LP.Cols[ivar].BndLo - PointIn[ivar]
				SINF = SINF + Violation
				NINF++
				if Violation > MaxViol {
					MaxViol = Violation
				}
			}
		}
		if lp.LP.Cols[ivar].BndUp < plinfy {
			// There is an upper bound
			if PointIn[ivar] <= lp.LP.Cols[ivar].BndUp+featol {
				// Upper bound is satisified and perhaps tight
				NumSat++
				if PointIn[ivar] >= lp.LP.Cols[ivar].BndUp-featol {
					NumTight++
				}
			} else {
				// Upper bound is violated
				Violation = PointIn[ivar] - lp.LP.Cols[ivar].BndUp
				SINF = SINF + Violation
				NINF++
				if Violation > MaxViol {
					MaxViol = Violation
				}
			}
		}
	}

	AvgViol = 0.0
	if NINF > 0 {
		AvgViol = SINF / float64(NINF)
	}

	// Print out results and return
	//fmt.Println("Point Test:")
	if NINF == 0 && Status == 0 {
		if PrintLevel > 0 {
			fmt.Println("***Feasible point***")
		}
	}
	//test
	//fmt.Println("Status:", Status, "NINF:", NINF, "NumSat:", NumSat, "NumTight:", NumTight, "SINF:", SINF, "MaxViol:", MaxViol, "AvgViol:", AvgViol)
	//fmt.Println("  ", NINF, "NINF (violated constraints/bounds)")
	//fmt.Println("  ", NumSat, "Satisfied constraints")
	//fmt.Println("    ", NumTight, "Tight constraints")
	//fmt.Println("  ", SINF, "SINF (sum of constraint violations)")
	//fmt.Println("    ", MaxViol, "Maximum violation")
	//fmt.Println("    ", AvgViol, "Average violation (for violated constraints/bounds)")

	return Status, NINF, NumSat, NumTight, SINF, MaxViol, AvgViol
}

//===============================================================================================
// Establishes a new set of initial points for re-sampling, based on latin hypercubing and
// shrinking the sampling box around the best points. Initially focussed just on reaching
// feasibility. Will be extended later to focus on optimality.
// Round: which round of sampling is this? 0 is first.
func NewPoints1(Round int) {

	// Local variables

	var BoxSide float64 = 10000.0       // standard launch box size is +/-10000 TODO: make this a parameter?
	var Width float64                   // distance between upper and lower bounds
	var BndLo, BndUp float64            // holders
	var realhold, realhold1 float64     // holders
	var rhold, rhold1, CVLength float64 // rhold is just a general holder, CVLength is the length of the consensus vector
	var FloatList []float64             // copy of a list of floats for use in sorting
	var IntList []int                   // a list of ints for use in sorting
	//var Pattern int                       // a list of dimension subdivision patterns
	//var iel, icol int                     // holders for element number and column number
	var ElNum, ColNum int
	var NINF int
	var NewMaxViol bool
	var FVLength, MaxFVLength, SFD float64
	var NewMaxFVLength bool
	var FVStatus, ViolStatus int
	var Violation, MaxViol, MaxMove float64  // MaxViol captures the largest violation, MaxMove captures the largest FV component seen
	FVMaxViol := make([]float64, lp.NumCols) // Captures the individual feasibility vector associated with the maximum LHS-RHS violation
	FVMaxFVLength := make([]float64, lp.NumCols)
	NumViol := make([]int, lp.NumCols)     // Number of violations
	SumViol := make([]float64, lp.NumCols) // Sum of violations (in terms of feasibility vector components)
	CV := make([]float64, lp.NumCols)      // Consensus Vector
	VotesUp := make([]int, lp.NumCols)     // Number of votes for increasing from incumbent value
	VotesDown := make([]int, lp.NumCols)   // Number of votes for decreasing from incumbent value
	//SumVector := make([]float64, len(Point))	// The movement vector for the sum method, from the incumbent

	// Set up the random number generator
	RandNum := rand.New(rand.NewSource(time.Now().UnixNano()))

	FloatList = make([]float64, MaxSwarmPts)
	//test
	//fmt.Println("Just entered NewPoints. Length of SwarmIn:",len(SwarmIn),"length of Swarm:",len(Swarm))

	//There will be a few special points, so set up the counters for these
	var NumSpecialPts int = 4
	var NumLHCPts int
	NumLHCPts = MaxSwarmPts - NumSpecialPts

	if Round > 0 {
		// The consensus vector will be needed, so calculate it now
		// The next four special points are all derived from the incumbent point and
		// it's feasibility and consensus vectors, so these must be calculated.
		NINF = 0
		MaxViol = -plinfy
		MaxMove = -plinfy
		MaxFVLength = -plinfy
		for i := 0; i < lp.NumCols; i++ {
			NumViol[i] = 0
			SumViol[i] = 0.0
			CV[i] = 0.0
			FVMaxViol[i] = 0.0
			FVMaxFVLength[i] = 0.0
		}
		for icon := 0; icon < lp.NumRows; icon++ {
			//test
			if math.IsNaN(IncumbentPt[0]) {
				fmt.Println("***1 GetViolation called with NaN IncumbentPt, line 1083 in NewPoints")
			}
			FVStatus, ViolStatus, Violation = GetViolation(icon, IncumbentPt)
			if FVStatus > 0 {
				fmt.Println("Error evaluating feasibility status for constraint", icon, ". Skipping it.")
				continue
			}
			if ViolStatus > 0 {
				// not violated, so skip
				continue
			}

			// Check length of feasibility vector
			rhold = 0.0 // Accumulates length of feasibility vector
			for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
				ElNum = lp.LP.Rows[icon].ElList[iel]
				ColNum = lp.Element[ElNum].Col
				rhold1 = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
				rhold = rhold + rhold1*rhold1
			}
			if rhold < Alpha*Alpha {
				// Feasibility vector is too short so skip this constraint
				continue
			}
			FVLength = math.Sqrt(rhold)
			SFD = SFD + FVLength

			// Constraint is violated
			NINF++
			//If using SINF
			NewMaxViol = false
			if math.Abs(Violation) > MaxViol {
				// There's a new maximum violation
				MaxViol = math.Abs(Violation)
				NewMaxViol = true
				// Empty the old FVMaxViol vector, fill it in the following step
				for j := 0; j < lp.NumCols; j++ {
					FVMaxViol[j] = 0.0
				}
			}
			NewMaxFVLength = false
			if FVLength > MaxFVLength {
				// There is a new longest feasibility vector
				MaxFVLength = FVLength
				NewMaxFVLength = true
				// Empty the old FVMaxFVLength, fill it in the next step
				for j := 0; j < lp.NumCols; j++ {
					FVMaxFVLength[j] = 0.0
				}
			}

			// Calculate the relevant elements of the feasibility vector
			rhold1 = 0.0
			for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
				ElNum = lp.LP.Rows[icon].ElList[iel]
				ColNum = lp.Element[ElNum].Col
				NumViol[ColNum]++
				rhold = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
				SumViol[ColNum] = SumViol[ColNum] + rhold
				rhold1 = rhold1 + rhold*rhold
				if NewMaxViol {
					FVMaxViol[ColNum] = rhold
				}
				if NewMaxFVLength {
					FVMaxFVLength[ColNum] = rhold
				}
				if rhold > 0.0 {
					VotesUp[ColNum]++
				}
				if rhold < 0.0 {
					VotesDown[ColNum]++
				}
				if MaxFVLength > MaxMove {
					MaxMove = MaxFVLength
				}
			}

		} // end of loop on icon

		// Run through the bounds looking for violations and making appropriate updates
		for ivar := 0; ivar < lp.NumCols; ivar++ {
			if IncumbentPt[ivar] >= lp.LP.Cols[ivar].BndLo-featol {
				// greater than lower bound
				if IncumbentPt[ivar] <= lp.LP.Cols[ivar].BndUp+featol {
					// less than upper bound
					continue
				} else if IncumbentPt[ivar]-lp.LP.Cols[ivar].BndUp > Alpha {
					// upper bound violated by large enough amount
					NINF++
					VotesDown[ivar]++
					NumViol[ivar]++
					rhold = lp.LP.Cols[ivar].BndUp - IncumbentPt[ivar]
					SumViol[ivar] = SumViol[ivar] + rhold
					SFD = SFD + math.Abs(rhold)

					if IncumbentPt[ivar]-lp.LP.Cols[ivar].BndUp > MaxFVLength {
						// There's a new maximum violation
						MaxFVLength = IncumbentPt[ivar] - lp.LP.Cols[ivar].BndUp
						// Empty the old FVMaxViol vector, fill it in the following step
						for j := 0; j < lp.LP.NumCols; j++ {
							FVMaxFVLength[j] = 0.0
						}
						FVMaxFVLength[ivar] = lp.LP.Cols[ivar].BndUp - IncumbentPt[ivar]
					}

				}
			} else if lp.LP.Cols[ivar].BndLo-IncumbentPt[ivar] > Alpha {
				// lower bound violated by large enough amount
				NINF++
				VotesUp[ivar]++
				NumViol[ivar]++
				rhold = lp.LP.Cols[ivar].BndLo - IncumbentPt[ivar]
				SumViol[ivar] = SumViol[ivar] + rhold
				SFD = SFD + rhold

				if lp.LP.Cols[ivar].BndLo-IncumbentPt[ivar] > MaxFVLength {
					// There's a new maximum violation
					MaxFVLength = lp.LP.Cols[ivar].BndLo - IncumbentPt[ivar]
					// Empty the old FVMaxViol vector, fill it in the following step
					for j := 0; j < lp.LP.NumCols; j++ {
						FVMaxFVLength[j] = 0.0
					}
					FVMaxFVLength[ivar] = lp.LP.Cols[ivar].BndLo - IncumbentPt[ivar]
				}

			}
		} // end of loop on ivar

		// Calculate the consensus vector vector and it's length
		rhold = 0.0 // Accumulates the squared elements of the consensus vector
		for ivar := 0; ivar < lp.NumCols; ivar++ {
			if NumViol[ivar] == 0 {
				CV[ivar] = 0.0
				continue
			}
			CV[ivar] = SumViol[ivar] / float64(NumViol[ivar])
			rhold = rhold + CV[ivar]*CV[ivar]
		}
		CVLength = math.Sqrt(rhold)

	} // end of calculation of the consensus vector

	// Set up the box boundaries
	switch {
	case Round == 0: // No swarm yet, so set up initial launch box based on sides of size 2e4
		for i := 0; i < lp.NumCols; i++ {
			// TODO: any types of columns to skip?
			BndLo = lp.LP.Cols[i].BndLo
			BndUp = lp.LP.Cols[i].BndUp
			Width = BndUp - BndLo
			if Width <= 2.0*BoxSide {
				BoxBndLo[i] = BndLo
				BoxBndUp[i] = BndUp
			} else {
				// Width is bigger than 2*BoxSide
				if BndLo <= -BoxSide && BndUp >= BoxSide {
					// center on zero
					BoxBndLo[i] = -BoxSide
					BoxBndUp[i] = BoxSide
				} else {
					// Extend from side closer to zero
					realhold = math.Abs(BndLo)
					realhold1 = math.Abs(BndUp)
					if realhold < realhold1 {
						// BndLo is closer to zero
						BoxBndLo[i] = BndLo
						BoxBndUp[i] = BndLo + 2.0*BoxSide
					} else {
						// BndUp is closer to zero
						BoxBndUp[i] = BndUp
						BoxBndLo[i] = BndUp - 2.0*BoxSide
					}
				}
			}
		} // end of for loop

	case Round == 1:
		// We just shift the box to centre it on the incumbent
		for i := 0; i < lp.NumCols; i++ {
			BoxBndLo[i] = IncumbentPt[i] - BoxSide
			BoxBndUp[i] = IncumbentPt[i] + BoxSide
		}

	case Round > 1: // Shrink the box around the current incumbent
		//BoxSide = BoxSide*float64(Round-1)*float64(2)/float64(3)  There was an error in the first runs...
		BoxSide = BoxSide * math.Pow(0.8, float64(Round-1))
		if BoxSide < featol*100.0 {
			BoxSide = featol * 100.0
		}
		for i := 0; i < lp.NumCols; i++ {
			BoxBndLo[i] = IncumbentPt[i] - BoxSide
			BoxBndUp[i] = IncumbentPt[i] + BoxSide
		}

	} // end of switch on Round

	// Set up the special points
	switch {

	case Round == 0:
		IdenticalPoints := true
		for i := 0; i < lp.LP.NumCols; i++ {
			// Point 0 is the origin
			Swarm[0][i] = 0.0
			// Point 1 is the box centre
			Swarm[1][i] = (BoxBndLo[i] + BoxBndUp[i]) / 2.0
			// Point 2 is at bound closest to zero, or zero if available
			if BoxBndLo[i] <= 0.0 && BoxBndUp[i] >= 0.0 {
				Swarm[2][i] = 0.0
			} else {
				if math.Abs(BoxBndLo[i]) < math.Abs(BoxBndUp[i]) {
					Swarm[2][i] = BoxBndLo[i]
					if BoxBndLo[i] != 0.0 {
						IdenticalPoints = false
					}
				} else {
					Swarm[2][i] = BoxBndUp[i]
					if BoxBndUp[i] != 0.0 {
						IdenticalPoints = false
					}
				}
			}
		}
		//If Points 0 and 1 are identical, then discard one of them in favour of more LHC points
		if IdenticalPoints {
			NumSpecialPts = NumSpecialPts - 1
			NumLHCPts++
		}

	case Round > 0:
		for i := 0; i < lp.NumCols; i++ {
			// Incumbent plus longest feasibility vector
			Swarm[0][i] = IncumbentPt[i] + FVMaxFVLength[i]
			// Incumbent plus SUM method
			Swarm[1][i] = IncumbentPt[i] + SumViol[i]
			// Incumbent plus MaxFVLength in CV direction
			// Incumbent plus large multiple in CV direction
			Swarm[2][i] = IncumbentPt[i] + CV[i]/CVLength*SFD*float64(Round)
			// Incumbent
			Swarm[3][i] = IncumbentPt[i]
		}

	} // end of Switch on Round for setting up special points

	// Set up the Latin Hypercube Sampling
	LongestSide := 0.0 // used here to capture the length of the longest side
	AvgSide := 0.0     // used here to capture the average side length
	for icol := 0; icol < lp.LP.NumCols; icol++ {
		Width = BoxBndUp[icol] - BoxBndLo[icol]
		if Width > LongestSide {
			LongestSide = Width
		}
		AvgSide = AvgSide + Width // First just accumulate the box side lengths, divide later

		realhold = (BoxBndUp[icol] - BoxBndLo[icol]) / (float64(NumLHCPts)) // holds the bin width
		for ibin := 0; ibin < NumLHCPts; ibin++ {
			//test
			//fmt.Println("NumSpecialPts",NumSpecialPts,"NumLHCPts",NumLHCPts,"ibin",ibin,"icol",icol)
			Swarm[NumSpecialPts+ibin][icol] = BoxBndLo[icol] + float64(ibin)*realhold + RandNum.Float64()*realhold
		}

		// Now shuffle the bins
		IntList = rand.Perm(NumLHCPts)
		for i := 0; i < NumLHCPts; i++ {
			FloatList[i] = Swarm[i+NumSpecialPts][icol]
		}
		for i := 0; i < NumLHCPts; i++ {
			Swarm[i+NumSpecialPts][icol] = FloatList[IntList[i]]
		}
	} // End of Latin Hypercubing

	//test: print out longest side, average side
	AvgSide = AvgSide / float64(lp.LP.NumCols)
	if PrintLevel > 0 {
		fmt.Println("\nBox", Round, ". Average side length:", AvgSide, ". Longest side length:", LongestSide)
	}

	return
}

//===============================================================================================
// Establishes a new set of initial points for re-sampling. Several of these are special points
// that are established relative to the current incumbent point. If called for, then there is
// also some random sampling in a box around the incumbent.  This sample box is set so that
// two-thirds of it's length is in the direction of the incumbent and the other third is in the
// opposite direction.
// Round: which round of sampling is this? 0 is first.
func NewPoints2(Round int) {

	// Local variables

	var BoxSide float64 = 10000.0       // standard launch box size is +/-10000 TODO: make this a parameter?
	var Width float64                   // distance between upper and lower bounds
	var BndLo, BndUp float64            // holders
	var realhold, realhold1 float64     // holders
	var rhold, rhold1, CVLength float64 // rhold is just a general holder, CVLength is the length of the consensus vector
	var FloatList []float64             // copy of a list of floats for use in sorting
	var IntList []int                   // a list of ints for use in sorting
	var AvgSide, LongestSide float64                 // average, longest box edge widths
	//var Pattern int                       // a list of dimension subdivision patterns
	//var iel, icol int                     // holders for element number and column number
	var ElNum, ColNum int
	var NINF int
	var NewMaxViol bool
	var FVLength, MaxFVLength, SFD float64
	var NewMaxFVLength bool
	var FVStatus, ViolStatus int
	var Violation, MaxViol, MaxMove float64  // MaxViol captures the largest violation, MaxMove captures the largest FV component seen
	FVMaxViol := make([]float64, lp.NumCols) // Captures the individual feasibility vector associated with the maximum LHS-RHS violation
	FVMaxFVLength := make([]float64, lp.NumCols)
	NumViol := make([]int, lp.NumCols)     // Number of violations
	SumViol := make([]float64, lp.NumCols) // Sum of violations (in terms of feasibility vector components)
	CV := make([]float64, lp.NumCols)      // Consensus Vector
	VotesUp := make([]int, lp.NumCols)     // Number of votes for increasing from incumbent value
	VotesDown := make([]int, lp.NumCols)   // Number of votes for decreasing from incumbent value
	//SumVector := make([]float64, len(Point))	// The movement vector for the sum method, from the incumbent

	// Set up the random number generator
	RandNum := rand.New(rand.NewSource(time.Now().UnixNano()))

	FloatList = make([]float64, MaxSwarmPts)
	//test
	//fmt.Println("Just entered NewPoints. Length of SwarmIn:",len(SwarmIn),"length of Swarm:",len(Swarm))

	//There will be a few special points, so set up the counters for these
	var NumSpecialPts int = 4
	var NumLHCPts int

	if UpdatesAtRoundStart == TotUpdates {
		MaxPts = 2 * NumSpecialPts
	} else {
		MaxPts = NumSpecialPts
	}
	NumLHCPts = MaxPts - NumSpecialPts

	if Round > 0 {
		// The consensus vector will be needed, so calculate it now
		// The next four special points are all derived from the incumbent point and
		// it's feasibility and consensus vectors, so these must be calculated.
		NINF = 0
		MaxViol = -plinfy
		MaxMove = -plinfy
		MaxFVLength = -plinfy
		for i := 0; i < lp.NumCols; i++ {
			NumViol[i] = 0
			SumViol[i] = 0.0
			CV[i] = 0.0
			FVMaxViol[i] = 0.0
			FVMaxFVLength[i] = 0.0
		}
		for icon := 0; icon < lp.NumRows; icon++ {
			//test
			if math.IsNaN(IncumbentPt[0]) {
				fmt.Println("***1 GetViolation called with NaN IncumbentPt, line 1083 in NewPoints")
			}
			FVStatus, ViolStatus, Violation = GetViolation(icon, IncumbentPt)
			if FVStatus > 0 {
				fmt.Println("Error evaluating feasibility status for constraint", icon, ". Skipping it.")
				continue
			}
			if ViolStatus > 0 {
				// not violated, so skip
				continue
			}

			// Check length of feasibility vector
			rhold = 0.0 // Accumulates length of feasibility vector
			for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
				ElNum = lp.LP.Rows[icon].ElList[iel]
				ColNum = lp.Element[ElNum].Col
				rhold1 = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
				rhold = rhold + rhold1*rhold1
			}
			if rhold < Alpha*Alpha {
				// Feasibility vector is too short so skip this constraint
				continue
			}
			FVLength = math.Sqrt(rhold)
			SFD = SFD + FVLength

			// Constraint is violated
			NINF++
			//If using SINF
			NewMaxViol = false
			if math.Abs(Violation) > MaxViol {
				// There's a new maximum violation
				MaxViol = math.Abs(Violation)
				NewMaxViol = true
				// Empty the old FVMaxViol vector, fill it in the following step
				for j := 0; j < lp.NumCols; j++ {
					FVMaxViol[j] = 0.0
				}
			}
			NewMaxFVLength = false
			if FVLength > MaxFVLength {
				// There is a new longest feasibility vector
				MaxFVLength = FVLength
				NewMaxFVLength = true
				// Empty the old FVMaxFVLength, fill it in the next step
				for j := 0; j < lp.NumCols; j++ {
					FVMaxFVLength[j] = 0.0
				}
			}

			// Calculate the relevant elements of the feasibility vector
			rhold1 = 0.0
			for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
				ElNum = lp.LP.Rows[icon].ElList[iel]
				ColNum = lp.Element[ElNum].Col
				NumViol[ColNum]++
				rhold = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
				SumViol[ColNum] = SumViol[ColNum] + rhold
				rhold1 = rhold1 + rhold*rhold
				if NewMaxViol {
					FVMaxViol[ColNum] = rhold
				}
				if NewMaxFVLength {
					FVMaxFVLength[ColNum] = rhold
				}
				if rhold > 0.0 {
					VotesUp[ColNum]++
				}
				if rhold < 0.0 {
					VotesDown[ColNum]++
				}
				if MaxFVLength > MaxMove {
					MaxMove = MaxFVLength
				}
			}

		} // end of loop on icon

		// Run through the bounds looking for violations and making appropriate updates
		for ivar := 0; ivar < lp.NumCols; ivar++ {
			if IncumbentPt[ivar] >= lp.LP.Cols[ivar].BndLo-featol {
				// greater than lower bound
				if IncumbentPt[ivar] <= lp.LP.Cols[ivar].BndUp+featol {
					// less than upper bound
					continue
				} else if IncumbentPt[ivar]-lp.LP.Cols[ivar].BndUp > Alpha {
					// upper bound violated by large enough amount
					NINF++
					VotesDown[ivar]++
					NumViol[ivar]++
					rhold = lp.LP.Cols[ivar].BndUp - IncumbentPt[ivar]
					SumViol[ivar] = SumViol[ivar] + rhold
					SFD = SFD + math.Abs(rhold)

					if IncumbentPt[ivar]-lp.LP.Cols[ivar].BndUp > MaxFVLength {
						// There's a new maximum violation
						MaxFVLength = IncumbentPt[ivar] - lp.LP.Cols[ivar].BndUp
						// Empty the old FVMaxViol vector, fill it in the following step
						for j := 0; j < lp.LP.NumCols; j++ {
							FVMaxFVLength[j] = 0.0
						}
						FVMaxFVLength[ivar] = lp.LP.Cols[ivar].BndUp - IncumbentPt[ivar]
					}

				}
			} else if lp.LP.Cols[ivar].BndLo-IncumbentPt[ivar] > Alpha {
				// lower bound violated by large enough amount
				NINF++
				VotesUp[ivar]++
				NumViol[ivar]++
				rhold = lp.LP.Cols[ivar].BndLo - IncumbentPt[ivar]
				SumViol[ivar] = SumViol[ivar] + rhold
				SFD = SFD + rhold

				if lp.LP.Cols[ivar].BndLo-IncumbentPt[ivar] > MaxFVLength {
					// There's a new maximum violation
					MaxFVLength = lp.LP.Cols[ivar].BndLo - IncumbentPt[ivar]
					// Empty the old FVMaxViol vector, fill it in the following step
					for j := 0; j < lp.LP.NumCols; j++ {
						FVMaxFVLength[j] = 0.0
					}
					FVMaxFVLength[ivar] = lp.LP.Cols[ivar].BndLo - IncumbentPt[ivar]
				}

			}
		} // end of loop on ivar

		// Calculate the consensus vector vector and it's length
		rhold = 0.0 // Accumulates the squared elements of the consensus vector
		for ivar := 0; ivar < lp.NumCols; ivar++ {
			if NumViol[ivar] == 0 {
				CV[ivar] = 0.0
				continue
			}
			CV[ivar] = SumViol[ivar] / float64(NumViol[ivar])
			rhold = rhold + CV[ivar]*CV[ivar]
		}
		CVLength = math.Sqrt(rhold)

	} // end of calculation of the consensus vector

	// Set up the box boundaries
	switch {
	case Round == 0: // No swarm yet, so set up initial launch box based on sides of size 2e4
		for i := 0; i < lp.NumCols; i++ {
			// TODO: any types of columns to skip?
			BndLo = lp.LP.Cols[i].BndLo
			BndUp = lp.LP.Cols[i].BndUp
			Width = BndUp - BndLo
			if Width <= 2.0*BoxSide {
				BoxBndLo[i] = BndLo
				BoxBndUp[i] = BndUp
			} else {
				// Width is bigger than 2*BoxSide
				if BndLo <= -BoxSide && BndUp >= BoxSide {
					// center on zero
					BoxBndLo[i] = -BoxSide
					BoxBndUp[i] = BoxSide
				} else {
					// Extend from side closer to zero
					realhold = math.Abs(BndLo)
					realhold1 = math.Abs(BndUp)
					if realhold < realhold1 {
						// BndLo is closer to zero
						BoxBndLo[i] = BndLo
						BoxBndUp[i] = BndLo + 2.0*BoxSide
					} else {
						// BndUp is closer to zero
						BoxBndUp[i] = BndUp
						BoxBndLo[i] = BndUp - 2.0*BoxSide
					}
				}
			}
		} // end of for loop

	case Round == 1:
		// We just shift the box to centre it on the incumbent
		for i := 0; i < lp.NumCols; i++ {
			BoxBndLo[i] = IncumbentPt[i] - BoxSide
			BoxBndUp[i] = IncumbentPt[i] + BoxSide
		}

	case Round > 1: // set up box with 2/3 of length in CV direction, other 1/3 in anti-CV direction
		BoxSide = SFD * 100.0
		if BoxSide < featol*100.0 {
			BoxSide = featol * 100.0
		}
		for i := 0; i < lp.NumCols; i++ {
			switch {
			case CV[i] > 0.0:
				BoxBndLo[i] = IncumbentPt[i] - 1.0/3.0*BoxSide
				BoxBndUp[i] = IncumbentPt[i] + 2.0/3.0*BoxSide
			case CV[i] < 0.0:
				BoxBndLo[i] = IncumbentPt[i] - 2.0/3.0*BoxSide
				BoxBndUp[i] = IncumbentPt[i] + 1.0/3.0*BoxSide
			case CV[i] == 0.0:
				BoxBndLo[i] = IncumbentPt[i] - 0.5*BoxSide
				BoxBndUp[i] = IncumbentPt[i] + 0.5*BoxSide
			}
		}

	} // end of switch on Round

	// Set up the special points
	switch {

	case Round == 0:
		IdenticalPoints := true
		for i := 0; i < lp.LP.NumCols; i++ {
			// Point 0 is the origin
			Swarm[0][i] = 0.0
			// Point 1 is the box centre
			Swarm[1][i] = (BoxBndLo[i] + BoxBndUp[i]) / 2.0
			// Point 2 is at bound closest to zero, or zero if available
			if BoxBndLo[i] <= 0.0 && BoxBndUp[i] >= 0.0 {
				Swarm[2][i] = 0.0
			} else {
				if math.Abs(BoxBndLo[i]) < math.Abs(BoxBndUp[i]) {
					Swarm[2][i] = BoxBndLo[i]
					if BoxBndLo[i] != 0.0 {
						IdenticalPoints = false
					}
				} else {
					Swarm[2][i] = BoxBndUp[i]
					if BoxBndUp[i] != 0.0 {
						IdenticalPoints = false
					}
				}
			}
		}
		//If Points 0 and 1 are identical, then discard one of them in favour of more LHC points
		if IdenticalPoints {
			NumSpecialPts = NumSpecialPts - 1
			NumLHCPts++
		}

	case Round > 0:
		for i := 0; i < lp.NumCols; i++ {
			// Incumbent plus longest feasibility vector
			Swarm[0][i] = IncumbentPt[i] + FVMaxFVLength[i]
			// Incumbent plus SUM method
			Swarm[1][i] = IncumbentPt[i] + SumViol[i]
			// Incumbent plus MaxFVLength in CV direction
			// Incumbent plus large multiple in CV direction
			Swarm[2][i] = IncumbentPt[i] + CV[i]/CVLength*SFD*float64(Round)
			// Incumbent
			Swarm[3][i] = IncumbentPt[i]
		}

	} // end of Switch on Round for setting up special points

	if NumLHCPts > 0 {
		// Set up the Latin Hypercube Sampling
		LongestSide = 0.0 // used here to capture the length of the longest side
		AvgSide = 0.0      // used here to capture the average side length
		for icol := 0; icol < lp.LP.NumCols; icol++ {
			Width = BoxBndUp[icol] - BoxBndLo[icol]
			if Width > LongestSide {
				LongestSide = Width
			}
			AvgSide = AvgSide + Width // First just accumulate the box side lengths, divide later

			realhold = (BoxBndUp[icol] - BoxBndLo[icol]) / (float64(NumLHCPts)) // holds the bin width
			for ibin := 0; ibin < NumLHCPts; ibin++ {
				//test
				//fmt.Println("NumSpecialPts",NumSpecialPts,"NumLHCPts",NumLHCPts,"ibin",ibin,"icol",icol)
				Swarm[NumSpecialPts+ibin][icol] = BoxBndLo[icol] + float64(ibin)*realhold + RandNum.Float64()*realhold
			}

			// Now shuffle the bins
			IntList = rand.Perm(NumLHCPts)
			for i := 0; i < NumLHCPts; i++ {
				FloatList[i] = Swarm[i+NumSpecialPts][icol]
			}
			for i := 0; i < NumLHCPts; i++ {
				Swarm[i+NumSpecialPts][icol] = FloatList[IntList[i]]
			}
		} // End of Latin Hypercubing

	}

	AvgSide = AvgSide / float64(lp.LP.NumCols)
	if PrintLevel > 0 {
		if NumLHCPts > 0 {
			fmt.Println("\nBox", Round, ". Average side length:", AvgSide, ". Longest side length:", LongestSide)
		} else {
			fmt.Println("\nBox", Round)
		}
	}

	return
}

//=========================================================================================
// This applies a simple search to improve the swarm. Since it operates on the package
// global variables, there are no arguments. The main idea is this: take some point k in
// the swarm and look at the vector between it and the incumbent point. You can calculate
// the rate of change of SINF between the two, and extrapolate that past the incumbent
// point to estimate the point at which SINF will be zero.
//   This version of swarm search tries (i) a forward linear projection from the swarm point
// through the incubment, then (ii) a reflection of the swarm point through the incumbent,
// (iii) a finally possibly a linear projection from the reflected point back through the
// incumbent.
// 	 In all cases, if the search succeeds then a quadratic projection is also tried.
//   Status: 0:(success), 1:(success feasible point found), 2:(failure)
func SwarmSearch4() (Status int) {

	// Local variables
	var Restart bool = true
	var AtLeastOneSuccess bool = false
	var TotTries int = 0 // total number of points tried
	var Vector []float64 // Vector between some point and the incumbent
	Vector = make([]float64, lp.NumCols)
	//	var VectorLength float64 // length of vector between two points
	var TryPoint []float64 // the tentative point to try
	TryPoint = make([]float64, lp.NumCols)
	var NINF int
	var MaxViol, AvgViol float64
	var SFD float64 // sum of feasibility distances
	MaxViol = MaxViol + 0
	AvgViol = AvgViol + 0 // dummy statements to please compiler

	if IncumbentSFD <= 0.0 || len(IncumbentPt) == 0 {
		fmt.Println("No incumbent on entry to SwarmSearch.")
	}

	for { // Loop until Restart is false
		if !Restart {
			break
		} // exit for loop if Restart is false
		Restart = false

		for ipt := 0; ipt < MaxSwarmPts; ipt++ {
			// Skip the incumbent, and don't bother if the point had only a small SINF difference from incumbent
			if IdenticalPts(Swarm[ipt], IncumbentPt) || SwarmSFD[ipt] < IncumbentSFD+10.0*Alpha {
				continue
			}
			// Set up the update vector
			for i := 0; i < lp.NumCols; i++ {
				Vector[i] = IncumbentPt[i] - Swarm[ipt][i]
			}
			// Try the forward projection
			TotTries++
			Status, TryPoint = SwarmProject(Swarm[ipt], Vector)
			if Status == 1 {
				// feasible point found so bail out
				FinalPointType = 20
				return 1
			}
			if Status > 1 {
				// some problem, so go to next point
				continue
			}
			// Check the point returned by the projection
			if IdenticalPts(IncumbentPt, TryPoint) {
				goto Reflect
			}
			Status, SFD, _, _, _, NINF = GetSFD(TryPoint)
			if Status == 1 {
				FinalPointType = 20
				// feasible point found
				return 1
			}
			if Status > 1 {
				fmt.Println("***Status > 1 for GetSFD call in SwarmSearch.")
			}
			if SFD < SwarmSFD[ipt] {
				copy(Swarm[ipt], TryPoint)
				SwarmSFD[ipt] = SFD
				// Check whether the incumbent has improved
				Status = UpdateIncumbentSFD(TryPoint, SFD, NINF, 20)
				if Status == 1 {
					// feasible point found
					FinalPointType = 20
					return 1
				}
				if Status == 0 {
					Restart = true // incumbent improved
				}
				// Point improved, so go to next point
				continue
			}
		Reflect:
			// Forward projection didn't work, so set up the reflected point
			for j := 0; j < lp.NumCols; j++ {
				TryPoint[j] = IncumbentPt[j] - (Swarm[ipt][j] - IncumbentPt[j])
			}
			// Test the reflected point
			Status, SFD, _, _, _, NINF = GetSFD(TryPoint)
			if Status == 1 {
				// feasible point found
				FinalPointType = 21
				return 1
			}
			if Status > 1 {
				fmt.Println("***Status > 1 for TestPoint call in SwarmSearch.")
			}
			// If the reflected point is better than the swarmpoint, update it
			if SFD < SwarmSFD[ipt] {
				copy(Swarm[ipt], TryPoint)
				SwarmSFD[ipt] = SFD
			}
			// Check whether reflected point is better than the incumbent
			if SFD < IncumbentSFD {
				// Reflected point is better, so project from incumbent through reflected point
				for i := 0; i < lp.NumCols; i++ {
					Vector[i] = TryPoint[i] - IncumbentPt[i]
				}
				TotTries++
				Status, TryPoint = SwarmProject(IncumbentPt, Vector)
			} else {
				// Reflected point is not better, so project from reflected point through incumbent
				for i := 0; i < lp.NumCols; i++ {
					Vector[i] = IncumbentPt[i] - TryPoint[i]
				}
				TotTries++
				Status, TryPoint = SwarmProject(TryPoint, Vector)
			}
			if Status == 1 {
				//feasible point found
				FinalPointType = 22
				return 1
			}
			if Status > 1 {
				continue
			} // either a problem or no improvement, so go to next point
			// Check the point returned by the projection
			if IdenticalPts(IncumbentPt, TryPoint) {
				continue
			}
			Status, SFD, _, _, _, NINF = GetSFD(TryPoint)
			if Status == 1 {
				// feasible point found
				FinalPointType = 22
				return 1
			}
			if Status > 1 {
				fmt.Println("***Status > 1 for GetSFD call in SwarmSearch.")
			}
			if SFD < SwarmSFD[ipt] {
				copy(Swarm[ipt], TryPoint)
				SwarmSFD[ipt] = SFD
				// Point improved, so see if incumbent can be updated
				Status = UpdateIncumbentSFD(TryPoint, SFD, NINF, 22)
				if Status == 1 {
					// feasible point found
					FinalPointType = 22
					return 1
				}
				if Status == 0 {
					Restart = true // incumbent improved
				}
			}

		} // end of loop on ipt

	} // end of Restart loop

	if PrintLevel > 0 {
		fmt.Println("Exiting swarm search after trying", TotTries, "points.")
	}
	if AtLeastOneSuccess {
		return 0
	}
	return 2
}
//=========================================================================================
// This applies a simple search to improve the swarm. Since it operates on the package
// global variables, there are no arguments. The main idea is this: take some point k in
// the swarm and look at the vector between it and the incumbent point. You can calculate
// the rate of change of SINF between the two, and extrapolate that past the incumbent
// point to estimate the point at which SINF will be zero.
//   This version of swarm search tries (i) a forward linear projection from the swarm point
// through the incubment, then (ii) a reflection of the swarm point through the incumbent,
// (iii) a finally possibly a linear projection from the reflected point back through the
// incumbent.
// 	 In all cases, if the search succeeds then a quadratic projection is also tried.
//   Status: 0:(success), 1:(success feasible point found), 2:(failure)
// The difference from SwarmSearch4 is that this one uses only the points up to MaxPts
// instead of up to MaxSwarmPts. MaxPts is set in NewPoints2 and is the number of points
// actually used in this round.
func SwarmSearch5() (Status int) {

	// Local variables
	var Restart bool = true
	var AtLeastOneSuccess bool = false
	var TotTries int = 0 // total number of points tried
	var Vector []float64 // Vector between some point and the incumbent
	Vector = make([]float64, lp.NumCols)
	//	var VectorLength float64 // length of vector between two points
	var TryPoint []float64 // the tentative point to try
	TryPoint = make([]float64, lp.NumCols)
	var NINF int
	var MaxViol, AvgViol float64
	var SFD float64 // sum of feasibility distances
	MaxViol = MaxViol + 0
	AvgViol = AvgViol + 0 // dummy statements to please compiler

	if IncumbentSFD <= 0.0 || len(IncumbentPt) == 0 {
		fmt.Println("No incumbent on entry to SwarmSearch.")
	}

	for { // Loop until Restart is false
		if !Restart {
			break
		} // exit for loop if Restart is false
		Restart = false

		for ipt := 0; ipt < MaxPts; ipt++ {
			// Skip the incumbent, and don't bother if the point had only a small SINF difference from incumbent
			if IdenticalPts(Swarm[ipt], IncumbentPt) || SwarmSFD[ipt] < IncumbentSFD+10.0*Alpha {
				continue
			}
			// Set up the update vector
			for i := 0; i < lp.NumCols; i++ {
				Vector[i] = IncumbentPt[i] - Swarm[ipt][i]
			}
			// Try the forward projection
			TotTries++
			Status, TryPoint = SwarmProject(Swarm[ipt], Vector)
			if Status == 1 {
				// feasible point found so bail out
				FinalPointType = 20
				return 1
			}
			if Status > 1 {
				// some problem, so go to next point
				continue
			}
			// Check the point returned by the projection
			if IdenticalPts(IncumbentPt, TryPoint) {
				goto Reflect
			}
			Status, SFD, _, _, _, NINF = GetSFD(TryPoint)
			if Status == 1 {
				FinalPointType = 20
				// feasible point found
				return 1
			}
			if Status > 1 {
				fmt.Println("***Status > 1 for GetSFD call in SwarmSearch.")
			}
			if SFD < SwarmSFD[ipt] {
				copy(Swarm[ipt], TryPoint)
				SwarmSFD[ipt] = SFD
				// Check whether the incumbent has improved
				Status = UpdateIncumbentSFD(TryPoint, SFD, NINF, 20)
				if Status == 1 {
					// feasible point found
					FinalPointType = 20
					return 1
				}
				if Status == 0 {
					Restart = true // incumbent improved
				}
				// Point improved, so go to next point
				continue
			}
		Reflect:
			// Forward projection didn't work, so set up the reflected point
			for j := 0; j < lp.NumCols; j++ {
				TryPoint[j] = IncumbentPt[j] - (Swarm[ipt][j] - IncumbentPt[j])
			}
			// Test the reflected point
			Status, SFD, _, _, _, NINF = GetSFD(TryPoint)
			if Status == 1 {
				// feasible point found
				FinalPointType = 21
				return 1
			}
			if Status > 1 {
				fmt.Println("***Status > 1 for TestPoint call in SwarmSearch.")
			}
			// If the reflected point is better than the swarmpoint, update it
			if SFD < SwarmSFD[ipt] {
				copy(Swarm[ipt], TryPoint)
				SwarmSFD[ipt] = SFD
			}
			// Check whether reflected point is better than the incumbent
			if SFD < IncumbentSFD {
				// Reflected point is better, so project from incumbent through reflected point
				for i := 0; i < lp.NumCols; i++ {
					Vector[i] = TryPoint[i] - IncumbentPt[i]
				}
				TotTries++
				Status, TryPoint = SwarmProject(IncumbentPt, Vector)
			} else {
				// Reflected point is not better, so project from reflected point through incumbent
				for i := 0; i < lp.NumCols; i++ {
					Vector[i] = IncumbentPt[i] - TryPoint[i]
				}
				TotTries++
				Status, TryPoint = SwarmProject(TryPoint, Vector)
			}
			if Status == 1 {
				//feasible point found
				FinalPointType = 22
				return 1
			}
			if Status > 1 {
				continue
			} // either a problem or no improvement, so go to next point
			// Check the point returned by the projection
			if IdenticalPts(IncumbentPt, TryPoint) {
				continue
			}
			Status, SFD, _, _, _, NINF = GetSFD(TryPoint)
			if Status == 1 {
				// feasible point found
				FinalPointType = 22
				return 1
			}
			if Status > 1 {
				fmt.Println("***Status > 1 for GetSFD call in SwarmSearch.")
			}
			if SFD < SwarmSFD[ipt] {
				copy(Swarm[ipt], TryPoint)
				SwarmSFD[ipt] = SFD
				// Point improved, so see if incumbent can be updated
				Status = UpdateIncumbentSFD(TryPoint, SFD, NINF, 22)
				if Status == 1 {
					// feasible point found
					FinalPointType = 22
					return 1
				}
				if Status == 0 {
					Restart = true // incumbent improved
				}
			}

		} // end of loop on ipt

	} // end of Restart loop

	if PrintLevel > 0 {
		fmt.Println("Exiting swarm search after trying", TotTries, "points.")
	}
	if AtLeastOneSuccess {
		return 0
	}
	return 2
}

//===================================================================================================
// Check to see whether any of the points in the Swarm are identical
func CheckForIdenticalPts() (SomeIdentical bool) {

	var Identical bool

	SomeIdentical = false
	for ipt1 := 0; ipt1 < MaxSwarmPts-1; ipt1++ {
		for ipt2 := ipt1 + 1; ipt2 < MaxSwarmPts; ipt2++ {
			Identical = true
			for j := 0; j < lp.NumCols; j++ {
				if Swarm[ipt1][j] != Swarm[ipt2][j] {
					Identical = false
					break
				}
			}
			if Identical {
				//fmt.Println("***Swarm points", ipt1, "and", ipt2, "are identical. SINF values are", SwarmSINF[ipt1], "and", SwarmSINF[ipt2])
				if PrintLevel > 0 {
					fmt.Println("***Swarm points", ipt1, "and", ipt2, "are identical. SFD values are", SwarmSFD[ipt1], "and", SwarmSFD[ipt2])
				}
				SomeIdentical = true
			}
		}
	}
	return SomeIdentical
}

//======================================================================================================
// Check whether the two compared points are identical or not
func IdenticalPts(Point1 []float64, Point2 []float64) (Identical bool) {
	Identical = true
	for j := 0; j < lp.NumCols; j++ {
		if Point1[j] != Point2[j] {
			Identical = false
			break
		}
	}
	//fmt.Println("Found identical points in IdenticalPts")
	return Identical
}

//=======================================================================================================
// Update the incumbent point.
// Status: 0(updated value), 1(feasible point), 2(input point not an improvement)
func UpdateIncumbent(PointIn []float64, SINFin float64, NINFin int, UpdatedBy int) (Status int) {

	var MyString string
	if SINFin >= IncumbentSINF {
		return 2
	}
	TotUpdates++
	if TotUpdates > 1 {
		FracUpdate[UpdatedBy] = FracUpdate[UpdatedBy] + (1.0 - SINFin/IncumbentSINF)
		NumUpdate[UpdatedBy]++
	}
	copy(IncumbentPt, PointIn)
	IncumbentSINF = SINFin
	IncumbentNINF = NINFin

	if UpdatedBy < 20 {
		MyString = "point " + strconv.Itoa(UpdatedBy)
	}
	if UpdatedBy == 20 {
		MyString = "forward swarm search"
	}
	if UpdatedBy == 21 {
		MyString = "reflected point"
	}
	if UpdatedBy == 22 {
		MyString = "reflected forward search"
	}
	fmt.Println("New incumbent:", IncumbentSINF, ". Generated by", MyString)
	Status = 0

	if IncumbentNINF == 0 {
		fmt.Println("\nFEASIBLE SOLUTION FOUND")
		Status = 1
	}
	return Status
}

//=======================================================================================================
// Updates either of the incumbent points (SFD or NINF)
// Status: 0(updated value), 1(feasible point), 2(input point not an improvement)
func UpdateIncumbents(PointIn []float64, SFDin, SINFin float64, NINFin int, UpdatedBy int) (Status int) {

	var MyString string
	if UpdatedBy < 20 {
		MyString = "point " + strconv.Itoa(UpdatedBy)
	}
	if UpdatedBy == 20 {
		MyString = "forward swarm search"
	}
	if UpdatedBy == 21 {
		MyString = "reflected point"
	}
	if UpdatedBy == 22 {
		MyString = "reflected forward search"
	}

	if SFDin < IncumbentSFD {
		// Update the incumbent SFD
		TotUpdates++
		if TotUpdates > 1 {
			FracUpdate[UpdatedBy] = FracUpdate[UpdatedBy] + (1.0 - SFDin/IncumbentSFD)
			NumUpdate[UpdatedBy]++
		}
		copy(IncumbentPt, PointIn)
		IncumbentSINF = SINFin
		IncumbentNINF = NINFin
		IncumbentSFD = SFDin

		fmt.Println("New incumbent SFD:", IncumbentSFD, ". Generated by", MyString)
		Status = 0
	}

	if NINFin < NIncumbentNINF {
		copy(NIncumbentPt, PointIn)
		NIncumbentSINF = SINFin
		NIncumbentNINF = NINFin
		NIncumbentSFD = SFDin
		fmt.Println("New incumbent NINF:", NIncumbentNINF, ". Generated by", MyString)
		Status = 0
	}

	if NINFin == 0 {
		fmt.Println("\nFEASIBLE SOLUTION FOUND")
		Status = 1
	}
	return Status
}

//=======================================================================================================
// MODIFIED TO CHOOSE SMALLER NINF AS INCUMBENT
//Update the incumbent point based on sum of feasibility distances.
// Status: 0(updated value), 1(feasible point), 2(input point not an improvement)
func UpdateIncumbentSFDforNINF(PointIn []float64, SFDin float64, NINFin int, UpdatedBy int) (Status int) {

	// Return immediately if SFD has not improved.
	var MyString string

	if NINFin > IncumbentNINF {
		return 2
	}
	if (NINFin == IncumbentNINF) && (SFDin > IncumbentSFD) {
		return 2
	}

	TotUpdates++

	//	if TotUpdates > 1 {
	//		for i := 0; i < lp.NumCols; i++ {
	//			if PointIn[i] < IncumbentPt[i] {
	//				IncumbentDown[i]++
	//				continue
	//			}
	//			if PointIn[i] > IncumbentPt[i] {
	//				IncumbentUp[i]++
	//				continue
	//			}
	//			IncumbentSame[i]++
	//		}
	//	}

	if TotUpdates > 1 {
		FracUpdate[UpdatedBy] = FracUpdate[UpdatedBy] + (1.0 - float64(NINFin)/float64(IncumbentNINF))
		NumUpdate[UpdatedBy]++
	}
	copy(IncumbentPt, PointIn)
	IncumbentSFD = SFDin
	IncumbentNINF = NINFin

	if UpdatedBy < 20 {
		MyString = "point " + strconv.Itoa(UpdatedBy)
	}
	if UpdatedBy == 20 {
		MyString = "forward swarm search"
	}
	if UpdatedBy == 21 {
		MyString = "reflected point"
	}
	if UpdatedBy == 22 {
		MyString = "reflected forward search"
	}
	fmt.Println("New incumbent SFD:", IncumbentSFD, "NINF:", IncumbentNINF, "generated by", MyString)
	Status = 0

	if IncumbentNINF == 0 {
		fmt.Println("\nFEASIBLE SOLUTION FOUND")
		Status = 1
	}
	return Status
}

//=======================================================================================================
// Update the incumbent point based on sum of feasibility distances.
// Status: 0(updated value), 1(feasible point), 2(input point not an improvement)
func UpdateIncumbentSFD(PointIn []float64, SFDin float64, NINFin int, UpdatedBy int) (Status int) {

	// Return immediately if SFD has not improved.
	if SFDin > IncumbentSFD {
		return 2
	}
	if (SFDin == IncumbentSFD) && (NINFin >= IncumbentNINF) {
		return 2
	}
	TotUpdates++

	if PrintLevel > 0 {fmt.Println("Updated SFD:",SFDin,"NINF:",NINFin)}

	copy(IncumbentPt, PointIn)
	IncumbentSFD = SFDin
	IncumbentNINF = NINFin
	Status = 0

	if IncumbentNINF == 0 {
		if PrintLevel > 0 {
			fmt.Println("\nFEASIBLE SOLUTION FOUND")
		}
		Status = 1
	}
	return Status
}

////==========================================================================================================
//// Augmentation step.
//// Input: a point and an update vector.
//// Operation: calculate SINF at updated point, then use the difference in SINF and the length of the direction
////   vector to calculate a multiplier for the direction vector that should take the solution to SINF=0.
////   This is the same as the forward swarm search. Don't bother with reflected search.
//// Output: a possibly updated point, or just the original point if this is unsuccessful.
//// Status: 0(success with improved point), 1(point not improved), 2(numerical problem or other failure)
////TODO: fix for use with SFD instead of SINF
//func Augment(PointIn []float64, UpdateVector []float64) (Status int, PointOut []float64) {
//	// Local variables
//	TryPoint := make([]float64, lp.NumCols)
//	var DeltaSINF, SINFgrad float64
//	var SINFIn, TrySINF, SINF, VectorLength, AugmentLength float64
//	var AugmentWorked bool = false
//
//	// Get SINF at the input point
//	Status, _, _, _, SINFIn, _, _ = TestPoint(PointIn)
//	if Status > 0 {
//		fmt.Println("Error calling TestPoint from Augment routine. Returning unsuccessfully.")
//		return 2, PointIn
//	}
//
//	// First make TryPoint the updated point
//	// and while we're at it, gather info on length of update vector
//	VectorLength = 0.0
//	for j := 0; j < lp.NumCols; j++ {
//		TryPoint[j] = PointIn[j] + UpdateVector[j]
//		VectorLength = VectorLength + UpdateVector[j]*UpdateVector[j]
//	}
//
//	// Get SINF at the updated point
//	Status, _, _, _, TrySINF, _, _ = TestPoint(TryPoint)
//	if Status > 0 {
//		fmt.Println("Error calling TestPoint from Augment routine. Returning unsuccessfully.")
//		return 2, PointIn
//	}
//	if TrySINF >= SINFIn {
//		// No improvement in SINF at updated point, so just return
//		//fmt.Println("Update vector provides no improvement in Augment routine. Returning unsuccessfully.")
//		return 1, PointIn
//	}
//
//	// SINF has improved, so now try an augmentation step.
//
//	// First look at the difference in SINF values
//	DeltaSINF = SINFIn - TrySINF
//	if DeltaSINF < featol {
//		//fmt.Println("***Oops: DeltaSINF too small in Augment.")
//		return 0, TryPoint
//	}
//
//	// Now check the length of the update vector
//	VectorLength = math.Sqrt(VectorLength)
//	if VectorLength < featol {
//		//fmt.Println ("***Oops: vector length too small in Augment.")
//		return 0, TryPoint
//	}
//
//	// Now check the rate of change of the augmentation vector
//	SINFgrad = DeltaSINF / VectorLength
//	if SINFgrad < featol {
//		//fmt.Println("***Oops: SINFgrad is too small in Augment.")
//		return 0, TryPoint
//	}
//
//	TryPoint2 := make([]float64, lp.NumCols)
//	// Estimated distance to where SINF is zeroed
//	AugmentLength = SINFIn / SINFgrad
//	// Calculate new TryPoint (while normalizing the Update Vector)
//	for j := 0; j < lp.NumCols; j++ {
//		TryPoint2[j] = PointIn[j] + AugmentLength*UpdateVector[j]/VectorLength
//	}
//
//	// Test the new point
//	Status, _, _, _, SINF, _, _ = TestPoint(TryPoint2)
//	if Status > 0 {
//		fmt.Println("Error calling TestPoint from Augment routine.")
//		AugmentFails++
//		//test re QuadApprox
//		//return 1, TryPoint
//	}
//	if SINF < TrySINF {
//		// Augmented point has succeeded
//		AugmentSucceeds++
//		FracAugment = FracAugment + (1.0 - SINF/TrySINF)
//		// test re QuadApprox
//		//return 0, TryPoint2
//		AugmentWorked = true
//	}
//	// Last point was better
//	AugmentFails++
//	//test re QuadApprox
//	//return 1, TryPoint
//
//	//test re QuadApprox
//	// OK now we have the info needed to try QuadApprox
//	Status, PointOut = QuadApprox(PointIn, TryPoint, TryPoint2, SINFIn, TrySINF, SINF)
//	if Status == 0 {
//		Status, _, _, _, SINF, _, _ = TestPoint(PointOut)
//		if Status > 0 {
//			fmt.Println("Error calling TestPoint from Augment routine.")
//		} else if SINF < TrySINF {
//			// QuadApprox has succeeded
//			QuadSucceeds++
//			FracQuad = FracQuad + (1.0 - SINF/TrySINF)
//			return 0, PointOut
//		}
//	}
//	QuadFails++
//	if AugmentWorked {return 0, TryPoint2}
//	return 1, TryPoint
//}
//
//
////==========================================================================================================
//// Augmentation step.
//// Input: a point and an update vector.
//// Operation: calculate SFD at updated point, then use the difference in SFD and the length of the direction
////   vector to calculate a multiplier for the direction vector that should take the solution to SFD=0.
////   This is the same as the forward swarm search. There is no reflected search. When we have the potential
////   updated point we now have 3 points in a line along the search vector, so we fit an interpolating
////   quadratic to these 3 points and go to the minimum of the quadratic, which adjusts the length of the
////   search vector. If this point is the best, then it is returned, else the augmented point could be
////   returned if better than the original.
//// Output: a possibly updated point, or just the original point if this is unsuccessful.
//// Status: 0(success with improved point), 1(point not improved), 2(numerical problem or other failure)
//func Augment1(PointIn []float64, UpdateVector []float64) (Status int, PointOut []float64) {
//	// Local variables
//	TryPoint := make([]float64, lp.NumCols)
//	var DeltaSFD, SFDgrad, SFDQuad float64
//	var SFDIn, TrySFD, SFD, VectorLength, AugmentLength float64
//	var AugmentWorked bool = false
//
//	// Get SFD at the input point
//	Status, SFDIn, _,_,_,_ = GetSFD(PointIn)
//	if Status == 1 {return 1, PointIn}
//	if Status > 1 {
//		fmt.Println("Error calling TestPoint from Augment routine. Returning unsuccessfully.")
//		return 2, PointIn
//	}
//
//	// First make the updated point TryPoint
//	// and while we're at it, gather info on length of update vector
//	VectorLength = 0.0
//	for j := 0; j < lp.LP.NumCols; j++ {
//		TryPoint[j] = PointIn[j] + UpdateVector[j]
//		VectorLength = VectorLength + UpdateVector[j]*UpdateVector[j]
//	}
//
//	// GetSFD at the updated point
//	Status, TrySFD, _,_,_,_ = GetSFD(TryPoint)
//	if Status == 1 {return 1, TryPoint}
//	if Status > 1 {
//		fmt.Println("Error calling TestPoint from Augment routine. Returning unsuccessfully.")
//		return 2, PointIn
//	}
//	if TrySFD >= SFDIn {
//		// No improvement in SINF at updated point, so just return
//		//fmt.Println("Update vector provides no improvement in Augment routine. Returning unsuccessfully.")
//		return 1, PointIn
//	}
//
//	// SINF has improved, so now try an augmentation step.
//
//	// First look at the difference in SINF values
//	DeltaSFD = SFDIn - TrySFD
//	if DeltaSFD < featol {
//		//fmt.Println("***Oops: DeltaSFD too small in Augment.")
//		return 0, TryPoint
//	}
//
//	// Now check the length of the update vector
//	VectorLength = math.Sqrt(VectorLength)
//	if VectorLength < featol {
//		//fmt.Println ("***Oops: vector length too small in Augment.")
//		return 0, TryPoint
//	}
//
//	// Now check the rate of change of the augmentation vector
//	SFDgrad = DeltaSFD / VectorLength
//	if SFDgrad < featol {
//		//fmt.Println("***Oops: SINFgrad is too small in Augment.")
//		return 0, TryPoint
//	}
//
//	TryPoint2 := make([]float64, lp.NumCols)
//	// Estimated distance to where SINF is zeroed
//	AugmentLength = SFDIn / SFDgrad
//	// Calculate new TryPoint (while normalizing the Update Vector)
//	for j := 0; j < lp.NumCols; j++ {
//		TryPoint2[j] = PointIn[j] + AugmentLength*UpdateVector[j]/VectorLength
//	}
//
//	// Test the new point
//	Status, SFD, _,_,_,_ = GetSFD(TryPoint2)
//	if Status == 1 {
//		AugmentSucceeds++
//		return 1, TryPoint2
//	}
//	if Status > 1 {
//		AugmentFails++
//		fmt.Println("Error calling TestPoint from Augment routine.")
//		return 0, TryPoint
//	}
//	if SFD < TrySFD {
//		// Augmented point has succeeded
//		AugmentWorked = true
//	}
//
//	//test re QuadApprox
//	// OK now we have the info needed to try QuadApprox
//	Status, PointOut = QuadApprox(PointIn, TryPoint, TryPoint2, SFDIn, TrySFD, SFD)
//	if Status == 0 {
//		// QuadApprox returns successfully
//		Status, SFDQuad, _,_,_,_ = GetSFD(PointOut)
//		if Status == 1 {
//			QuadSucceeds++
//			FracQuad = FracQuad + (1.0 - SFDQuad/math.Min(TrySFD,SFD))
//			return 1, PointOut
//		}
//		if Status > 1 {
//			fmt.Println("Error calling GetSFD from Augment1 routine.")
//			QuadFails++
//			if AugmentWorked {
//				AugmentSucceeds++
//				FracAugment = FracAugment + (1.0 - SFD/TrySFD)
//				return 0, TryPoint2
//			}
//			AugmentFails++
//			return 0, TryPoint
//		}
//		if SFDQuad < math.Min(math.Min(SFD,TrySFD), SFDIn) {
//			QuadSucceeds++
//			FracQuad = FracQuad + (1.0 - SFDQuad/math.Min(TrySFD,SFD))
//			return 0, PointOut
//		}
//		if AugmentWorked {
//			AugmentSucceeds++
//			FracAugment = FracAugment + (1.0 - SFD/TrySFD)
//			return 0, TryPoint2
//		}
//		AugmentFails++
//		return 0, TryPoint
//	}
//	//QuadApprox failed
//	QuadFails++
//	if AugmentWorked {
//		AugmentSucceeds++
//		FracAugment = FracAugment + (1.0 - SFD/TrySFD)
//		return 0, TryPoint2
//	}
//	AugmentFails++
//	return 0, TryPoint
//}

//==========================================================================================================
// This routine takes in a point and an update vector (usually the current CC point and the consensus vector)
//   and projects past the updated point to see if it can find a better point. Two types of projection are
//   used: (i) linear, based on the differences in the values of the SFD at the two points, and (ii)
//   quadratic, based on the minimum point derived from a quadratic fit to the first three points.
// There are 4 relevant points and related information:
//   Pt0: this is the original point
//   Pt1: this is the point updated by the UpdateVector
//   Pt2: this is the point linearly projected from Pt0 through Pt1 based on the difference in SFD
//   Pt3: this is the point found by minimizing the quadratic fit to points Pt0, Pt1 and Pt2.
// Input: a point and an update vector.
// Output: a possibly updated point, or just the original point if this is unsuccessful.
// Status: 0(success), 1(success and feasible pt found), 2(numerical problem or other failure)
func Project(Pt0 []float64, UpdateVector []float64) (Status int, PointOut []float64) {

	// Local variables
	Pt1 := make([]float64, lp.NumCols)
	Pt2 := make([]float64, lp.NumCols)
	Pt3 := make([]float64, lp.NumCols)
	var SFD0, SFD1, SFD2, SFD3 float64
	var NINF0 int
	var BestPt int = 0 // keeps track of the point having the lowest SFD among the four
	var DeltaSFD, SFDgrad float64
	var VectorLength, ProjectLength float64

	// Get SFD at Pt0
	Status, SFD0, _, _, _, NINF0 = GetSFD(Pt0)
	if Status == 1 { // Point is feasible
		return 1, Pt0
	}
	if Status > 1 {
		fmt.Println("Error calling GetSFD from Project for Pt0. Returning unsuccessfully.")
		return 2, Pt0
	}
	BestPt = 0
	//test
	NINF0 = NINF0 + 1

	// Get Pt1 and the length of update vector
	VectorLength = 0.0
	for j := 0; j < lp.LP.NumCols; j++ {
		Pt1[j] = Pt0[j] + UpdateVector[j]
		VectorLength = VectorLength + UpdateVector[j]*UpdateVector[j]
	}
	// GetSFD at Pt1
	Status, SFD1, _, _, _, _ = GetSFD(Pt1)
	if Status == 1 { // feasible point
		copy(IncumbentPt, Pt1)
		IncumbentSFD = 0.0
		IncumbentNINF = 0.0
		IncumbentSINF=0.0
		return 1, Pt1
	}
	if Status > 1 {
		fmt.Println("Error calling GetSFD from Project for Pt1. Returning unsuccessfully.")
		return 2, Pt0
	}
	if SFD1 >= SFD0 {
		// No improvement in SFD at updated point, so just return
		//fmt.Println("Update vector provides no improvement in Project routine. Returning unsuccessfully.")
		return 2, Pt0
	}
	BestPt = 1

	// SFD decreases between Pt0 and Pt1 so try a linear projection
	// First look at the difference in SINF values
	DeltaSFD = SFD0 - SFD1
	if DeltaSFD < featol {
		//fmt.Println("***Oops: DeltaSFD too small in Project.")
		return 0, Pt1
	}
	// Now check the length of the update vector
	VectorLength = math.Sqrt(VectorLength)
	if VectorLength < featol {
		//fmt.Println ("***Oops: vector length too small in Project.")
		return 0, Pt1
	}
	// Now check the rate of change of the augmentation vector
	SFDgrad = DeltaSFD / VectorLength
	if SFDgrad < featol {
		//fmt.Println("***Oops: SINFgrad is too small in Project.")
		return 0, Pt1
	}
	// Estimated distance to where SFD is zeroed.
	//VectorLength = (IncumbentSFD / SFDgrad) * 1.0/(0.5 + 1.0/(2.0*float64(IncumbentNINF)))
	ProjectLength = (SFD0 / SFDgrad) //* 1.0/(0.5 + 1.0/(2.0*float64(NINF0)))
	// Calculate linearly projected point (while normalizing the Update Vector)
	for j := 0; j < lp.NumCols; j++ {
		Pt2[j] = Pt0[j] + ProjectLength*UpdateVector[j]/VectorLength
	}

	// Test the linearly projected point Pt2
	Status, SFD2, _, _, _, _ = GetSFD(Pt2)
	if Status == 1 {
		// feasible point found
		LinProjSucceeds++
		LinProjFrac = LinProjFrac + 1.0
		copy(IncumbentPt, Pt2)
		IncumbentSFD = 0.0
		IncumbentNINF = 0.0
		IncumbentSINF=0.0
		return 1, Pt2
	}
	if Status > 1 {
		LinProjFails++
		fmt.Println("Error calling GetSFD from Project.")
		return 0, Pt1
	}
	if SFD2 < SFD1 {
		// Linearly projected point has succeeded
		LinProjSucceeds++
		LinProjFrac = LinProjFrac + (1.0 - SFD2/SFD1)
		BestPt = 2
	}
	LinProjFails++

	// Now we have the info needed to try a quadratic approximation
	Status, Pt3 = QuadApprox(Pt0, Pt1, Pt2, SFD0, SFD1, SFD2)
	if Status > 0 {
		// QuadApprox failed, so return best point so far, which must be Pt1 or Pt2
		QuadProjFails++
		if BestPt == 1 {
			return 0, Pt1
		}
		if BestPt == 2 {
			return 0, Pt2
		}
	}
	// QuadApprox succeeded, so test relative goodness of point vs. previous best
	Status, SFD3, _, _, _, _ = GetSFD(Pt3)
	if Status == 1 {
		// feasible point found
		QuadProjSucceeds++
		QuadProjFrac = QuadProjFrac + 1.0
		copy(IncumbentPt, Pt3)
		IncumbentSFD = 0.0
		IncumbentNINF = 0.0
		IncumbentSINF=0.0
		return 1, Pt3
	}
	if SFD3 < math.Min(SFD2, SFD1) {
		// QuadApprox returned a better point
		QuadProjSucceeds++
		QuadProjFrac = QuadProjFrac + (1.0 - SFD3/math.Min(SFD2, SFD1))
		return 0, Pt3
	}
	QuadProjFails++
	if BestPt == 1 {
		return 0, Pt1
	}
	if BestPt == 2 {
		return 0, Pt2
	}
	return 0, Pt1
}

//==========================================================================================================
// Identical to Project routine, but has different status vector and will not return the incumbent (Pt1)
// This routine takes in a point and an update vector (usually the current CC point and the consensus vector)
//   and projects past the updated point to see if it can find a better point. Two types of projection are
//   used: (i) linear, based on the differences in the values of the SFD at the two points, and (ii)
//   quadratic, based on the minimum point derived from a quadratic fit to the first three points.
// There are 4 relevant points and related information:
//   Pt0: this is the original point
//   Pt1: this is the point updated by the UpdateVector
//   Pt2: this is the point linearly projected from Pt0 through Pt1 based on the difference in SFD
//   Pt3: this is the point found by minimizing the quadratic fit to points Pt0, Pt1 and Pt2.
// Input: a point and an update vector.
// Output: a possibly updated point, or just the original point if this is unsuccessful.
// Status: 0(improved point found), 1(success and feasible pt found),
//         2(no improved pt found), 3(numerical problem or other failure)
func SwarmProject(Pt0 []float64, UpdateVector []float64) (Status int, PointOut []float64) {

	// Local variables
	Pt1 := make([]float64, lp.NumCols)
	Pt2 := make([]float64, lp.NumCols)
	Pt3 := make([]float64, lp.NumCols)
	var SFD0, SFD1, SFD2, SFD3 float64
	var NINF0 int
	var BestPt int = 0 // keeps track of the point having the lowest SFD among the four
	var DeltaSFD, SFDgrad float64
	var VectorLength, ProjectLength float64

	// Get SFD at Pt0
	Status, SFD0, _, _, _, NINF0 = GetSFD(Pt0)
	if Status == 1 {
		return 1, Pt0
	}
	if Status > 1 {
		fmt.Println("Error calling GetSFD from Project for Pt0. Returning unsuccessfully.")
		return 3, Pt0
	}
	BestPt = 0
	//test
	NINF0 = NINF0 + 1

	// Get Pt1 and the length of update vector
	VectorLength = 0.0
	for j := 0; j < lp.LP.NumCols; j++ {
		Pt1[j] = Pt0[j] + UpdateVector[j]
		VectorLength = VectorLength + UpdateVector[j]*UpdateVector[j]
	}
	// GetSFD at Pt1
	Status, SFD1, _, _, _, _ = GetSFD(Pt1)
	if Status == 1 {
		//feasible point found
		copy(IncumbentPt, Pt1)
		IncumbentSFD = 0.0
		IncumbentNINF = 0.0
		IncumbentSINF=0.0
		return 1, Pt1
	}
	if Status > 1 {
		fmt.Println("Error calling GetSFD from Project for Pt1. Returning unsuccessfully.")
		return 3, Pt0
	}
	if SFD1 >= SFD0 {
		// No improvement in SFD at updated point, so just return
		//fmt.Println("Update vector provides no improvement in Project routine. Returning unsuccessfully.")
		return 2, Pt0
	}
	BestPt = 1

	// SFD decreases between Pt0 and Pt1 so try a linear projection
	// First look at the difference in SINF values
	DeltaSFD = SFD0 - SFD1
	if DeltaSFD < featol {
		//fmt.Println("***Oops: DeltaSFD too small in Project.")
		return 2, Pt1
	}
	// Now check the length of the update vector
	VectorLength = math.Sqrt(VectorLength)
	if VectorLength < featol {
		//fmt.Println ("***Oops: vector length too small in Project.")
		return 2, Pt1
	}
	// Now check the rate of change of the augmentation vector
	SFDgrad = DeltaSFD / VectorLength
	if SFDgrad < featol {
		//fmt.Println("***Oops: SINFgrad is too small in Project.")
		return 2, Pt1
	}
	// Estimated distance to where SFD is zeroed.
	//VectorLength = (IncumbentSFD / SFDgrad) * 1.0/(0.5 + 1.0/(2.0*float64(IncumbentNINF)))
	ProjectLength = (SFD0 / SFDgrad) //* 1.0/(0.5 + 1.0/(2.0*float64(NINF0)))
	// Calculate linearly projected point (while normalizing the Update Vector)
	for j := 0; j < lp.NumCols; j++ {
		Pt2[j] = Pt0[j] + ProjectLength*UpdateVector[j]/VectorLength
	}

	// Test the linearly projected point Pt2
	Status, SFD2, _, _, _, _ = GetSFD(Pt2)
	if Status == 1 {
		LinProjSucceeds++
		LinProjFrac = LinProjFrac + 1.0
		copy(IncumbentPt, Pt2)
		IncumbentSFD = 0.0
		IncumbentNINF = 0.0
		IncumbentSINF=0.0
		return 1, Pt2
	}
	if Status > 1 {
		LinProjFails++
		fmt.Println("Error calling GetSFD from Project.")
		return 2, Pt1
	}
	if SFD2 < SFD1 {
		// Linearly projected point has succeeded
		LinProjSucceeds++
		LinProjFrac = LinProjFrac + (1.0 - SFD2/SFD1)
		BestPt = 2
	}
	LinProjFails++

	// Now we have the info needed to try a quadratic approximation
	Status, Pt3 = QuadApprox(Pt0, Pt1, Pt2, SFD0, SFD1, SFD2)
	if Status > 0 {
		// QuadApprox failed, so return best point so far, which must be Pt1 or Pt2
		QuadProjFails++
		if BestPt == 1 {
			return 2, Pt1
		}
		if BestPt == 2 {
			return 2, Pt2
		}
	}
	// QuadApprox succeeded, so test relative goodness of point vs. previous best
	Status, SFD3, _, _, _, _ = GetSFD(Pt3)
	if Status == 1 {
		// feasible point found
		QuadProjSucceeds++
		QuadProjFrac = QuadProjFrac + 1.0
		copy(IncumbentPt, Pt3)
		IncumbentSFD = 0.0
		IncumbentNINF = 0.0
		IncumbentSINF=0.0
		return 1, Pt3
	}
	if SFD3 < math.Min(SFD2, SFD1) {
		// QuadApprox returned a better point
		QuadProjSucceeds++
		QuadProjFrac = QuadProjFrac + (1.0 - SFD3/math.Min(SFD2, SFD1))
		return 0, Pt3
	}
	QuadProjFails++
	if BestPt == 1 {
		return 2, Pt1
	}
	if BestPt == 2 {
		return 2, Pt2
	}
	return 2, Pt1
}

//==========================================================================================================
// VERSION THAT ONLY REPLACES POINT IF NINF REDUCED
// Identical to Project routine, but has different status vector and will not return the incumbent (Pt1)
// This routine takes in a point and an update vector (usually the current CC point and the consensus vector)
//   and projects past the updated point to see if it can find a better point. Two types of projection are
//   used: (i) linear, based on the differences in the values of the SFD at the two points, and (ii)
//   quadratic, based on the minimum point derived from a quadratic fit to the first three points.
// There are 4 relevant points and related information:
//   Pt0: this is the original point
//   Pt1: this is the point updated by the UpdateVector
//   Pt2: this is the point linearly projected from Pt0 through Pt1 based on the difference in SFD
//   Pt3: this is the point found by minimizing the quadratic fit to points Pt0, Pt1 and Pt2.
// Input: a point and an update vector.
// Output: a possibly updated point, or just the original point if this is unsuccessful.
// Status: 0(improved point found), 1(success and feasible pt found),
//         2(no improved pt found), 3(numerical problem or other failure)
func SwarmProject1(Pt0 []float64, UpdateVector []float64) (Status int, PointOut []float64) {

	// Local variables
	Pt1 := make([]float64, lp.NumCols)
	Pt2 := make([]float64, lp.NumCols)
	Pt3 := make([]float64, lp.NumCols)
	var SFD0, SFD1, SFD2, SFD3 float64
	var NINF0, NINF1, NINF2, NINF3, BestNINF int
	var BestPt int = 0 // keeps track of the point having the lowest SFD among the four
	var DeltaSFD, SFDgrad float64
	var VectorLength, ProjectLength float64

	// Get SFD at Pt0
	Status, SFD0, _, _, _, NINF0 = GetSFD(Pt0)
	if Status == 1 {
		return 1, Pt0
	}
	if Status > 1 {
		fmt.Println("Error calling GetSFD from Project for Pt0. Returning unsuccessfully.")
		return 3, Pt0
	}
	BestPt = 0
	BestNINF = NINF0
	//test
	//NINF0 = NINF0 + 1

	// Get Pt1 and the length of update vector
	VectorLength = 0.0
	for j := 0; j < lp.LP.NumCols; j++ {
		Pt1[j] = Pt0[j] + UpdateVector[j]
		VectorLength = VectorLength + UpdateVector[j]*UpdateVector[j]
	}
	// GetSFD at Pt1
	Status, SFD1, _, _, _, NINF1 = GetSFD(Pt1)
	if Status == 1 {
		return 1, Pt1
	}
	if Status > 1 {
		fmt.Println("Error calling GetSFD from Project for Pt1. Returning unsuccessfully.")
		return 3, Pt0
	}
	if SFD1 >= SFD0 {
		// No improvement in SFD at updated point, so just return
		//fmt.Println("Update vector provides no improvement in Project routine. Returning unsuccessfully.")
		return 2, Pt0
	}
	BestPt = 1
	BestNINF = NINF1
	if NINF0 < NINF1 {
		BestPt = 0
		BestNINF = NINF0
	}

	// SFD decreases between Pt0 and Pt1 so try a linear projection
	// First look at the difference in SINF values
	DeltaSFD = SFD0 - SFD1
	if DeltaSFD < featol {
		//fmt.Println("***Oops: DeltaSFD too small in Project.")
		return 2, Pt1
	}
	// Now check the length of the update vector
	VectorLength = math.Sqrt(VectorLength)
	if VectorLength < featol {
		//fmt.Println ("***Oops: vector length too small in Project.")
		return 2, Pt1
	}
	// Now check the rate of change of the augmentation vector
	SFDgrad = DeltaSFD / VectorLength
	if SFDgrad < featol {
		//fmt.Println("***Oops: SINFgrad is too small in Project.")
		return 2, Pt1
	}
	// Estimated distance to where SFD is zeroed.
	//VectorLength = (IncumbentSFD / SFDgrad) * 1.0/(0.5 + 1.0/(2.0*float64(IncumbentNINF)))
	ProjectLength = (SFD0 / SFDgrad) //* 1.0/(0.5 + 1.0/(2.0*float64(NINF0)))
	// Calculate linearly projected point (while normalizing the Update Vector)
	for j := 0; j < lp.NumCols; j++ {
		Pt2[j] = Pt0[j] + ProjectLength*UpdateVector[j]/VectorLength
	}

	// Test the linearly projected point Pt2
	Status, SFD2, _, _, _, NINF2 = GetSFD(Pt2)
	if Status == 1 {
		LinProjSucceeds++
		LinProjFrac = LinProjFrac + 1.0
		return 1, Pt2
	}
	if Status > 1 {
		LinProjFails++
		fmt.Println("Error calling GetSFD from Project.")
		return 2, Pt1
	}
	if SFD2 < SFD1 {
		// Linearly projected point has succeeded
		LinProjSucceeds++
		LinProjFrac = LinProjFrac + (1.0 - SFD2/SFD1)
		//BestPt = 2
		if NINF2 < BestNINF {
			BestPt = 2
			BestNINF = NINF2
		}
	}
	LinProjFails++

	// Now we have the info needed to try a quadratic approximation
	Status, Pt3 = QuadApprox(Pt0, Pt1, Pt2, SFD0, SFD1, SFD2)
	if Status > 0 {
		// QuadApprox failed, so return best point so far, which must be Pt1 or Pt2
		QuadProjFails++
		if BestPt == 1 {
			return 2, Pt1
		}
		if BestPt == 2 {
			return 2, Pt2
		}
		return 2, Pt0 // no improvement
	}
	// QuadApprox succeeded, so test relative goodness of point vs. previous best
	Status, SFD3, _, _, _, NINF3 = GetSFD(Pt3)
	if Status == 1 {
		// feasible point found
		QuadProjSucceeds++
		QuadProjFrac = QuadProjFrac + 1.0
		return 1, Pt3
	}
	if SFD3 < math.Min(SFD2, SFD1) {
		// QuadApprox returned a better point
		QuadProjSucceeds++
		QuadProjFrac = QuadProjFrac + (1.0 - SFD3/math.Min(SFD2, SFD1))
		if NINF3 < BestNINF {
			BestPt = 3
			BestNINF = NINF3
		}
		switch {
		case BestPt == 0:
			return 2, Pt0 // no improvement
		case BestPt == 1:
			return 0, Pt1
		case BestPt == 2:
			return 0, Pt2
		case BestPt == 3:
			return 0, Pt3
		}
	}
	QuadProjFails++
	if BestPt == 1 {
		return 2, Pt1
	}
	if BestPt == 2 {
		return 2, Pt2
	}
	return 2, Pt1
}

//===========================================================================================================
// For a given input point, this routine returns the sum of the feasibility distances SFDout, the largest
// feasibility distance MaxFDout, and the number of the constraint or variable that MaxFDout is
// associated with.
// Status: 0(successful), 1(successful and feasible), 2(numerical problem)
func GetSFD(PointIn []float64) (Status int, SFDout float64, MaxFDout float64, MaxFDCon int, MaxFDVar int, NINF int) {

	// Local variables
	var FVStatus, ViolStatus int
	var Violation float64
	var ElNum int
	var rhold, rhold1 float64

	//test
	if math.IsNaN(PointIn[0]) {
		fmt.Println("***1 GetViolation called with NaN PointIn in GetSFD. Exiting GetSFD.")
		//os.Exit(1)}
		return 2, 0.0, 0.0, -1, -1, 0
	}

	Status = 0
	SFDout = 0.0
	MaxFDout = 0.0
	MaxFDCon = -1
	MaxFDVar = -1
	NINF = 0
	// Run through the constraints
	for icon := 0; icon < lp.NumRows; icon++ {

		// Get the feasibility vector, if there is one
		FVStatus, ViolStatus, Violation = GetViolation(icon, PointIn)

		//test
		//fmt.Println("After GetViolation call for con",icon,"Violation:",Violation,"FVStatus:",FVStatus,"ViolStatus:",ViolStatus)

		if FVStatus > 0 {
			fmt.Println("Error evaluating feasibility status for constraint", icon, "in GetSFD. Skipping it.")
			continue
		}
		if ViolStatus > 0 {
			// not violated, so skip
			continue
		}

		// Check length of feasibility vector
		rhold = 0.0 // Accumulates length of feasibility vector
		for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
			ElNum = lp.LP.Rows[icon].ElList[iel]
			rhold1 = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
			rhold = rhold + rhold1*rhold1
		}
		if rhold < Alpha*Alpha {
			// Feasibility vector is too short
			continue
		}

		// Constraint is violated
		rhold = math.Sqrt(rhold) // Converts to actual length from length squared
		SFDout = SFDout + rhold
		if rhold > MaxFDout {
			MaxFDout = rhold
			MaxFDCon = icon
		}
		NINF++
	}

	// Run through the bounds looking for violations and making appropriate updates
	for ivar := 0; ivar < lp.NumCols; ivar++ {
		if PointIn[ivar] >= lp.LP.Cols[ivar].BndLo-Alpha {
			// greater than lower bound
			if PointIn[ivar] <= lp.LP.Cols[ivar].BndUp+Alpha {
				// less than upper bound
				continue
			} else if PointIn[ivar]-lp.LP.Cols[ivar].BndUp > Alpha {
				// upper bound violated by large enough amount
				NINF++
				rhold = PointIn[ivar] - lp.LP.Cols[ivar].BndUp
				SFDout = SFDout + rhold
				if rhold > MaxFDout {
					MaxFDout = rhold
					MaxFDCon = -1
					MaxFDVar = ivar
				}

			}
		} else if lp.LP.Cols[ivar].BndLo-PointIn[ivar] > Alpha {
			// lower bound violated by large enough amount
			NINF++
			rhold = lp.LP.Cols[ivar].BndLo - PointIn[ivar]
			SFDout = SFDout + rhold
			if rhold > MaxFDout {
				MaxFDout = rhold
				MaxFDCon = -1
				MaxFDVar = ivar
			}
		}
	}

	if NINF == 0 {
		//fmt.Println("***Feasible point found in GetSFD.")
		return 1, 0.0, 0.0, -1, -1, 0
	}
	return 0, SFDout, MaxFDout, MaxFDCon, MaxFDVar, NINF
}

//======================================================================================================
// Given two points X0 and X1, the routine finds the multiplier to apply to the direction
// vector between them so that the updated point will satisfy the specified constraint or bound exactly.
// CBIndex: the index of the constraint or bound
// ConOrBnd: 0(constraint), 1(bound)
// Status: 0(successful output of a multiplier), 1(cannot calculate a multiplier in this case), 2(numerical error)
func GetMultiplier(X0, X1 []float64, CBIndex int, ConOrBnd int) (Status int, Multiplier float64) {

	var Violation0, Violation1, Diff float64
	var FVStatus, ViolStatus int
	var Lower, Upper float64

	if ConOrBnd == 0 {
		// It's a row constraint
		if lp.LP.Rows[CBIndex].Type == "N" {
			return 1, 0.0
		}
		FVStatus, ViolStatus, Violation0 = GetViolation(CBIndex, X0)
		if FVStatus > 0 {
			return 2, 0.0
		} // numerical error
		if ViolStatus > 0 {
			return 1, 0.0
		} // constraint satisfied at start point so bail out
		FVStatus, ViolStatus, Violation1 = GetViolation(CBIndex, X1)
		if FVStatus > 0 {
			return 2, 0.0
		} // numerical error
		if ViolStatus > 0 {
			return 0, 1.0
		} // constraint satisfied at end point so current CV length OK
	} else {
		// It's a variable bound
		Lower = lp.LP.Cols[CBIndex].BndLo
		Upper = lp.LP.Cols[CBIndex].BndUp
		Violation0 = 0.0
		if X0[CBIndex] < Lower-featol {
			Violation0 = Lower - X0[CBIndex]
		}
		if X0[CBIndex] > Upper+featol {
			Violation0 = Upper - X0[CBIndex]
		}
		if Violation0 == 0.0 {
			return 1, 0.0
		} // bounds satisfied so bail out
		Violation1 = 0.0
		if X1[CBIndex] < Lower-featol {
			Violation1 = Lower - X1[CBIndex]
		}
		if X1[CBIndex] > Upper+featol {
			Violation1 = Upper - X1[CBIndex]
		}
		if Violation1 == 0.0 {
			return 0, 1.0
		} // satisfied at update point
	}
	Diff = Violation1 - Violation0
	if math.Abs(Diff) < featol {
		return 1, 0.0
	} // difference is below tolerance
	if (Violation0 > 0 && Diff > 0) || (Violation0 < 0 && Diff < 0) {
		return 1, 0.0
	} // vector is making violation worse
	if math.IsNaN(-Violation0 / Diff) {
		fmt.Println("Multiplier is NaN: aborting GetMultiplier")
		return 2, 0.0
	}
	//test
	//if -Violation0/Diff > 1000.0 {fmt.Println("Large multiplier:",-Violation0/Diff)}
	return 0, -Violation0 / Diff
}

//======================================================================================================
// Given 3 input points (Pt0, Pt1, Pt2) and the metric recorded at each of these points (Y0, Y1, Y2),
// find a quadratic interpolation and then find and return the minimum point.
// Assumptions: (i) these three points are in a line along some n-vector, so the x axis is just
// distance along the vector, (ii) the vector starts at Pt0 and proceeds through Pt1 to Pt2,
// (iii) we set x0=0 and x1=1, so can calculate x2 as some multiplier of the x1-x0 distance, and
// the output x will be in the same units, (iv) the metric for the second point is better than
// the metric for the first point (easy to obtain if the second point is always the incumbent).
// This is set up with SFD in mind as the metric, but it could also be applied to SINF.
// Status: 0(no problems), 1(some difficulty, so ignore results)
// MinPt: the actual point in n-space where the minimum of the quadratic fit curve appears
func QuadApprox(Pt0, Pt1, Pt2 []float64, Y0, Y1, Y2 float64) (Status int, MinPt []float64) {

	Vector := make([]float64, lp.LP.NumCols)
	MinPt = make([]float64, lp.LP.NumCols)
	var a, b, rhold1, rhold2 float64
	var Vector1Length float64
	var X0, X1, X2, XMin float64

	// Calculate the X values. We let X0=0 and X1=1, i.e. these are multiples of Vector1Length
	rhold1 = 0.0
	rhold2 = 0.0
	for j := 0; j < lp.LP.NumCols; j++ {
		Vector[j] = Pt1[j] - Pt0[j]
		rhold1 = rhold1 + Vector[j]*Vector[j]
		rhold2 = rhold2 + (Pt2[j]-Pt0[j])*(Pt2[j]-Pt0[j])
	}
	Vector1Length = math.Sqrt(rhold1)
	X0 = 0.0
	X1 = 1.0
	X2 = math.Sqrt(rhold2) / Vector1Length

	// Now calculate the numerator a and denominator b of the calculation for the minimum X
	a = (2.0*Y0)/((X0-X1)*(X0-X2)) + (2.0*Y1)/((X1-X0)*(X1-X2)) + (2.0*Y2)/((X2-X0)*(X2-X1))
	if a < featol {
		return 1, Pt2
	}
	b = (Y0*X2+Y0*X1)/((X0-X1)*(X0-X2)) + (Y1*X2+Y1*X0)/((X1-X0)*(X1-X2)) + (Y2*X1+Y2*X0)/((X2-X0)*(X2-X1))
	XMin = b / a

	for j := 0; j < lp.LP.NumCols; j++ {
		MinPt[j] = Pt0[j] + XMin*Vector[j]
	}
	return 0, MinPt

}

//=====================================================================================================
// Given two constraints, return the angle between them
// Status: 0(angle returned), 1(no intersection), 2(numerical problem)
func AngleConCon(Con1, Con2 int) (Status int, AngleOut float64) {

	var Length1, Length2 float64
	var Dot float64
	var El1, El2, Var1, Var2 int
	var Value1, Value2 float64
	var NumInCommon int = 0

	Length1 = 0.0
	Length2 = 0.0
	Dot = 0.0
	for i := 0; i < lp.LP.Rows[Con1].NumEl; i++ {
		El1 = lp.LP.Rows[Con1].ElList[i]
		Var1 = lp.Element[El1].Col
		Value1 = lp.Element[El1].Value
		Length1 = Length1 + Value1*Value1
		for j := 0; j < lp.LP.Rows[Con2].NumEl; j++ {
			El2 = lp.LP.Rows[Con2].ElList[j]
			Var2 = lp.Element[El2].Col
			if Var1 == Var2 {
				NumInCommon++
				Dot = Dot + Value1*lp.Element[El2].Value
				break
			}
		}
	}
	if NumInCommon == 0 {
		return 1, 0.0
	} // No common dimensions

	for i := 0; i < lp.LP.Rows[Con2].NumEl; i++ {
		El2 = lp.LP.Rows[Con2].ElList[i]
		Value2 = lp.Element[El2].Value
		Length2 = Length2 + Value2*Value2
	}

	Length1 = math.Sqrt(Length1)
	Length2 = math.Sqrt(Length2)
	if Length1*Length2 < featol {
		return 2, 0.0
	}

	AngleOut = math.Acos(Dot / (Length1 * Length2))
	return 0, AngleOut

}

//=========================================================================================
// Given a constraint and a variable, return the angle between them if the variable has bounds
// Status: 0(angle returned), 1(no intersection), 2(numerical problem)
func AngleConVarb(Con, Varb int) (Status int, AngleOut float64) {
	var Intersect bool = false
	var Value1 float64 = 0.0
	var Elem int
	var Length float64 = 0.0

	if lp.LP.Cols[Varb].BndLo <= -plinfy && lp.LP.Cols[Varb].BndUp >= plinfy {
		return 1, 0.0
	}
	for i := 0; i < lp.LP.Rows[Con].NumEl; i++ {
		Elem = lp.LP.Rows[Con].ElList[i]
		Length = Length + lp.Element[Elem].Value*lp.Element[Elem].Value
		if lp.Element[Elem].Col == Varb {
			// The constraint involves the variable
			Value1 = lp.Element[Elem].Value
			Intersect = true
		}
	}

	if !Intersect {
		return 1, 0.0
	}
	Length = math.Sqrt(Length)
	if Length < featol {
		return 2, 0.0
	}
	return 0, math.Acos(Value1 / Length)
}

//=====================================================================================================
// Given two row constraints, or a row constraint and a bound, return the angle between them
// Inputs: Con1 must be a row constraint, Con2 can be a row constraint or a bound
//   Con2Type: 0(row constraint) or 1(variable bound)
// Status: 0(angle returned), 1(no intersection), 2(numerical problem)
func AngleFV(Con1 int, Mult1 float64, Con2 int, Con2Type int, Mult2 float64) (Status int, AngleOut float64) {

	var Length1, Length2 float64
	var Dot float64
	var El1, El2, Var1, Var2 int
	var Value1, Value2 float64
	var NumInCommon int = 0

	Length1 = 0.0
	Length2 = 0.0
	Dot = 0.0
	for i := 0; i < lp.LP.Rows[Con1].NumEl; i++ {
		El1 = lp.LP.Rows[Con1].ElList[i]
		Var1 = lp.Element[El1].Col
		Value1 = lp.Element[El1].Value * Mult1
		Length1 = Length1 + Value1*Value1
		if Con2Type == 0 {
			// Con2 is a row constraint
			for j := 0; j < lp.LP.Rows[Con2].NumEl; j++ {
				El2 = lp.LP.Rows[Con2].ElList[j]
				Var2 = lp.Element[El2].Col
				if Var1 == Var2 {
					NumInCommon++
					Dot = Dot + Value1*lp.Element[El2].Value*Mult2
					break
				}
			}
		} else if Var1 == Con2 {
			// Con2 is a variable bound and Con1 contains this variable
			NumInCommon++
			Dot = Value1 * Mult2
		}
	}
	if NumInCommon == 0 {
		return 1, 0.0
	} // No common dimensions

	if Con2Type == 0 {
		for i := 0; i < lp.LP.Rows[Con2].NumEl; i++ {
			El2 = lp.LP.Rows[Con2].ElList[i]
			Value2 = lp.Element[El2].Value * Mult2
			Length2 = Length2 + Value2*Value2
		}
	} else {
		Length2 = Mult2 * Mult2
	}
	Length1 = math.Sqrt(Length1)
	Length2 = math.Sqrt(Length2)
	if Length1*Length2 < featol {
		return 2, 0.0
	}

	AngleOut = math.Acos(Dot / (Length1 * Length2))
	return 0, AngleOut

}

//=============================================================================================
// Checks to see whether an input point should overwrite one of the existing swarm points
func UpdateSwarm(PtIn []float64, SFDin float64, NINFin int) {
	// local variables
	var WorstSwarmEl int

	if NINFin > WorstNINF {
		return
	}
	if (NINFin == WorstNINF) && (SFDin > SwarmSFD[WorstNINFel]) {
		return
	}
	// The input point is better than the worst swarm point, so it overwrites it
	copy(Swarm[WorstNINFel], PtIn)
	SwarmNINF[WorstNINFel] = NINFin
	SwarmSFD[WorstNINFel] = SFDin
	if NINFin < SmallestNINF {
		SmallestNINF = NINFin
	}
	// Update data about the worst point
	WorstSwarmEl = 0

	for i := 1; i < MaxSwarmPts; i++ { // note that the loop starts at 1 on purpose
		if SwarmNINF[i] < SwarmNINF[WorstSwarmEl] {
			continue
		}
		if (SwarmNINF[i] == SwarmNINF[WorstSwarmEl]) && (SwarmSFD[i] < SwarmSFD[WorstSwarmEl]) {
			continue
		}
		WorstSwarmEl = i
	}
	WorstNINF = SwarmNINF[WorstSwarmEl]
	WorstNINFel = WorstSwarmEl
	if PrintLevel > 0 {
		fmt.Println("NINF updated by NINF:", NINFin, "SFD:", SFDin, "New worst NINF:", WorstNINF, "SFD:", SwarmSFD[WorstSwarmEl], "Smallest NINF:", SmallestNINF)
	}
	return
}

//=============================================================================================
// Checks to see whether an input point should overwrite one of the existing swarm points
// THIS VERSION ONLY UPDATES A PARTICULAR POINT, NOT WORST SWARM POINT
func UpdateSwarm1(PtIn []float64, PtNum int, SFDin float64, NINFin int) {
	// local variables
	var WorstSwarmEl int

	if NINFin > SwarmNINF[PtNum] {
		return
	}
	if (NINFin == SwarmNINF[PtNum]) && (SFDin > SwarmSFD[PtNum]) {
		return
	}
	// The input point is better than the input swarm point, so it overwrites it
	copy(Swarm[PtNum], PtIn)
	SwarmNINF[PtNum] = NINFin
	SwarmSFD[PtNum] = SFDin
	if NINFin < SmallestNINF {
		SmallestNINF = NINFin
	}
	// Update data about the worst point
	WorstSwarmEl = 0

	for i := 1; i < MaxSwarmPts; i++ { // note that the loop starts at 1 on purpose
		if SwarmNINF[i] < SwarmNINF[WorstSwarmEl] {
			continue
		}
		if (SwarmNINF[i] == SwarmNINF[WorstSwarmEl]) && (SwarmSFD[i] < SwarmSFD[WorstSwarmEl]) {
			continue
		}
		WorstSwarmEl = i
	}
	WorstNINF = SwarmNINF[WorstSwarmEl]
	WorstNINFel = WorstSwarmEl
	if PrintLevel > 0 {
		fmt.Println("NINF updated by NINF:", NINFin, "SFD:", SFDin, "New worst NINF:", WorstNINF, "SFD:", SwarmSFD[WorstSwarmEl], "Smallest NINF:", SmallestNINF)
	}
	return
}

//================================================================================================
// Given a point, this routine returns a consensus vector.
// Mode:
//   0(basic CV),
//   1(basic CV with superimposed max FD vector if basic CV too short)
//   2(CV weighted by lengths of feasibility vectors)
//   3(SUM method)
// Status:
//   0(success with CV returned)
//   1(CV is too short)
//   2(numerical or other failure)
func GetCV(Pt []float64, Mode int) (Status int, CV []float64, SFD float64, SINF float64, NINF int) {

	//	var NINF int = 0 // Number of violated constraints
	//	var SINF float64 = 0.0                           // Sum of LHS-RHS violations
	//	var SFD float64 = 0.0 // Sum of the feasibility distance vectors
	var Violation float64                       // The constraint violation
	var FVLength float64                        // Length of the feasibility vector
	NumViol := make([]int, len(Pt))             // Number of violations
	SumViol := make([]float64, len(Pt))         // Sum of violations (in terms of feasibility vector components)
	SumWeightedViol := make([]float64, len(Pt)) // Sum of the weighted violations (weighted by violation)
	SumWeights := make([]float64, len(Pt))      // Sum of the weights
	//	CCPoint := make([]float64, len(Pt))         // Constraint consensus point
	//	CV := make([]float64, len(Pt))              // Consensus Vector
	//	BestPt := make([]float64, len(Pt))          // The best point seen in this CC run
	//	var BestPtSFD float64 = plinfy
	FVMaxViol := make([]float64, len(Pt))     // Captures the individual feasibility vector associated with the maximum LHS-RHS violation
	FVMaxFVLength := make([]float64, len(Pt)) // Captures the individual feasibility vector associated with the largest feasibility vector
	var MaxViol float64                       // Captures the maximum LHS-RHS violation seen
	var MaxFVLength float64                   // Catures the maximum feasibility vector length seen
	var NewMaxViol bool                       // Boolean to notice when a larger MaxViol is seen
	var NewMaxFVLength bool                   // Boolean to notice when a large MaxFVLength is seen
	//	var Status int
	var FVStatus int = 0
	var ViolStatus int = 0
	var ElNum int  // Element number
	var ColNum int // Column number
	var rhold, rhold1 float64
	var CVLength float64
	//	var CVLengthLast float64
	//	var MaxMultiplier float64
	//	var NumMultipliers int
	//	var FDFar bool = false
	//var rhold1 float64

	//var Status int = 0

	//Status=0

	// Zero the accumulators
	NINF = 0
	SFD = 0.0
	SINF = 0.0
	MaxViol = -plinfy
	MaxFVLength = -plinfy
	for i := range Pt {
		NumViol[i] = 0
		SumViol[i] = 0.0
		CV[i] = 0.0
		FVMaxViol[i] = 0.0
		FVMaxFVLength[i] = 0.0
		SumWeightedViol[i] = 0.0
		SumWeights[i] = 0.0
	}

	// Run through the constraints
	for icon := 0; icon < lp.NumRows; icon++ {
		// Get the feasibility vector, if there is one

		//test
		if math.IsNaN(Pt[0]) {
			fmt.Println("***1 GetViolation called with NaN point in GetCV")
		}
		FVStatus, ViolStatus, Violation = GetViolation(icon, Pt)

		//test
		//fmt.Println("After GetViolation call for con",icon,"Violation:",Violation,"FVStatus:",FVStatus,"ViolStatus:",ViolStatus)

		if FVStatus > 0 {
			fmt.Println("Error evaluating feasibility status for constraint", icon, ". Skipping it in GetCV.")
			continue
		}
		if ViolStatus > 0 {
			// not violated, so skip
			continue
		}
		// Check length of feasibility vector
		rhold = 0.0 // Accumulates length of feasibility vector
		for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
			ElNum = lp.LP.Rows[icon].ElList[iel]
			ColNum = lp.Element[ElNum].Col
			rhold1 = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
			rhold = rhold + rhold1*rhold1
		}
		if rhold < Alpha*Alpha {
			// Feasibility vector is too short so skip this constraint
			continue
		}

		// Constraint is violated
		NINF++
		FVLength = math.Sqrt(rhold)
		SFD = SFD + FVLength
		SINF = SINF + math.Abs(Violation)

		//			// Instead of classing a constraint as violated if the feasibility vector is too long,
		//			// use the classical LHS-RHS violation tolerance
		//			if math.Abs(Violation) <= featol {
		//				continue
		//			}

		// If using SINF
		NewMaxViol = false
		if math.Abs(Violation) > MaxViol {
			// There's a new maximum violation
			MaxViol = math.Abs(Violation)
			NewMaxViol = true
			// Empty the old FVMaxViol vector, fill it in the following step
			for j := 0; j < lp.LP.NumCols; j++ {
				FVMaxViol[j] = 0.0
			}
		}
		// If using SFD
		NewMaxFVLength = false
		if FVLength > MaxFVLength {
			// There is a new longest feasibility vector
			MaxFVLength = FVLength
			NewMaxFVLength = true
			// Empty the old FVMaxFVLength, fill it in the next step
			for j := 0; j < lp.NumCols; j++ {
				FVMaxFVLength[j] = 0.0
			}
		}

		// Calculate the relevant elements of the feasibility vector
		for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
			ElNum = lp.LP.Rows[icon].ElList[iel]
			ColNum = lp.Element[ElNum].Col
			NumViol[ColNum]++
			SumViol[ColNum] = SumViol[ColNum] + Violation*lp.Element[ElNum].Value/lp.LP.Rows[icon].GradVecLenSq
			SumWeightedViol[ColNum] = SumWeightedViol[ColNum] + Violation*lp.Element[ElNum].Value/lp.LP.Rows[icon].GradVecLenSq*math.Abs(Violation)
			SumWeights[ColNum] = SumWeights[ColNum] + math.Abs(Violation)
			if NewMaxViol {
				FVMaxViol[ColNum] = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
			}
			if NewMaxFVLength {
				FVMaxFVLength[ColNum] = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
			}
		}
	} // end of loop on the constraints

	// Run through the bounds looking for violations and making appropriate updates
	for ivar := 0; ivar < lp.NumCols; ivar++ {
		if Pt[ivar] >= lp.LP.Cols[ivar].BndLo-Alpha {
			// greater than lower bound
			if Pt[ivar] <= lp.LP.Cols[ivar].BndUp+Alpha {
				// less than upper bound
				continue
			} else if Pt[ivar]-lp.LP.Cols[ivar].BndUp > Alpha {
				// upper bound violated by large enough amount
				NINF++
				NumViol[ivar]++
				rhold = lp.LP.Cols[ivar].BndUp - Pt[ivar]
				SumViol[ivar] = SumViol[ivar] + rhold
				SFD = SFD + math.Abs(rhold)
				SumWeightedViol[ivar] = SumViol[ivar]
				SumWeights[ivar] = SumWeights[ivar] + rhold

				if Pt[ivar]-lp.LP.Cols[ivar].BndUp > MaxViol {
					// There's a new maximum violation
					MaxViol = Pt[ivar] - lp.LP.Cols[ivar].BndUp
					// Empty the old FVMaxViol vector, fill it in the following step
					for j := 0; j < lp.LP.NumCols; j++ {
						FVMaxViol[j] = 0.0
					}
					FVMaxViol[ivar] = lp.LP.Cols[ivar].BndUp - Pt[ivar]
				}
				if math.Abs(rhold) > MaxFVLength {
					// There's a new longest FV
					MaxFVLength = math.Abs(rhold)
					// Empty the old FVMaxFVLength and fill it in following step
					for j := 0; j < lp.NumCols; j++ {
						FVMaxFVLength[j] = 0.0
					}
					FVMaxFVLength[ivar] = lp.LP.Cols[ivar].BndUp - Pt[ivar]
				}

			}
		} else if lp.LP.Cols[ivar].BndLo-Pt[ivar] > Alpha {
			// lower bound violated by large enough amount
			NINF++
			NumViol[ivar]++
			rhold = lp.LP.Cols[ivar].BndLo - Pt[ivar]
			SumViol[ivar] = SumViol[ivar] + rhold
			SFD = SFD + rhold
			SumWeightedViol[ivar] = SumViol[ivar]
			SumWeights[ivar] = SumWeights[ivar] + lp.LP.Cols[ivar].BndLo - Pt[ivar]

			if lp.LP.Cols[ivar].BndLo-Pt[ivar] > MaxViol {
				// There's a new maximum violation
				MaxViol = lp.LP.Cols[ivar].BndLo - Pt[ivar]
				// Empty the old FVMaxViol vector, fill it in the following step
				for j := 0; j < lp.LP.NumCols; j++ {
					FVMaxViol[j] = 0.0
				}
				FVMaxViol[ivar] = lp.LP.Cols[ivar].BndLo - Pt[ivar]
			}
			if rhold > MaxFVLength {
				// There's a new longest FV
				MaxFVLength = rhold
				//Empty the old FVMaxFVLength and fill it in the following step
				for j := 0; j < lp.NumCols; j++ {
					FVMaxFVLength[j] = 0.0
				}
				FVMaxFVLength[ivar] = rhold
			}

		}
	}

	if NINF == 0 {
		// Exit successfully with a feasible point
		for i := 0; i < lp.NumCols; i++ {
			CV[i] = 0.0
		}
		return 0, CV, SFD, SINF, 0
	}

	switch Mode {

	case 0, 1: // Basic CC or superimposed FD vector
		// Calculate the consensus vector vector and it's length
		rhold = 0.0 // Accumulates the squared elements of the consensus vector
		for ivar := 0; ivar < lp.NumCols; ivar++ {
			if NumViol[ivar] == 0 {
				CV[ivar] = 0.0
				continue
			}
			CV[ivar] = SumViol[ivar] / float64(NumViol[ivar]) // For standard basic CC
			rhold = rhold + CV[ivar]*CV[ivar]
		}
		CVLength = math.Sqrt(rhold)
		if CVLength < Beta {
			//CV is too short
			if Mode == 0 {
				// Basic CV
				return 1, CV, SFD, SINF, NINF
			}
			// Mode is 1, which superimposes the longest FD vector on top on the basic CV
			rhold = 0.0
			for ivar := 0; ivar < lp.NumCols; ivar++ {
				if FVMaxFVLength[ivar] != 0.0 {
					CV[ivar] = FVMaxFVLength[ivar]
				}
				rhold = rhold + CV[ivar]*CV[ivar]
			}
			CVLength = math.Sqrt(rhold)
			if CVLength < Beta {
				return 1, CV, SFD, SINF, NINF
			}
			return 0, CV, SFD, SINF, NINF
		}
		return 0, CV, SFD, SINF, NINF

	case 2: // CV weighted by lengths of feasibility vectors
		rhold = 0.0 // Accumulates the squared elements of the consensus vector
		for ivar := 0; ivar < lp.NumCols; ivar++ {
			if NumViol[ivar] == 0 {
				CV[ivar] = 0.0
				continue
			}
			CV[ivar] = SumWeightedViol[ivar] / SumWeights[ivar] // For violation-weighted CC
			rhold = rhold + CV[ivar]*CV[ivar]
		}
		CVLength = math.Sqrt(rhold)
		if CVLength < Beta {
			//CV is too short
			return 1, CV, SFD, SINF, NINF
		}
		return 0, CV, SFD, SINF, NINF

	case 3: // SUM method
		rhold = 0.0 // Accumulates the squared elements of the consensus vector
		for ivar := 0; ivar < lp.NumCols; ivar++ {
			if NumViol[ivar] == 0 {
				CV[ivar] = 0.0
				continue
			}
			CV[ivar] = SumViol[ivar] // For the SUM method
			rhold = rhold + CV[ivar]*CV[ivar]
		}
		CVLength = math.Sqrt(rhold)
		if CVLength < Beta {
			//CV is too short
			return 1, CV, SFD, SINF, NINF
		}
		return 0, CV, SFD, SINF, NINF

	} // end of switch on Mode

	//***righthere: Things to do:
	// potentially update all of the incumbents now this point is assessed
	// should return length of CV too, since it is used in some of the CC methods
	return 0, CV, SFD, SINF, NINF
}

//================================================================================================
// Given a point, this routine returns several versions of the consensus vector.
// Outputs:
//   Status:
//     0(success with CV returned)
//	   1(success with feasible point returned)
//     2(numerical or other failure)
//   CV0(basic CV),
//   CV1(basic CV with superimposed max FD vector if basic CV too short)
//   CV2(CV weighted by lengths of feasibility vectors)
//   CV3(SUM method)
//	 CV0Short: false(long enough), true(too short)
//   CV1Short, CV2Status, CV3Status: as above
//   SFD: sum of the feasibility distances
//	 SINF: sum of the infeasibilities
//   NINF: number of infeasibilities
//
func GetCV1(Pt []float64) (Status int, CV0 []float64, CV1 []float64, CV2 []float64, CV3 []float64,
	CV0Short bool, CV1Short bool, CV2Short bool, CV3Short bool, SFD float64, SINF float64, NINF int) {

	var Violation float64                       // The constraint violation
	var FVLength float64                        // Length of the feasibility vector
	NumViol := make([]int, len(Pt))             // Number of violations
	SumViol := make([]float64, len(Pt))         // Sum of violations (in terms of feasibility vector components)
	SumWeightedViol := make([]float64, len(Pt)) // Sum of the weighted violations (weighted by violation)
	SumWeights := make([]float64, len(Pt))      // Sum of the weights
	FVMaxViol := make([]float64, len(Pt))       // Captures the individual feasibility vector associated with the maximum LHS-RHS violation
	FVMaxFVLength := make([]float64, len(Pt))   // Captures the individual feasibility vector associated with the largest feasibility vector
	var MaxViol float64                         // Captures the maximum LHS-RHS violation seen
	var MaxFVLength float64                     // Catures the maximum feasibility vector length seen
	var NewMaxViol bool                         // Boolean to notice when a larger MaxViol is seen
	var NewMaxFVLength bool                     // Boolean to notice when a large MaxFVLength is seen
	var FVStatus int = 0
	var ViolStatus int = 0
	var ElNum int  // Element number
	var ColNum int // Column number
	var rhold, rhold0, rhold1, rhold2, rhold3 float64
	CV0 = make([]float64, len(Pt)) // Consensus Vector
	CV1 = make([]float64, len(Pt)) // Consensus Vector
	CV2 = make([]float64, len(Pt)) // Consensus Vector
	CV3 = make([]float64, len(Pt)) // Consensus Vector

	// Zero the accumulators
	NINF = 0
	SFD = 0.0
	SINF = 0.0
	MaxViol = -plinfy
	MaxFVLength = -plinfy
	for i := range Pt {
		NumViol[i] = 0
		SumViol[i] = 0.0
		CV0[i] = 0.0
		CV1[1] = 0.0
		CV2[i] = 0.0
		CV3[0] = 0.0
		FVMaxViol[i] = 0.0
		FVMaxFVLength[i] = 0.0
		SumWeightedViol[i] = 0.0
		SumWeights[i] = 0.0
	}
	CV0Short = false
	CV1Short = false
	CV2Short = false
	CV3Short = false

	// Run through the constraints
	for icon := 0; icon < lp.NumRows; icon++ {
		// Get the feasibility vector, if there is one

		//test
		if math.IsNaN(Pt[0]) {
			fmt.Println("***1 GetViolation called with NaN point in GetCV")
		}
		FVStatus, ViolStatus, Violation = GetViolation(icon, Pt)

		if FVStatus > 0 {
			fmt.Println("Error evaluating feasibility status for constraint", icon, ". Skipping it in GetCV.")
			continue
		}
		if ViolStatus > 0 {
			// not violated, so skip
			continue
		}
		// Check length of feasibility vector
		rhold = 0.0 // Accumulates length of feasibility vector
		for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
			ElNum = lp.LP.Rows[icon].ElList[iel]
			ColNum = lp.Element[ElNum].Col
			rhold1 = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
			rhold = rhold + rhold1*rhold1
		}
		if rhold < Alpha*Alpha {
			// Feasibility vector is too short so skip this constraint
			continue
		}

		// Constraint is violated
		NINF++
		FVLength = math.Sqrt(rhold)
		SFD = SFD + FVLength
		SINF = SINF + math.Abs(Violation)

		//			// Instead of classing a constraint as violated if the feasibility vector is too long,
		//			// use the classical LHS-RHS violation tolerance
		//			if math.Abs(Violation) <= featol {
		//				continue
		//			}

		// If using SINF
		NewMaxViol = false
		if math.Abs(Violation) > MaxViol {
			// There's a new maximum violation
			MaxViol = math.Abs(Violation)
			NewMaxViol = true
			// Empty the old FVMaxViol vector, fill it in the following step
			for j := 0; j < lp.LP.NumCols; j++ {
				FVMaxViol[j] = 0.0
			}
		}
		// If using SFD
		NewMaxFVLength = false
		if FVLength > MaxFVLength {
			// There is a new longest feasibility vector
			MaxFVLength = FVLength
			NewMaxFVLength = true
			// Empty the old FVMaxFVLength, fill it in the next step
			for j := 0; j < lp.NumCols; j++ {
				FVMaxFVLength[j] = 0.0
			}
		}

		// Calculate the relevant elements of the feasibility vector
		for iel := 0; iel < lp.LP.Rows[icon].NumEl; iel++ {
			ElNum = lp.LP.Rows[icon].ElList[iel]
			ColNum = lp.Element[ElNum].Col
			NumViol[ColNum]++
			SumViol[ColNum] = SumViol[ColNum] + Violation*lp.Element[ElNum].Value/lp.LP.Rows[icon].GradVecLenSq
			SumWeightedViol[ColNum] = SumWeightedViol[ColNum] + Violation*lp.Element[ElNum].Value/lp.LP.Rows[icon].GradVecLenSq*math.Abs(Violation)
			SumWeights[ColNum] = SumWeights[ColNum] + math.Abs(Violation)
			if NewMaxViol {
				FVMaxViol[ColNum] = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
			}
			if NewMaxFVLength {
				FVMaxFVLength[ColNum] = Violation * lp.Element[ElNum].Value / lp.LP.Rows[icon].GradVecLenSq
			}
		}
	} // end of loop on the constraints

	// Run through the bounds looking for violations and making appropriate updates
	for ivar := 0; ivar < lp.NumCols; ivar++ {
		if Pt[ivar] >= lp.LP.Cols[ivar].BndLo-Alpha {
			// greater than lower bound
			if Pt[ivar] <= lp.LP.Cols[ivar].BndUp+Alpha {
				// less than upper bound
				continue
			} else if Pt[ivar]-lp.LP.Cols[ivar].BndUp > Alpha {
				// upper bound violated by large enough amount
				NINF++
				NumViol[ivar]++
				rhold = lp.LP.Cols[ivar].BndUp - Pt[ivar]
				SumViol[ivar] = SumViol[ivar] + rhold
				SFD = SFD + math.Abs(rhold)
				SumWeightedViol[ivar] = SumViol[ivar]
				SumWeights[ivar] = SumWeights[ivar] + rhold

				if Pt[ivar]-lp.LP.Cols[ivar].BndUp > MaxViol {
					// There's a new maximum violation
					MaxViol = Pt[ivar] - lp.LP.Cols[ivar].BndUp
					// Empty the old FVMaxViol vector, fill it in the following step
					for j := 0; j < lp.LP.NumCols; j++ {
						FVMaxViol[j] = 0.0
					}
					FVMaxViol[ivar] = lp.LP.Cols[ivar].BndUp - Pt[ivar]
				}
				if math.Abs(rhold) > MaxFVLength {
					// There's a new longest FV
					MaxFVLength = math.Abs(rhold)
					// Empty the old FVMaxFVLength and fill it in following step
					for j := 0; j < lp.NumCols; j++ {
						FVMaxFVLength[j] = 0.0
					}
					FVMaxFVLength[ivar] = lp.LP.Cols[ivar].BndUp - Pt[ivar]
				}

			}
		} else if lp.LP.Cols[ivar].BndLo-Pt[ivar] > Alpha {
			// lower bound violated by large enough amount
			NINF++
			NumViol[ivar]++
			rhold = lp.LP.Cols[ivar].BndLo - Pt[ivar]
			SumViol[ivar] = SumViol[ivar] + rhold
			SFD = SFD + rhold
			SumWeightedViol[ivar] = SumViol[ivar]
			SumWeights[ivar] = SumWeights[ivar] + lp.LP.Cols[ivar].BndLo - Pt[ivar]

			if lp.LP.Cols[ivar].BndLo-Pt[ivar] > MaxViol {
				// There's a new maximum violation
				MaxViol = lp.LP.Cols[ivar].BndLo - Pt[ivar]
				// Empty the old FVMaxViol vector, fill it in the following step
				for j := 0; j < lp.LP.NumCols; j++ {
					FVMaxViol[j] = 0.0
				}
				FVMaxViol[ivar] = lp.LP.Cols[ivar].BndLo - Pt[ivar]
			}
			if rhold > MaxFVLength {
				// There's a new longest FV
				MaxFVLength = rhold
				//Empty the old FVMaxFVLength and fill it in the following step
				for j := 0; j < lp.NumCols; j++ {
					FVMaxFVLength[j] = 0.0
				}
				FVMaxFVLength[ivar] = rhold
			}

		}
	}

	if NINF == 0 {
		// Exit successfully with a feasible point
		for i := 0; i < lp.NumCols; i++ {
			CV0[i] = 0.0
			CV1[i] = 0.0
			CV2[i] = 0.0
			CV3[i] = 0.0
		}
		return 1, CV0, CV1, CV2, CV3, true, true, true, true, 0.0, 0.0, 0
	}

	// Now calculate the various versions of the consensus vector
	rhold0 = 0.0 // accumulators for the lengths of the consensus vectors
	rhold1 = 0.0
	rhold2 = 0.0
	rhold3 = 0.0
	for ivar := 0; ivar < lp.NumCols; ivar++ {
		if NumViol[ivar] == 0 {
			CV0[ivar] = 0.0
			CV1[ivar] = 0.0
			CV2[ivar] = 0.0
			CV3[ivar] = 0.0
			continue
		}
		CV0[ivar] = SumViol[ivar] / float64(NumViol[ivar]) // For standard basic CC
		rhold0 = rhold0 + CV0[ivar]*CV0[ivar]
		if FVMaxFVLength[ivar] != 0.0 { // For longest FV imposed on standard CV
			CV1[ivar] = FVMaxFVLength[ivar]
		} else {
			CV1[ivar] = CV0[ivar]
		}
		rhold1 = rhold1 + CV1[ivar]*CV1[ivar]
		CV2[ivar] = SumWeightedViol[ivar] / SumWeights[ivar] // For violation-weighted CC
		rhold2 = rhold2 + CV2[ivar]*CV2[ivar]
		CV3[ivar] = SumViol[ivar] // For the SUM method
		rhold3 = rhold3 + CV3[ivar]*CV3[ivar]
	}
	// Check the lengths of the consensus vectors
	if math.Sqrt(rhold0) < Beta {
		CV0Short = true
	}
	if math.Sqrt(rhold1) < Beta {
		CV1Short = true
	}
	if math.Sqrt(rhold2) < Beta {
		CV2Short = true
	}
	if math.Sqrt(rhold3) < Beta {
		CV3Short = true
	}

	return 0, CV0, CV1, CV2, CV3, CV0Short, CV1Short, CV2Short, CV3Short, SFD, SINF, NINF

}
//=======================================================================================
// Given an input point at which some of the variables may violate their bounds, this 
// routine returns an output point in which all of the variables have been reset onto their
// closest bound, if necessary.
func EnforceBounds(PtIn []float64) (PtOut []float64) {
	PtOut = make([]float64, len(PtIn))
	for j:=0; j<lp.NumCols; j++ {
		if PtIn[j] < lp.LP.Cols[j].BndLo {
			PtOut[j] = lp.LP.Cols[j].BndLo
			continue
		}
		if PtIn[j] > lp.LP.Cols[j].BndUp {
			PtOut[j] = lp.LP.Cols[j].BndUp
			continue
		}
		PtOut[j] = PtIn[j]
	}
	return
}

//===========================================================================================
// Sorts the row constraints in order from most to least impact, where impact is measured by
// the number of other row constraints impacted by a given constraint
func SortByImpact () () {
	ImpactData := make([]IMPACT, lp.NumRows) 
	ImpactList = make([]int, lp.NumRows)
	Impacted := make([]bool, lp.NumRows)	// Scratch list of which rows are impacted by a given row
	var iel, ivar int
	
	for i:=0; i<lp.NumRows; i++ {
		ImpactData[i].Row = i
		ImpactData[i].Sum = 0
		//for every row
		if lp.LP.Rows[i].Type == "N" {continue}
		for j:=0; j<lp.NumRows; j++ {
			Impacted[j] = false
		}
		//for every variable in the row
		for ii:=0; ii<lp.LP.Rows[i].NumEl; ii++ {
			iel = lp.LP.Rows[i].ElList[ii]
			ivar = lp.Element[iel].Col
			//for every row that variable appears in
			for j:=0; j<lp.LP.Cols[ivar].NumEl; j++ {
				jel:=lp.LP.Cols[ivar].ElList[j]
				jrow:=lp.Element[jel].Row
				if lp.LP.Rows[jrow].Type == "N" {continue}
				Impacted[jrow] = true
			}
		}
		//Count up the impact for that row
		for j:=0; j<lp.NumRows; j++ {
			if Impacted[j] {ImpactData[i].Sum++}
		}
		//Don't count yourself in the impact list
		if ImpactData[i].Sum > 0 {ImpactData[i].Sum = ImpactData[i].Sum - 1}
	}
	
	// Now sort the impact list
	sort.Sort(BySum(ImpactData))
	// test
	//fmt.Println("Impact Data:", ImpactData)
	
	// Reverse the sorted list so it goes highest to lowest
	j:=-1
	for i:=lp.NumRows-1; i>-1; i=i-1 {
		j++
		ImpactList[j] = ImpactData[i].Row
	}
	return
}
//=================================================================================
// These three small functions are needed for sorting ImpactData
func (s BySum) Len() int {
	return len(s)
}
func (s BySum) Swap(i, j int) {
	s[i], s[j] = s[j], s[i]
}
func (s BySum) Less(i, j int) bool {
	return s[i].Sum < s[j].Sum
}
