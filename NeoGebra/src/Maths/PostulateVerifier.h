#pragma once
#include "Model.h"
#include "Equation.h"

enum ParallelType
{
	NORESULT, ELLIPTIC, EUCLIDEAN, HYPERBOLIC
};

enum PostulateVerifierValues
{
	VALID, INVALID, UNKOWN, UNTESTED, BEINGTESTED
};

class PostulateVerifier
{
public:
	static PostulateVerifierValues I2(const Model& model);
	static PostulateVerifierValues I3(const Model& model);

	static PostulateVerifierValues B1(const Model& model);
	static PostulateVerifierValues B2(const Model& model);
	static PostulateVerifierValues B3(const Model& model);

	static PostulateVerifierValues C3(const Model& model);

	static PostulateVerifierValues DISTANCE(const Model& model);
	static ParallelType PARALLEL(const Model& model);
};