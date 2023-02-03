#pragma once
#include "Model.h"
#include "Equation.h"

enum ParallelType
{
	ELLIPTIC, EUCLIDEAN, HYPERBOLIC
};

class PostulateVerifier
{
public:
	static bool I2(const Model& model);
	static bool I3(const Model& model);

	static bool B1(const Model& model);
	static bool B2(const Model& model);
	static bool B3(const Model& model);

	static bool C3(const Model& model);	

	static bool DISTANCE(const Model& model);
	static ParallelType PARALLEL(const Model& model);
};