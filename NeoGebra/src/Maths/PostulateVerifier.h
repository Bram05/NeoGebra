#pragma once
#include "Model.h"
#include "Equation.h"

class PostulateVerifier
{
public:
	static bool I2(const Model& model);
	static bool I3(const Model& model);
};