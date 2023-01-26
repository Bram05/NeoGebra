#pragma once

#include "Maths/Equation.h"

class Graph;

class GraphComputeShaderManager
{
public:
	GraphComputeShaderManager(const std::string& name, float width, float height);
	~GraphComputeShaderManager();

	std::pair<std::vector<unsigned int>, std::vector<unsigned int>> CreateFirstCompShaders(const std::string& name, std::shared_ptr<OrAnd> equations) const;
	unsigned int CreateOtherComputeShader(const std::string& name) const;
	void RunComputeShaders(Graph* graph, float midCoordX, float midCoordY, float unitLengthPixels) const;
	unsigned int CreateTexture() const;

	void SetGraphSize(int width, int height);

	void SetUniform(unsigned int loc, const std::array<float, 4>& vec) const;

private:
	unsigned int m_CompShader2;
	unsigned int m_CompShader3;
	unsigned int m_IntermediateTexture;
	int m_MaxNumberOfTextureUnits;
	int m_Width, m_Height; // Stored in pixels
	std::string m_Name;

	unsigned int RunRecursive(Graph* graph, std::shared_ptr<OrAnd> currentObj, float midCoordX, float midCoordY, float unitLengthPixels) const;
};