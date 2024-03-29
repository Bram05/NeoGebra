#pragma once

#include "Maths/Equation.h"

class Graph;

class GraphComputeShaderManager
{
public:
	GraphComputeShaderManager(const std::string& name, float width, float height);
	~GraphComputeShaderManager();

	void CreateShader(Graph* graph, const std::string& name) const;
	unsigned int CreateOtherComputeShader(const std::string& name) const;
	void RunComputeShaders(Graph* graph, float midCoordX, float midCoordY, float unitLengthPixels) const;
	unsigned int CreateTexture() const;

	void SetGraphSize(int width, int height);

	void SetUniform(unsigned int loc, const std::array<float, 4>& vec) const;

private:
	unsigned int m_CompShader2, m_CompShader3, m_CompShader4;
	unsigned int m_IntermediateTexture1;
	std::vector<unsigned int> m_IntermediateTextures2;
	int m_MaxNumberOfTextureUnits;
	int m_Width, m_Height; // Stored in pixels
	std::string m_Name;
};