#pragma once

class Graph;

class GraphComputeShaderManager
{
public:
	GraphComputeShaderManager(const std::string& name, float width, float height);
	~GraphComputeShaderManager();

	unsigned int CreateCompShader(const std::string name, const std::string& insertText) const;
	void RunComputeShader(Graph* graph, float midCoordX, float midCoordY, float unitLengthPixels) const;
	unsigned int CreateTexture() const;

	void SetGraphSize(float width, float height);

	void SetUniform(unsigned int loc, const std::array<float,4>& vec) const;

private:
	unsigned int m_CompShader2;
	unsigned int m_IntermediateTexture;
	int m_Width, m_Height; // Stored in pixels
	std::string m_Name;
};