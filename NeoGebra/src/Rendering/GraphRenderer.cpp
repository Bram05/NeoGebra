#include "GraphRenderer.h"

#include "GraphComputeShaderManager.h"
#include "Util.h"
#include "Application.h"

Graph::Graph(NEElement& el, const GraphComputeShaderManager& manager, float leftX, float rightX, float topY, float bottomY, float midCoordX, float midCoordY, float unitLengthPixels, const RGBColour& colour)
	: m_El{ el },
	m_Colour{ colour },
	m_Texture{ manager.CreateTexture() }
{
	m_CompShader1 = manager.CreateCompShader("graphShader1", m_El.getShader());
	// It is not needed to run the compute shader, because this will be done from GraphUI

	float buffer[16] = {
		leftX,	topY,	 0.0f, 1.0f,
		leftX,	bottomY, 0.0f, 0.0f,
		rightX,	bottomY, 1.0f, 0.0f,
		rightX,	topY,	 1.0f, 1.0f
	};
	unsigned int indices[6] = { // this buffer is technically not specific for every square but I think it's fine like this because of how small it is
		0, 1, 2,
		2, 3, 0
	};
	glGenVertexArrays(1, &m_Vao);
	glBindVertexArray(m_Vao);

	glGenBuffers(1, &m_Vb);
	glBindBuffer(GL_ARRAY_BUFFER, m_Vb);
	glBufferData(GL_ARRAY_BUFFER, sizeof(buffer), buffer, GL_STATIC_DRAW);

	glEnableVertexAttribArray(0);
	glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE, 4 * sizeof(float), 0);
	glEnableVertexAttribArray(1);
	glVertexAttribPointer(1, 2, GL_FLOAT, GL_FALSE, 4 * sizeof(float), (void*)(2 * sizeof(float)));

	glGenBuffers(1, &m_Ib);
	glBindBuffer(GL_ELEMENT_ARRAY_BUFFER, m_Ib);
	glBufferData(GL_ELEMENT_ARRAY_BUFFER, sizeof(indices), indices, GL_STATIC_DRAW);
}

Graph::~Graph()
{
	glDeleteBuffers(1, &m_Vb);
	glDeleteBuffers(1, &m_Ib);
	glDeleteVertexArrays(1, &m_Vao);
	glDeleteProgram(m_CompShader1);
	glDeleteTextures(1, &m_Texture);
}

GraphRenderer::GraphRenderer()
	: m_Shader("graphShader")
{
	setLineThickness(3); // Make sure these number are valid, because otherwise it will crash, because we can't display errors yet, since WindowUI is not fully constructed yet and not set in Application
	setPointSize(10);
}

GraphRenderer::~GraphRenderer()
{
}

void GraphRenderer::AddToRenderQueue(const std::shared_ptr<Graph>& graph)
{
	m_RenderQueue.push(graph);
}

void GraphRenderer::setLineThickness(int pixels) {
	if (pixels < 1) {
		Application::Get()->GetWindowUI()->DisplayError("Invalid line thickness: " + std::to_string(pixels) + "\nFalling back to default 3");
		pixels = 3;
	}
	m_LineThickness = pixels;
}

void GraphRenderer::setPointSize(int pixels) {
	if (pixels < 1) {
		Application::Get()->GetWindowUI()->DisplayError("Invalid point size: " + std::to_string(pixels) + "\nFalling back to default 10");
		pixels = 10;
	}
	m_PointSize = pixels;
}

void GraphRenderer::RenderQueue()
{
	m_Shader.Bind();
	while (!m_RenderQueue.empty())
	{
		std::shared_ptr<Graph> graph{ m_RenderQueue.front() };
		m_RenderQueue.pop();

		m_Shader.SetTexture(graph->m_Texture);
		RGBColour c = graph->m_Colour;
		m_Shader.SetUniform("u_Colour", std::array<float, 4>{ c.norm_r, c.norm_g, c.norm_b, c.norm_a });
		switch (graph->getElement().getType())
		{
		case point:
			m_Shader.SetUniform("u_Size", m_PointSize);
			break;
		case line:
		case notype:
			m_Shader.SetUniform("u_Size", m_LineThickness);
			break;
		default:
			std::cerr << "Unkown type!\n";
			Util::ExitDueToFailure();
		}
		glBindVertexArray(graph->m_Vao);
		glDrawElements(GL_TRIANGLES, 6, GL_UNSIGNED_INT, 0);
	}
}

bool operator==(const NEElement e, const std::shared_ptr<Graph> g) {
	return e.getID() == g->getElement().getID();
}
bool operator!=(const NEElement e, const std::shared_ptr<Graph> g) { return !(e == g); }
bool operator==(const std::shared_ptr<Graph> g, const NEElement e) { return   e == g; }
bool operator!=(const std::shared_ptr<Graph> g, const NEElement e) { return !(e == g); }