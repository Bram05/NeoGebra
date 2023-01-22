#include "GraphRenderer.h"

#include "GraphComputeShaderManager.h"
#include "Util.h"

Graph::Graph(NEElement& el, const GraphComputeShaderManager& manager, float leftX, float rightX, float topY, float bottomY, float midCoordX, float midCoordY, float unitLengthPixels, const RGBColour& colour)
	: m_El{ el },
	m_LeftX{ leftX }, m_RightX{ rightX }, m_TopY{ topY }, m_BottomY{ bottomY },
	m_MidCoordX{ midCoordX }, m_MidCoordY{ midCoordY }, m_UnitLengthPixels{ unitLengthPixels },
	m_Colour{ colour }
{
	int widthPix{ Util::ConvertToPixelCoordinate(rightX - leftX, true) };
	int heightPix{ Util::ConvertToPixelCoordinate(topY - bottomY, false) };
	glGenTextures(1, &m_Texture);
	glActiveTexture(GL_TEXTURE0);
	glBindTexture(GL_TEXTURE_2D, m_Texture);

	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);

	glTexImage2D(GL_TEXTURE_2D, 0, GL_R32F, widthPix, heightPix, 0, GL_RED, GL_FLOAT, NULL);
	glBindImageTexture(0, m_Texture, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);

	m_CompShader1 = manager.CreateCompShader("graphShader1", m_El.getShader());

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

void Graph::ReGenTexture(const GraphComputeShaderManager& manager) {
	manager.RunComputeShader(this);
}

GraphRenderer::GraphRenderer()
	: m_Shader("graphShader")
{
	setLineThickness(3);
	setPointSize(20);
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
		throw std::invalid_argument("Invalid line thickness: " + std::to_string(pixels));
	}
	m_LineThickness = pixels;
}

void GraphRenderer::setPointSize(int pixels) {
	if (pixels < 1) {
		throw std::invalid_argument("Invalid point size: " + std::to_string(pixels));
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
			m_Shader.SetUniform("u_Size", m_LineThickness);
			break;
		default:
			throw std::runtime_error("Unkown type!");
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