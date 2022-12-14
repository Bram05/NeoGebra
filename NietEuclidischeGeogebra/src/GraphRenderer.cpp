#include "GraphRenderer.h"

Graph::Graph(NEElement& el, float leftX, float rightX, float topY, float bottomY, float midCoordX, float midCoordY, float unitLengthPixels, const RGBColour& colour)
	: m_El{ el },
	m_LeftX{ leftX }, m_RightX{ rightX }, m_TopY{ topY }, m_BottomY{ bottomY },
	m_MidCoordX{ midCoordX }, m_MidCoordY{ midCoordY }, m_UnitLengthPixels{ unitLengthPixels },
	m_Colour{ colour }
{
	GraphShader::CreateCompShader("graphShader1", m_El.getShader(), m_CompShader1);

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
}

void Graph::GenTexture(float leftX, float rightX, float topY, float bottomY, float midCoordX, float midCoordY, float unitLengthPixels, GraphRenderer* rendPtr) {
	m_LeftX = leftX;
	m_RightX = rightX;
	m_TopY = topY;
	m_BottomY = bottomY;
	m_MidCoordX = midCoordX;
	m_MidCoordX = midCoordY;
	m_UnitLengthPixels = unitLengthPixels;

	float buffer[16] = {
		leftX,	topY,	 0.0f, 1.0f,
		leftX,	bottomY, 0.0f, 0.0f,
		rightX,	bottomY, 1.0f, 0.0f,
		rightX,	topY,	 1.0f, 1.0f
	};

	glBindBuffer(GL_ARRAY_BUFFER, m_Vb);
	glBufferData(GL_ARRAY_BUFFER, sizeof(buffer), buffer, GL_STATIC_DRAW);

	float normWidth = rightX - leftX;
	float normHeight = topY - bottomY;
	if (m_Texture != NULL) {
		glDeleteTextures(1, &m_Texture);
	}
	m_Texture = rendPtr->m_Shader.RunComp(normWidth, normHeight, m_MidCoordX, m_MidCoordY, m_UnitLengthPixels, m_CompShader1);
}

GraphRenderer::GraphRenderer()
	: m_Shader("graphShader")
{
	setLineThickness(3);
}

GraphRenderer::~GraphRenderer()
{
}

void GraphRenderer::AddToRenderQueue(const std::shared_ptr<Graph>& graph)
{
	m_RenderQueue.push(graph);
}

void GraphRenderer::setLineThickness(int pixels) {
	if (pixels > 8 or pixels < 1) { 
		throw std::invalid_argument("Invalid line thickness"); 
	} 
	m_LineThickness = pixels; 
	if (pixels % 2 == 0) { --m_LineThickness;  }

	int mid = m_LineThickness / 2;
	int maxD = std::pow(m_LineThickness/2, 2) + 1 - pixels % 2;
	for (int x = 0; x < 7; ++x) {
		for (int y = 0; y < 7; ++y) {
			int d = std::pow(x - mid, 2) + std::pow(y - mid, 2);
			if (d <= maxD) { m_Kernel[y][x] = 1; }
			else { m_Kernel[y][x] = 0; }
		}
	}
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
		m_Shader.SetUniform("u_Colour", { c.norm_r, c.norm_g, c.norm_b, c.norm_a });
		m_Shader.SetUniform("u_KernelSize", m_LineThickness);
		m_Shader.SetUniform2d("u_Kernel", m_Kernel);
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