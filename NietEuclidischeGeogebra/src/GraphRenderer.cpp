#include "GraphRenderer.h"

Graph::Graph(line l, float leftX, float rightX, float topY, float bottomY, int graphWindowLeftX, int graphWindowRightX, int graphWindowTopY, int graphWindowBottomY, const std::array<float, 4>& colour)
	: m_Eq{ l },
	m_LeftX{ leftX }, m_RightX{ rightX }, m_TopY{ topY }, m_BottomY{ bottomY }, 
	m_GraphWindowLeftX{ graphWindowLeftX }, m_GraphWindowRightX{ graphWindowRightX }, m_GraphWindowTopY{ graphWindowTopY }, m_GraphWindowBottomY{ graphWindowBottomY }, 
	m_Colour{ colour }
{	
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
}

/*void Graph::SetPosition(float leftX, float rightX, float topY, float bottomY)
{
	float buffer[8] = {
		leftX, topY,
		leftX, bottomY,
		rightX, bottomY,
		rightX, topY
	};
	glBindBuffer(GL_ARRAY_BUFFER, m_Vao);
	glBufferData(GL_ARRAY_BUFFER, sizeof(buffer), buffer, GL_STATIC_DRAW);
}*/

GraphRenderer::GraphRenderer()
	: m_Shader("graphShader")
{
}

GraphRenderer::~GraphRenderer()
{
}

void GraphRenderer::AddToRenderQueue(const std::shared_ptr<Graph>& graph)
{
	m_RenderQueue.push(graph);
}

void GraphRenderer::RenderQueue()
{
	m_Shader.Bind();
	glEnable(GL_BLEND);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	while (!m_RenderQueue.empty())
	{
		std::shared_ptr<Graph> graph{m_RenderQueue.front()};
		m_RenderQueue.pop();

		m_Shader.SetTexture(graph->m_Texture);
		m_Shader.SetUniform("u_Colour", graph->m_Colour);
		glBindVertexArray(graph->m_Vao);
		glDrawElements(GL_TRIANGLES, 6, GL_UNSIGNED_INT, 0);
	}
	glDisable(GL_BLEND);
}

void GraphRenderer::GenTexture(const std::shared_ptr<Graph>& graph) {
	float normWidth = graph->GetRightX() - graph->GetLeftX();
	float normHeight = graph->GetTopY() - graph->GetBottomY();
	graph->SetTexture(m_Shader.RunComp(graph->m_Eq, normWidth, normHeight, graph->m_GraphWindowLeftX, graph->m_GraphWindowRightX, graph->m_GraphWindowTopY, graph->m_GraphWindowBottomY));
}