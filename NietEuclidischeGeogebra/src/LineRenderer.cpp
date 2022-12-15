// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "LineRenderer.h"

#include "Application.h"

LineRenderer::LineRenderer()
	: m_Shader("lineShader")
{
}

LineRenderer::~LineRenderer()
{
}

void LineRenderer::AddToRenderQueue(const std::shared_ptr<Line>& line)
{
	m_RenderQueue.push(line);
}

void LineRenderer::RenderQueue()
{
	m_Shader.Bind();
	//glLineWidth(10.0f);
	while (m_RenderQueue.size() != 0)
	{
		std::shared_ptr<Line> l = m_RenderQueue.front();
		m_RenderQueue.pop();

		m_Shader.SetUniform("u_Colour", l->m_Colour);
		glBindVertexArray(l->m_Vao);
		glDrawElements(GL_TRIANGLES, 6, GL_UNSIGNED_INT, NULL);
	}
}

Line::Line(Point begin, Point end, const std::array<float, 4>& colour /*= { 1.0f, 0.0f, 0.0f, 1.0f }*/, float thickness /*= 1.0f*/)
	: m_Begin{ begin }, m_End{ end }, m_Colour{ colour }, m_Thickness{ thickness }
{
	auto[width, height] = Application::Get()->GetWindow()->GetSize();
	Point diffVec = end - begin;
	Point perpendicularVector{ diffVec.y, diffVec.x };
	float length{ std::sqrt(diffVec.x * diffVec.x + diffVec.y * diffVec.y) };
	Point normalizedPerpendicular{ perpendicularVector / length };

	normalizedPerpendicular.y = -normalizedPerpendicular.y;

	Point beginTop = begin + normalizedPerpendicular * (thickness / width); // I think some of these might need to be changed to height
	Point beginBottom = begin - normalizedPerpendicular * (thickness / width);
	Point endTop = end + normalizedPerpendicular * (thickness / width);
	Point endBottom = end - normalizedPerpendicular * (thickness / width);

	float buffer[8] = {
		beginTop.x, beginTop.y,
		beginBottom.x, beginBottom.y,
		endBottom.x, endBottom.y,
		endTop.x, endTop.y,
	};
	unsigned int indices[6] = { 0,1,2,2,3,0 };

	glGenVertexArrays(1, &m_Vao);
	glBindVertexArray(m_Vao);

	glGenBuffers(1, &m_Vb);
	glBindBuffer(GL_ARRAY_BUFFER, m_Vb);
	glBufferData(GL_ARRAY_BUFFER, sizeof(buffer), buffer, GL_STATIC_DRAW);

	glEnableVertexAttribArray(0);
	glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE, 0, 0);

	glGenBuffers(1, &m_Ib);
	glBindBuffer(GL_ELEMENT_ARRAY_BUFFER, m_Ib);
	glBufferData(GL_ELEMENT_ARRAY_BUFFER, sizeof(indices), indices, GL_STATIC_DRAW);
}

Line::~Line()
{
	glDeleteBuffers(1, &m_Vb);
	glDeleteBuffers(1, &m_Ib);
	glDeleteVertexArrays(1, &m_Vao);
}

void Line::SetLocation(Point newBegin, Point newEnd)
{
	Point diffVec = newEnd - newBegin;
	Point perpendicularVector{ diffVec.y, diffVec.x };
	float length{ std::sqrt(diffVec.x * diffVec.x + diffVec.y * diffVec.y) };
	Point normalizedPerpendicular{ diffVec / length };

	Point beginTop = newBegin + normalizedPerpendicular * m_Thickness;
	Point beginBottom = newBegin - normalizedPerpendicular * m_Thickness;
	Point endTop = newEnd + normalizedPerpendicular * m_Thickness;
	Point endBottom = newEnd - normalizedPerpendicular * m_Thickness;

	float buffer[8] = {
		beginTop.x, beginTop.y,
		beginBottom.x, beginBottom.y,
		endBottom.x, endBottom.y,
		endTop.x, endTop.y,
	};
	glBindBuffer(GL_ARRAY_BUFFER, m_Vb);
	glBufferSubData(GL_ARRAY_BUFFER, 0, sizeof(buffer), buffer);

	m_Begin = newBegin;
	m_End = newEnd;
}