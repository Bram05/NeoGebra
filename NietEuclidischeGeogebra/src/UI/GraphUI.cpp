#include "GraphUI.h"

#include "Renderer.h"
#include "Application.h"
#include "Util.h"

constexpr int horizontalLineDiff{100};

GraphUI::GraphUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "GraphUI")
{
	UpdateLines();
	UpdateGraphs();
}

GraphUI::~GraphUI()
{
}

void GraphUI::RenderPass(Renderer* r)
{
	for (std::shared_ptr<Line>& line : m_Lines)
	{
		r->AddToRenderQueue(line);
	}
	for (std::shared_ptr<Graph>& graph : m_Graphs)
	{
		r->AddToRenderQueue(graph);
	}
	UIElement::RenderPass(r);
}

void GraphUI::ResizeWindow(int width, int height)
{
	UpdateLines();
	UIElement::ResizeWindow(width, height);
}

void GraphUI::UpdateLines()
{
	m_Lines.clear();
	m_Lines.push_back(std::make_shared<Line>(Point(m_LeftX, m_TopY), Point(m_LeftX, m_BottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(m_LeftX, m_TopY), Point(m_RightX, m_TopY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(m_RightX, m_BottomY), Point(m_RightX, m_TopY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(m_RightX, m_BottomY), Point(m_LeftX, m_BottomY))); // bottom

	float pixelTopY = Util::ConvertToPixelCoordinate(m_TopY, false);
	float pixelBottomY = Util::ConvertToPixelCoordinate(m_BottomY, false);
	float pixelLeftX = Util::ConvertToPixelCoordinate(m_LeftX, true);
	float pixelRightX = Util::ConvertToPixelCoordinate(m_RightX, true);

	int numHorizontalLines{ (int)((pixelTopY - pixelBottomY) / horizontalLineDiff) };
	for (int i = 0; i < numHorizontalLines; i++)
	{
		float y = m_TopY - i * ((m_TopY - m_BottomY) / numHorizontalLines);
		m_Lines.push_back(std::make_shared<Line>(Point(m_LeftX, y), Point(m_RightX, y), std::array<float, 4>{0.0f, 0.0f, 0.0f, 1.0f}));
	}

	int numVerticalLines{ (int)((pixelRightX - pixelLeftX) / horizontalLineDiff) };
	for (int i = 0; i < numVerticalLines; i++)
	{
		float x = m_RightX - i * ((m_RightX - m_LeftX) / numVerticalLines);
		m_Lines.push_back(std::make_shared<Line>(Point(x, m_TopY), Point(x, m_BottomY), std::array<float, 4>{0.0f, 0.0f, 0.0f, 1.0f}));
	}
}

void GraphUI::UpdateGraphs()
{
	m_Graphs.clear();
	m_Graphs.push_back(std::make_shared<Graph>(m_LeftX, m_RightX, m_TopY, m_BottomY, -10, 10, -10, -10, std::array{ 1.0f, 0.0f, 0.0f, 1.0f }));
}
