#include "GraphUI.h"

#include "Renderer.h"
#include "Application.h"
#include "Util.h"

GraphUI::GraphUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "GraphUI")
{
	m_MidCoordX = 0.0f, m_MidCoordY = 0.0f, m_UnitLengthPixels = 135.0f;

	UpdateLines();
	UpdateGraphs();
}

GraphUI::~GraphUI()
{
}

void GraphUI::DeleteGraphs()
{
	m_Graphs.clear();
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
	UpdateGraphs();
	UIElement::ResizeWindow(width, height);
}

void GraphUI::UpdateGraphUI()
{
	UpdateGraphs();
}

void GraphUI::WasClicked(float x, float y) {
	m_XBeforeDrag = x;
	m_YBeforeDrag = y;
	m_MidCoordXBeforeDrag = m_MidCoordX;
	m_MidCoordYBeforeDrag = m_MidCoordY;
}

void GraphUI::DraggedUpdate(float x, float y) {
	m_MidCoordX = m_MidCoordXBeforeDrag - (Util::ConvertToPixelCoordinate(x, true) - Util::ConvertToPixelCoordinate(m_XBeforeDrag, true)) / m_UnitLengthPixels;
	m_MidCoordY = m_MidCoordYBeforeDrag - (Util::ConvertToPixelCoordinate(y, false) - Util::ConvertToPixelCoordinate(m_YBeforeDrag, false)) / m_UnitLengthPixels;
	UpdateLines();
	UpdateGraphs();
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

	float midPixelX = (pixelLeftX + pixelRightX) / 2;
	float midPixelY = (pixelTopY + pixelBottomY) / 2;

	//Pixel nearest to midpixel with  from floored whole coordinate in pixels (+1 for small correction, maybe better fix later)
	float nearMidPixelX = midPixelX - (m_MidCoordX - (int)(m_MidCoordX)) * m_UnitLengthPixels + 1;
	float nearMidPixelY = midPixelY - (m_MidCoordY - (int)(m_MidCoordY)) * m_UnitLengthPixels + 1;
	
	for (int i = 0; i < (nearMidPixelX - pixelLeftX) / m_UnitLengthPixels; ++i) {
		float x = Util::ConvertToOpenGLCoordinate(nearMidPixelX - i * m_UnitLengthPixels, true);
		m_Lines.push_back(std::make_shared<Line>(Point(x, m_TopY), Point(x, m_BottomY), std::array<float, 4>{0.0f, 0.0f, 0.0f, 1.0f}));
	}

	for (int i = 1; i < (pixelRightX - nearMidPixelX) / m_UnitLengthPixels; ++i) {
		float x = Util::ConvertToOpenGLCoordinate(nearMidPixelX + i * m_UnitLengthPixels, true);
		m_Lines.push_back(std::make_shared<Line>(Point(x, m_TopY), Point(x, m_BottomY), std::array<float, 4>{0.0f, 0.0f, 0.0f, 1.0f}));
	}

	for (int i = 0; i < (nearMidPixelY - pixelBottomY) / m_UnitLengthPixels; ++i) {
		float y = Util::ConvertToOpenGLCoordinate(nearMidPixelY - i * m_UnitLengthPixels, false);
		m_Lines.push_back(std::make_shared<Line>(Point(m_LeftX, y), Point(m_RightX, y), std::array<float, 4>{0.0f, 0.0f, 0.0f, 1.0f}));
	}

	for (int i = 1; i < (pixelTopY - nearMidPixelY) / m_UnitLengthPixels; ++i) {
		float y = Util::ConvertToOpenGLCoordinate(nearMidPixelY + i * m_UnitLengthPixels, false);
		m_Lines.push_back(std::make_shared<Line>(Point(m_LeftX, y), Point(m_RightX, y), std::array<float, 4>{0.0f, 0.0f, 0.0f, 1.0f}));
	}
}

void GraphUI::UpdateGraphs()
{
	GraphRenderer* rendPtr = Application::Get()->GetRenderer()->GetGraphRenderer();

	std::shared_ptr<Model> m = Application::Get()->GetModelManager()->GetModel();
	// Add new extra equations
	for (NEElement& el : m->getExtraEquations()) {
		bool found = false;
		for (std::shared_ptr<Graph> graph : m_Graphs) {
			if (el == graph) { found = true; break; }
		}
		if (!found) {
			m_Graphs.push_back(std::make_shared<Graph>(el, m_LeftX, m_RightX, m_TopY, m_BottomY, m_MidCoordX, m_MidCoordY, m_UnitLengthPixels, el.getColour()));
		}
	}
	// Add new graphs
	for (NEElement& el : m->getElements()) {
		bool found = false;
		for (std::shared_ptr<Graph> graph : m_Graphs) {
			if (el == graph) { found = true; break; }
		}
		if (!found) {
			m_Graphs.push_back(std::make_shared<Graph>(el, m_LeftX, m_RightX, m_TopY, m_BottomY, m_MidCoordX, m_MidCoordY, m_UnitLengthPixels, el.getColour()));
		}
	}

	// Remove old graphs that no longer exist
	// Go backwards through vector to avoid index shifting when removing element
	for (int i = m_Graphs.size() - 1; i >= 0; --i) {
		std::shared_ptr<Graph> graph = m_Graphs[i];
		bool found = false;
		for (NEElement& el : m->getElements()) {
			if (el == graph) {
				found = true;
				break;
			}
		}
		if (!found) {
			for (NEElement& el : m->getExtraEquations()) {
				if (el == graph) {
					found = true;
					break;
				}
			}
		}
		if (!found) {
			m_Graphs.erase(m_Graphs.begin() + i);
		}
		else {
			//Need to regenerate texture because graph moved
			graph->GenTexture(m_LeftX, m_RightX, m_TopY, m_BottomY, m_MidCoordX, m_MidCoordY, m_UnitLengthPixels, rendPtr);
		}
	}
}
